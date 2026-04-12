from __future__ import annotations
import html
import io
import re
import shutil
import time
import unicodedata
from collections import defaultdict
from contextlib import redirect_stdout
from datetime import datetime
from dataclasses import dataclass
from pathlib import Path
from statistics import median
from typing import Iterable

import fitz


ROOT = Path(__file__).resolve().parent
OUTPUT_DIR = ROOT / "html_output"
ASSET_DIR = OUTPUT_DIR / "assets"

PAGE_FACSIMILE_TEXT_THRESHOLD = 80
INLINE_FIGURE_AREA_RATIO = 0.02
EDGE_BAND_RATIO = 0.08
MARGIN_BAND_RATIO = 0.12
MARGIN_NUMBER_WIDTH = 48.0

NBSP_CHARS = {
    "\u00a0": " ",
    "\u2002": " ",
    "\u2003": " ",
    "\u2009": " ",
    "\u202f": " ",
}

NOISE_PATTERNS = [
    re.compile(r"^page\s+\d+(\s+of\s+\d+)?$", re.I),
    re.compile(r"^p\s+a\s+g\s+e\s+\d+(\s+of\s+\d+)?$", re.I),
    re.compile(r"^\d+$"),
    re.compile(r"^signature not verified$", re.I),
    re.compile(r"^digitally signed by$", re.I),
    re.compile(r"^reason:?$", re.I),
    re.compile(r"^date:?$", re.I),
]

ORDERED_MARKER_RE = re.compile(r"^\(?((?:\d{1,4})|(?:[IVXLCDM]{1,8})|(?:[A-Za-z]))([\.\)])(?:\s+|$)(.*)$")
BULLET_MARKER_RE = re.compile(r"^[\u2022\uf0b7\-]\s+(.*)$")
CONNECTOR_RE = re.compile(
    r"^(and|or|but|for|nor|yet|so|because|however|therefore|thus|further|furthermore|"
    r"moreover|provided|whereas|which|who|whom|whose|that|this|these|those|the|a|an|"
    r"in|on|at|by|of|to|from|with|within|under|over|after|before|against|between|"
    r"if|when|while|unless|since|as|also|including|such|is|are|was|were|be|being|been)\b",
    re.I,
)
HEADING_KEYWORDS = {
    "JUDGMENT",
    "ORDER",
    "HEADNOTE",
    "REPORTABLE",
    "NON-REPORTABLE",
    "VERSUS",
    "WITH",
    "APPELLATE JURISDICTION",
    "ORIGINAL JURISDICTION",
    "CIVIL APPELLATE JURISDICTION",
    "CRIMINAL APPELLATE JURISDICTION",
    "CIVIL ORIGINAL JURISDICTION",
    "CRIMINAL ORIGINAL JURISDICTION",
}

SUPER_SUB_SIZE_RATIO = 0.92
SUPER_RISE_RATIO = 0.18
SUB_DROP_RATIO = 0.10
SPAN_SPACE_GAP_RATIO = 0.22

MOJIBAKE_REPLACEMENTS = {
    "â€œ": '"',
    "â€": '"',
    "â€˜": "'",
    "â€™": "'",
    "â€“": "-",
    "â€”": "--",
    "â€¦": "...",
}


@dataclass
class TextLine:
    text: str
    html_text: str
    bbox: tuple[float, float, float, float]
    font_size: float
    bold: bool

    @property
    def x0(self) -> float:
        return self.bbox[0]

    @property
    def y0(self) -> float:
        return self.bbox[1]

    @property
    def x1(self) -> float:
        return self.bbox[2]

    @property
    def y1(self) -> float:
        return self.bbox[3]


@dataclass
class PageObject:
    kind: str
    top: float
    value: object


@dataclass
class DocItem:
    kind: str
    page_num: int
    text: str | None = None
    inline_html: str | None = None
    level: int | None = None
    list_style: str | None = None
    ordinal: int | None = None
    html_fragment: str | None = None


def slugify(name: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9]+", "-", name).strip("-").lower()
    return safe or "document"


def prettify_stem(stem: str) -> str:
    pretty = stem.replace("_", " ").replace(".", " ").strip()
    pretty = re.sub(r"\s+", " ", pretty)
    return pretty


def log(message: str) -> None:
    timestamp = datetime.now().strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}", flush=True)


def progress_step(page_count: int) -> int:
    return max(10, page_count // 10) if page_count > 20 else 5


def format_percent(current: int, total: int) -> int:
    return int((current / total) * 100) if total else 100


def normalize_text(text: str) -> str:
    if not text:
        return ""

    if any(marker in text for marker in ("â", "Ã", "€", "™")):
        try:
            repaired = text.encode("latin1").decode("utf-8")
            text = repaired
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass

    text = unicodedata.normalize("NFKC", text)
    for original, replacement in NBSP_CHARS.items():
        text = text.replace(original, replacement)
    for original, replacement in MOJIBAKE_REPLACEMENTS.items():
        text = text.replace(original, replacement)
    text = text.replace("\u00ad", "")
    text = text.replace("\uf0b7", "•")
    text = text.replace("\r", " ").replace("\n", " ")
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r"\bP\s+a\s+g\s+e\s+\d+(\s+of\s+\d+)?\b", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    text = collapse_spaced_caps(text)
    return text


def edge_text_key(text: str) -> str:
    return normalize_text(text).lower()


def repeated_edge_threshold(page_count: int) -> int:
    if page_count <= 10:
        return 2
    if page_count <= 50:
        return 3
    return 5


def margin_side(bbox: tuple[float, float, float, float], page_width: float) -> str | None:
    if bbox[0] <= page_width * MARGIN_BAND_RATIO:
        return "left"
    if bbox[2] >= page_width * (1 - MARGIN_BAND_RATIO):
        return "right"
    return None


def is_margin_number_candidate(text: str, bbox: tuple[float, float, float, float], page_width: float) -> bool:
    if not re.fullmatch(r"\d{2,4}", text):
        return False
    if not margin_side(bbox, page_width):
        return False
    return (bbox[2] - bbox[0]) <= MARGIN_NUMBER_WIDTH


def collapse_spaced_caps(text: str) -> str:
    tokens = text.split()
    if len(tokens) >= 4 and all(len(token) == 1 and token.isalpha() and token.isupper() for token in tokens):
        return "".join(tokens)
    return text


def is_noise_line(text: str, bbox: tuple[float, float, float, float], page_num: int, page_count: int, page_height: float) -> bool:
    cleaned = normalize_text(text)
    if not cleaned:
        return True

    lowered = cleaned.lower()
    if lowered.startswith("http://judis.nic.in"):
        return True
    if "signature not verified" in lowered or "digitally signed by" in lowered:
        return True
    if re.search(r"\bpage\s+\d+\s+of\s+\d+\b", cleaned, re.I):
        return True

    for pattern in NOISE_PATTERNS:
        if pattern.fullmatch(cleaned):
            if cleaned.isdigit() and int(cleaned) != page_num:
                return False
            return True

    y0, y1 = bbox[1], bbox[3]
    near_edge = y0 < page_height * 0.12 or y1 > page_height * 0.88
    if page_num > 1 and cleaned.upper() in {"JUDGMENT", "ORDER"}:
        return True
    if near_edge and cleaned.isdigit() and int(cleaned) == page_num:
        return True
    if near_edge and re.fullmatch(r"page\s+\d+", cleaned, re.I):
        return True
    if near_edge and page_count > 1 and cleaned.endswith(f"Page {page_num}"):
        return True
    return False


def bbox_within(inner: tuple[float, float, float, float], outer: tuple[float, float, float, float], tolerance: float = 2.0) -> bool:
    return (
        inner[0] >= outer[0] - tolerance
        and inner[1] >= outer[1] - tolerance
        and inner[2] <= outer[2] + tolerance
        and inner[3] <= outer[3] + tolerance
    )


def parse_ordered_marker(text: str) -> tuple[str, int, str] | None:
    match = ORDERED_MARKER_RE.match(text)
    if not match:
        return None

    token = match.group(1)
    remainder = match.group(3).strip()
    if token.isdigit():
        return "decimal", int(token), remainder
    if not text.startswith("("):
        return None
    if len(token) == 1 and token.isalpha():
        if not token.islower():
            return None
        style = "upper-alpha" if token.isupper() else "lower-alpha"
        return style, alpha_to_int(token), remainder
    roman = roman_to_int(token)
    if roman:
        if token != token.lower():
            return None
        style = "upper-roman" if token.isupper() else "lower-roman"
        return style, roman, remainder
    return None


def alpha_to_int(token: str) -> int:
    return ord(token.lower()) - 96


def roman_to_int(token: str) -> int | None:
    token = token.upper()
    values = {"I": 1, "V": 5, "X": 10, "L": 50, "C": 100, "D": 500, "M": 1000}
    total = 0
    prev = 0
    for char in reversed(token):
        value = values.get(char)
        if value is None:
            return None
        if value < prev:
            total -= value
        else:
            total += value
            prev = value
    return total


def starts_like_continuation(text: str) -> bool:
    if not text:
        return False
    if text[0].islower():
        return True
    if text[0] in ",.;:)]}" or text.startswith("'"):
        return True
    return bool(CONNECTOR_RE.match(text))


def ends_sentence(text: str) -> bool:
    return bool(re.search(r"[.!?\"”']\s*$", text))


def join_text(left: str, right: str) -> str:
    left = left.rstrip()
    right = right.lstrip()
    if not left:
        return right
    if not right:
        return left
    if left.endswith("-") and right[:1].islower():
        return left[:-1] + right
    if left.endswith("/") or right.startswith("/"):
        return left + right
    if left.endswith(("(", "[", "{", "/")):
        return left + right
    if right.startswith((",", ".", ";", ":", ")", "]", "}")):
        return left + right
    return left + " " + right


def join_inline_html(left_html: str, right_html: str, left_text: str, right_text: str, *, force_space: bool = False) -> str:
    left_html = left_html.rstrip()
    right_html = right_html.lstrip()
    left_text = left_text.rstrip()
    right_text = right_text.lstrip()
    if not left_html:
        return right_html
    if not right_html:
        return left_html
    if left_text.endswith("-") and right_text[:1].islower():
        return (left_html[:-1] if left_html.endswith("-") else left_html) + right_html
    if left_text.endswith("/") or right_text.startswith("/"):
        return left_html + right_html
    if left_text.endswith(("(", "[", "{", "/")):
        return left_html + right_html
    if right_text.startswith((",", ".", ";", ":", ")", "]", "}", "?", "!", "%")):
        return left_html + right_html
    if force_space:
        return left_html + " " + right_html
    return left_html + " " + right_html


def item_inline_html(item: DocItem) -> str:
    if item.inline_html is not None:
        return item.inline_html
    return html.escape(item.text or "")


def merge_item_text(current: DocItem, text: str, inline_html: str) -> None:
    current.inline_html = join_inline_html(item_inline_html(current), inline_html, current.text or "", text)
    current.text = join_text(current.text or "", text)


def merge_doc_items(left: DocItem, right: DocItem) -> None:
    left.inline_html = join_inline_html(item_inline_html(left), item_inline_html(right), left.text or "", right.text or "")
    left.text = join_text(left.text or "", right.text or "")


def normalize_span_text(text: str) -> str:
    text = normalize_text(text)
    return text.strip()


def classify_script_position(
    span: dict,
    dominant_font: float,
    dominant_top: float,
    dominant_bottom: float,
) -> str | None:
    span_text = normalize_span_text(span.get("text", ""))
    if not span_text:
        return None
    size = float(span.get("size", 0.0) or 0.0)
    if size <= 0:
        return None
    if size >= dominant_font * SUPER_SUB_SIZE_RATIO:
        return None
    bbox = span.get("bbox", (0.0, 0.0, 0.0, 0.0))
    top = float(bbox[1])
    bottom = float(bbox[3])
    rise_threshold = max(0.8, dominant_font * SUPER_RISE_RATIO)
    drop_threshold = max(0.8, dominant_font * SUB_DROP_RATIO)
    if bottom <= dominant_bottom - rise_threshold:
        return "sup"
    if top >= dominant_top + drop_threshold or bottom >= dominant_bottom + drop_threshold:
        return "sub"
    return None


def build_line_text_and_html(line: dict) -> tuple[str, str, float, bool]:
    spans = [span for span in line["spans"] if normalize_span_text(span.get("text", ""))]
    if not spans:
        return "", "", 0.0, False

    dominant_font = max(float(span.get("size", 0.0) or 0.0) for span in spans)
    dominant_spans = [span for span in spans if float(span.get("size", 0.0) or 0.0) >= dominant_font * 0.95]
    baseline_group = dominant_spans or spans
    dominant_top = median(float(span["bbox"][1]) for span in baseline_group)
    dominant_bottom = median(float(span["bbox"][3]) for span in baseline_group)
    bold = any("bold" in str(span.get("font", "")).lower() or "black" in str(span.get("font", "")).lower() for span in spans)

    plain_text = ""
    html_text = ""
    previous_x1: float | None = None
    previous_size: float | None = None

    for span in spans:
        span_text = normalize_span_text(span.get("text", ""))
        if not span_text:
            continue
        bbox = span.get("bbox", (0.0, 0.0, 0.0, 0.0))
        size = float(span.get("size", 0.0) or 0.0)
        script_kind = classify_script_position(span, dominant_font, dominant_top, dominant_bottom)
        escaped_text = html.escape(span_text)
        fragment_html = escaped_text if script_kind is None else f"<{script_kind}>{escaped_text}</{script_kind}>"
        fragment_plain = span_text
        force_space = False

        if script_kind is not None and plain_text:
            fragment_plain = " " + fragment_plain
        elif previous_x1 is not None and previous_size is not None:
            gap = float(bbox[0]) - previous_x1
            gap_threshold = max(1.0, previous_size * SPAN_SPACE_GAP_RATIO)
            force_space = gap > gap_threshold

        if not plain_text:
            plain_text = fragment_plain.lstrip()
            html_text = fragment_html.lstrip()
        elif script_kind is not None:
            html_text = html_text + fragment_html
            plain_text = join_text(plain_text, fragment_plain)
        else:
            html_text = join_inline_html(html_text, fragment_html, plain_text, fragment_plain, force_space=force_space)
            plain_text = join_text(plain_text, fragment_plain)

        previous_x1 = float(bbox[2])
        previous_size = size

    return normalize_text(plain_text), html_text.strip(), dominant_font, bold


def should_join_across_boundary(previous: DocItem, current: DocItem) -> bool:
    if previous.kind not in {"p", "ol_item", "ul_item"}:
        return False
    if current.kind not in {"p", "ol_item", "ul_item"}:
        return False
    if not previous.text or not current.text:
        return False
    if current.kind == "ol_item" and current.ordinal is not None:
        return False
    if previous.text.endswith("-"):
        return True
    if starts_like_continuation(current.text):
        return True
    if previous.text.endswith((",", ";", ":")):
        return True
    return not ends_sentence(previous.text) and len(previous.text) >= 80


def should_continue_item(current: DocItem, line: TextLine, previous_line: TextLine | None) -> bool:
    if current.text is None:
        return False
    if previous_line is None:
        return True
    gap = max(0.0, line.y0 - previous_line.y1)
    same_indent = abs(line.x0 - previous_line.x0) <= 18
    hanging_indent = line.x0 - previous_line.x0 > 10
    continuation = starts_like_continuation(line.text)

    if gap <= max(previous_line.font_size * 0.9, 7):
        return True
    if current.text.endswith("-"):
        return True
    if continuation:
        return True
    if not ends_sentence(current.text) and same_indent:
        return True
    if current.kind in {"ol_item", "ul_item"} and gap <= max(previous_line.font_size * 1.4, 12) and not hanging_indent:
        return True
    return False


def is_heading_line(line: TextLine, median_font: float, page_width: float) -> bool:
    text = line.text
    if not text or len(text) > 160:
        return False
    if ORDERED_MARKER_RE.match(text) or BULLET_MARKER_RE.match(text):
        return False

    normalized = re.sub(r"[^A-Za-z ]+", "", text).strip().upper()
    if normalized in HEADING_KEYWORDS:
        return True

    letters = [char for char in text if char.isalpha()]
    if not letters:
        return False

    caps_ratio = sum(char.isupper() for char in letters) / len(letters)
    centered = abs(((line.x0 + line.x1) / 2) - (page_width / 2)) <= page_width * 0.16
    larger = line.font_size >= median_font * 1.15
    short = len(text.split()) <= 14

    if short and centered and len(text.split()) >= 2 and caps_ratio >= 0.8 and (larger or line.bold):
        return True
    return False


def heading_level(line: TextLine, median_font: float) -> int:
    if line.font_size >= median_font * 1.35:
        return 2
    return 3


def table_metrics(rows: list[list[str | None]]) -> dict[str, float] | None:
    cleaned_rows = [[normalize_text(cell or "") for cell in row] for row in rows if row]
    if not cleaned_rows:
        return None
    column_count = max(len(row) for row in cleaned_rows)
    non_empty_cells = sum(1 for row in cleaned_rows for cell in row if cell)
    if column_count < 2 or len(cleaned_rows) < 2 or non_empty_cells < 4:
        return None

    texts = [cell for row in cleaned_rows for cell in row if cell]
    avg_nonempty_per_row = non_empty_cells / len(cleaned_rows)
    occupancy = non_empty_cells / (len(cleaned_rows) * column_count)
    avg_text_len = sum(len(cell) for cell in texts) / len(texts)
    short_ratio = sum(1 for cell in texts if len(cell) <= 3) / len(texts)
    return {
        "column_count": float(column_count),
        "row_count": float(len(cleaned_rows)),
        "avg_nonempty_per_row": avg_nonempty_per_row,
        "occupancy": occupancy,
        "avg_text_len": avg_text_len,
        "short_ratio": short_ratio,
    }


def table_should_render_as_html(metrics: dict[str, float]) -> bool:
    return (
        2 <= metrics["column_count"] <= 10
        and metrics["avg_nonempty_per_row"] >= 2
        and metrics["occupancy"] >= 0.45
        and metrics["avg_text_len"] >= 7
        and metrics["short_ratio"] <= 0.35
    )


def table_should_force_facsimile(metrics: dict[str, float]) -> bool:
    return (
        metrics["column_count"] >= 3
        and metrics["occupancy"] >= 0.35
        and metrics["avg_text_len"] >= 7
    )


def table_to_html(rows: list[list[str | None]]) -> str:
    cleaned_rows = [[normalize_text(cell or "") for cell in row] for row in rows if row]
    if not cleaned_rows:
        return ""

    column_count = max(len(row) for row in cleaned_rows)
    normalized_rows: list[list[str]] = []
    for row in cleaned_rows:
        padded = row + [""] * (column_count - len(row))
        normalized_rows.append(padded)

    first_row = normalized_rows[0]
    use_header = all(cell for cell in first_row)

    parts = ['<table class="court-table">']
    if use_header:
        parts.append("<thead><tr>")
        for cell in first_row:
            parts.append(f"<th>{html.escape(cell)}</th>")
        parts.append("</tr></thead>")
        body_rows = normalized_rows[1:]
    else:
        body_rows = normalized_rows

    parts.append("<tbody>")
    for row in body_rows:
        parts.append("<tr>")
        for cell in row:
            parts.append(f"<td>{html.escape(cell)}</td>")
        parts.append("</tr>")
    parts.append("</tbody></table>")
    return "".join(parts)


def extract_tables(plumber_page: pdfplumber.page.Page) -> tuple[list[tuple[tuple[float, float, float, float], str]], bool]:
    tables: list[tuple[tuple[float, float, float, float], str]] = []
    requires_facsimile = False
    for table in plumber_page.find_tables():
        rows = table.extract()
        metrics = table_metrics(rows)
        if not metrics:
            continue
        if table_should_render_as_html(metrics):
            html_fragment = table_to_html(rows)
            if html_fragment:
                tables.append((table.bbox, html_fragment))
            continue
        if table_should_force_facsimile(metrics):
            requires_facsimile = True
    return tables, requires_facsimile


def extract_repeated_edge_keys(doc: fitz.Document) -> tuple[set[str], set[str]]:
    top_hits: dict[str, set[int]] = defaultdict(set)
    bottom_hits: dict[str, set[int]] = defaultdict(set)
    threshold = repeated_edge_threshold(doc.page_count)

    for page_index, page in enumerate(doc, start=1):
        raw = page.get_text("dict", sort=True)
        height = page.rect.height
        top_seen: set[str] = set()
        bottom_seen: set[str] = set()

        for block in raw["blocks"]:
            if block["type"] != 0:
                continue
            for line in block["lines"]:
                text = normalize_text("".join(span["text"] for span in line["spans"]))
                if not text:
                    continue
                key = edge_text_key(text)
                if not key:
                    continue
                y0, y1 = line["bbox"][1], line["bbox"][3]
                if y1 <= height * EDGE_BAND_RATIO:
                    top_seen.add(key)
                elif y0 >= height * (1 - EDGE_BAND_RATIO):
                    bottom_seen.add(key)

        for key in top_seen:
            top_hits[key].add(page_index)
        for key in bottom_seen:
            bottom_hits[key].add(page_index)

    top_keys = {key for key, pages in top_hits.items() if len(pages) >= threshold}
    bottom_keys = {key for key, pages in bottom_hits.items() if len(pages) >= threshold}
    return top_keys, bottom_keys


def extract_sequential_margin_numbers(doc: fitz.Document) -> dict[int, set[str]]:
    candidates_by_side: dict[str, list[tuple[int, int, str, float]]] = defaultdict(list)
    skipped: dict[int, set[str]] = defaultdict(set)

    for page_index, page in enumerate(doc, start=1):
        raw = page.get_text("dict", sort=True)
        page_width = page.rect.width

        for block in raw["blocks"]:
            if block["type"] != 0:
                continue
            for line in block["lines"]:
                text = normalize_text("".join(span["text"] for span in line["spans"]))
                bbox = tuple(line["bbox"])
                side = margin_side(bbox, page_width)
                if not side or not is_margin_number_candidate(text, bbox, page_width):
                    continue
                candidates_by_side[side].append((page_index, int(text), text, bbox[1]))

    for candidates in candidates_by_side.values():
        if not candidates:
            continue
        candidates.sort(key=lambda item: (item[0], item[3], item[1]))
        run: list[tuple[int, int, str, float]] = [candidates[0]]

        def flush_run() -> None:
            if len(run) < 3:
                return
            for page_index, _, text, _ in run:
                skipped[page_index].add(text)

        for candidate in candidates[1:]:
            prev = run[-1]
            page_gap = candidate[0] - prev[0]
            if candidate[1] == prev[1] + 1 and 0 <= page_gap <= 1:
                run.append(candidate)
                continue
            flush_run()
            run = [candidate]
        flush_run()

    return skipped


def extract_text_lines(
    page: fitz.Page,
    table_bboxes: Iterable[tuple[float, float, float, float]],
    repeated_top_keys: set[str],
    repeated_bottom_keys: set[str],
    sequential_margin_numbers: dict[int, set[str]],
) -> list[TextLine]:
    lines: list[TextLine] = []
    raw = page.get_text("dict", sort=True)
    page_height = page.rect.height
    page_width = page.rect.width
    page_count = page.parent.page_count
    page_num = page.number + 1
    for block in raw["blocks"]:
        if block["type"] != 0:
            continue
        for line in block["lines"]:
            bbox = tuple(line["bbox"])
            if any(bbox_within(bbox, table_bbox) for table_bbox in table_bboxes):
                continue
            text, html_text, font_size, bold = build_line_text_and_html(line)
            if not text:
                continue
            if is_noise_line(text, bbox, page_num, page_count, page_height):
                continue
            if (
                text in sequential_margin_numbers.get(page_num, set())
                and is_margin_number_candidate(text, bbox, page_width)
            ):
                continue
            key = edge_text_key(text)
            if bbox[3] <= page_height * EDGE_BAND_RATIO and key in repeated_top_keys:
                continue
            if bbox[1] >= page_height * (1 - EDGE_BAND_RATIO) and key in repeated_bottom_keys:
                continue
            lines.append(TextLine(text=text, html_text=html_text, bbox=bbox, font_size=font_size, bold=bold))
    return lines


def page_has_complex_table(page: fitz.Page) -> bool:
    try:
        with redirect_stdout(io.StringIO()):
            table_finder = page.find_tables()
    except Exception:
        return False

    page_area = page.rect.width * page.rect.height
    for table in table_finder.tables:
        metrics = table_metrics(table.extract())
        if not metrics:
            continue
        if metrics["row_count"] < 4 or metrics["column_count"] < 6:
            continue
        if metrics["avg_text_len"] < 7:
            continue
        bbox = table.bbox
        coverage = ((bbox[2] - bbox[0]) * (bbox[3] - bbox[1])) / page_area
        if coverage >= 0.45 and metrics["occupancy"] >= 0.85:
            return True
    return False


def merge_spelled_heading_fragments(lines: list[TextLine], page_width: float) -> list[TextLine]:
    merged: list[TextLine] = []
    index = 0
    while index < len(lines):
        current = lines[index]
        compact = re.sub(r"\s+", "", current.text)
        center_delta = abs(((current.x0 + current.x1) / 2) - (page_width / 2))
        if 1 <= len(compact) <= 3 and compact.isalpha() and compact.isupper() and center_delta <= page_width * 0.18:
            letters = [compact]
            x0, y0, x1, y1 = current.bbox
            font_size = current.font_size
            bold = current.bold
            next_index = index + 1
            last_y = current.y1
            while next_index < len(lines):
                candidate = lines[next_index]
                candidate_compact = re.sub(r"\s+", "", candidate.text)
                candidate_center_delta = abs(((candidate.x0 + candidate.x1) / 2) - (page_width / 2))
                gap = max(0.0, candidate.y0 - last_y)
                if (
                    1 <= len(candidate_compact) <= 3
                    and candidate_compact.isalpha()
                    and candidate_compact.isupper()
                    and candidate_center_delta <= page_width * 0.18
                    and gap <= max(candidate.font_size * 1.2, 16)
                ):
                    letters.append(candidate_compact)
                    x0 = min(x0, candidate.x0)
                    y0 = min(y0, candidate.y0)
                    x1 = max(x1, candidate.x1)
                    y1 = max(y1, candidate.y1)
                    font_size = max(font_size, candidate.font_size)
                    bold = bold or candidate.bold
                    last_y = candidate.y1
                    next_index += 1
                    continue
                break
            if sum(len(fragment) for fragment in letters) >= 4:
                merged.append(TextLine(text="".join(letters), html_text=html.escape("".join(letters)), bbox=(x0, y0, x1, y1), font_size=font_size, bold=bold))
                index = next_index
                continue
        merged.append(current)
        index += 1
    return merged


def save_image_bytes(image_bytes: bytes, extension: str, asset_root: Path, filename: str) -> str:
    asset_root.mkdir(parents=True, exist_ok=True)
    target = asset_root / f"{filename}.{extension}"
    target.write_bytes(image_bytes)
    return target.relative_to(OUTPUT_DIR).as_posix()


def render_page_facs(page: fitz.Page, asset_root: Path, slug: str) -> str:
    pixmap = page.get_pixmap(matrix=fitz.Matrix(1.8, 1.8), alpha=False)
    asset_root.mkdir(parents=True, exist_ok=True)
    target = asset_root / f"{slug}-page-{page.number + 1:04d}.png"
    pixmap.save(target)
    rel = target.relative_to(OUTPUT_DIR).as_posix()
    return (
        f'<figure class="page-facsimile" data-page="{page.number + 1}">'
        f'<img src="{html.escape(rel)}" alt="Facsimile of page {page.number + 1}" />'
        "</figure>"
    )


def extract_figures(page: fitz.Page, table_bboxes: Iterable[tuple[float, float, float, float]], asset_root: Path, slug: str) -> list[PageObject]:
    objects: list[PageObject] = []
    page_area = page.rect.width * page.rect.height
    raw = page.get_text("dict", sort=True)
    for block in raw["blocks"]:
        if block["type"] != 1:
            continue
        bbox = tuple(block["bbox"])
        if any(bbox_within(bbox, table_bbox, tolerance=5.0) for table_bbox in table_bboxes):
            continue
        area = (bbox[2] - bbox[0]) * (bbox[3] - bbox[1])
        if area / page_area < INLINE_FIGURE_AREA_RATIO:
            continue
        rel = save_image_bytes(
            block["image"],
            block["ext"],
            asset_root,
            f"{slug}-page-{page.number + 1:04d}-image-{block['number'] + 1}",
        )
        fragment = (
            f'<figure class="embedded-figure" data-page="{page.number + 1}">'
            f'<img src="{html.escape(rel)}" alt="Embedded figure from page {page.number + 1}" />'
            f"</figure>"
        )
        objects.append(PageObject(kind="figure", top=bbox[1], value=fragment))
    return objects


def page_is_facsimile(page: fitz.Page) -> bool:
    text = page.get_text().strip()
    if len(text) >= PAGE_FACSIMILE_TEXT_THRESHOLD:
        return False
    raw = page.get_text("dict", sort=True)
    image_blocks = [block for block in raw["blocks"] if block["type"] == 1]
    if not image_blocks:
        return False
    page_area = page.rect.width * page.rect.height
    largest_area = max((block["bbox"][2] - block["bbox"][0]) * (block["bbox"][3] - block["bbox"][1]) for block in image_blocks)
    return largest_area / page_area >= 0.25


def flush_current_item(items: list[DocItem], current: DocItem | None) -> None:
    if current and current.text:
        current.text = current.text.strip()
        if current.inline_html is not None:
            current.inline_html = current.inline_html.strip()
        items.append(current)


def page_objects_for_text(lines: list[TextLine]) -> list[PageObject]:
    return [PageObject(kind="line", top=line.y0, value=line) for line in lines]


def process_page(
    page: fitz.Page,
    asset_root: Path,
    slug: str,
    repeated_top_keys: set[str],
    repeated_bottom_keys: set[str],
    sequential_margin_numbers: dict[int, set[str]],
) -> list[DocItem]:
    page_num = page.number + 1
    if page_is_facsimile(page) or page_has_complex_table(page):
        return [DocItem(kind="facsimile", page_num=page_num, html_fragment=render_page_facs(page, asset_root, slug))]

    table_bboxes: list[tuple[float, float, float, float]] = []
    lines = extract_text_lines(page, table_bboxes, repeated_top_keys, repeated_bottom_keys, sequential_margin_numbers)
    lines = merge_spelled_heading_fragments(lines, page.rect.width)
    median_font = median(line.font_size for line in lines) if lines else 11.0

    objects = page_objects_for_text(lines)
    objects.extend(extract_figures(page, table_bboxes, asset_root, slug))
    objects.sort(key=lambda obj: (obj.top, 0 if obj.kind == "line" else 1))

    items: list[DocItem] = []
    current: DocItem | None = None
    previous_line: TextLine | None = None
    page_width = page.rect.width

    def flush() -> None:
        nonlocal current, previous_line
        flush_current_item(items, current)
        current = None
        previous_line = None

    for obj in objects:
        if obj.kind == "table":
            flush()
            items.append(DocItem(kind="table", page_num=page_num, html_fragment=obj.value))
            continue
        if obj.kind == "figure":
            flush()
            items.append(DocItem(kind="figure", page_num=page_num, html_fragment=obj.value))
            continue

        line = obj.value
        assert isinstance(line, TextLine)

        if is_heading_line(line, median_font, page_width):
            flush()
            items.append(DocItem(kind="heading", page_num=page_num, text=line.text, inline_html=line.html_text, level=heading_level(line, median_font)))
            continue

        ordered = parse_ordered_marker(line.text)
        if ordered:
            style, ordinal, remainder = ordered
            if remainder:
                flush()
                current = DocItem(kind="ol_item", page_num=page_num, text=remainder, inline_html=html.escape(remainder), list_style=style, ordinal=ordinal)
                previous_line = line
            else:
                flush()
                current = DocItem(kind="ol_item", page_num=page_num, text="", inline_html="", list_style=style, ordinal=ordinal)
                previous_line = line
            continue

        bullet = BULLET_MARKER_RE.match(line.text)
        if bullet:
            flush()
            current = DocItem(kind="ul_item", page_num=page_num, text=bullet.group(1).strip(), inline_html=html.escape(bullet.group(1).strip()))
            previous_line = line
            continue

        if current is None:
            current = DocItem(kind="p", page_num=page_num, text=line.text, inline_html=line.html_text)
            previous_line = line
            continue

        if should_continue_item(current, line, previous_line):
            merge_item_text(current, line.text, line.html_text)
            previous_line = line
            continue

        flush()
        current = DocItem(kind="p", page_num=page_num, text=line.text, inline_html=line.html_text)
        previous_line = line

    flush()
    return items


def merge_boundary_items(items: list[DocItem]) -> list[DocItem]:
    merged: list[DocItem] = []
    for item in items:
        if merged and should_join_across_boundary(merged[-1], item):
            merge_doc_items(merged[-1], item)
            continue
        merged.append(item)
    return merged


def list_type_and_start(style: str | None, ordinal: int | None) -> tuple[str, str]:
    if style == "upper-roman":
        return ' type="I"', f' start="{ordinal or 1}"'
    if style == "lower-roman":
        return ' type="i"', f' start="{ordinal or 1}"'
    if style == "upper-alpha":
        return ' type="A"', f' start="{ordinal or 1}"'
    if style == "lower-alpha":
        return ' type="a"', f' start="{ordinal or 1}"'
    return "", f' start="{ordinal or 1}"'


def format_inline_text(text: str | None = None, inline_html: str | None = None) -> str:
    if inline_html is not None:
        return inline_html
    return html.escape(text or "")


def render_body(items: list[DocItem]) -> str:
    parts: list[str] = []
    open_list_kind: str | None = None
    open_list_style: str | None = None
    previous_ordinal: int | None = None

    def close_list() -> None:
        nonlocal open_list_kind, open_list_style, previous_ordinal
        if open_list_kind:
            parts.append(f"</{open_list_kind}>")
        open_list_kind = None
        open_list_style = None
        previous_ordinal = None

    for item in items:
        if item.kind == "heading":
            close_list()
            level = min(max(item.level or 2, 2), 4)
            parts.append(f"<h{level}>{format_inline_text(item.text, item.inline_html)}</h{level}>")
            continue

        if item.kind == "p":
            close_list()
            parts.append(f'<p data-page="{item.page_num}">{format_inline_text(item.text, item.inline_html)}</p>')
            continue

        if item.kind == "table":
            close_list()
            parts.append(f'<div class="table-wrap" data-page="{item.page_num}">{item.html_fragment}</div>')
            continue

        if item.kind in {"figure", "facsimile"}:
            close_list()
            parts.append(item.html_fragment or "")
            continue

        if item.kind == "ul_item":
            if open_list_kind != "ul":
                close_list()
                parts.append('<ul class="bullet-list">')
                open_list_kind = "ul"
            parts.append(f"<li>{format_inline_text(item.text, item.inline_html)}</li>")
            continue

        if item.kind == "ol_item":
            needs_new_list = (
                open_list_kind != "ol"
                or open_list_style != item.list_style
                or (previous_ordinal is not None and item.ordinal is not None and item.ordinal != previous_ordinal + 1)
            )
            if needs_new_list:
                close_list()
                type_attr, start_attr = list_type_and_start(item.list_style, item.ordinal)
                parts.append(f'<ol class="numbered-list"{type_attr}{start_attr}>')
                open_list_kind = "ol"
                open_list_style = item.list_style
            parts.append(f"<li>{format_inline_text(item.text, item.inline_html)}</li>")
            previous_ordinal = item.ordinal
            continue

    close_list()
    return "\n".join(parts)


def render_document(body_html: str) -> str:
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title></title>
  <style>
    :root {{
      --ink: #17130f;
      --paper: #fffdf8;
      --rule: #d8d1c3;
      --accent: #6d4c2f;
    }}
    * {{ box-sizing: border-box; }}
    html {{ background: #ece7df; }}
    body {{
      margin: 0;
      background: var(--paper);
      color: var(--ink);
      font-family: "Georgia", "Times New Roman", serif;
      line-height: 1.6;
    }}
    main {{
      max-width: 980px;
      margin: 32px auto;
      padding: 40px 56px 72px;
      background: var(--paper);
      box-shadow: 0 10px 35px rgba(0, 0, 0, 0.08);
    }}
    h1, h2, h3, h4 {{
      font-weight: 700;
      line-height: 1.25;
      margin: 1.15em 0 0.45em;
    }}
    h2 {{
      font-size: 1.35rem;
      text-transform: uppercase;
      letter-spacing: 0.04em;
    }}
    h3 {{
      font-size: 1.12rem;
    }}
    p {{
      margin: 0.65em 0;
      text-align: justify;
    }}
    ol, ul {{
      margin: 0.65em 0 0.95em 1.5em;
      padding: 0;
    }}
    li {{
      margin: 0.28em 0;
      padding-left: 0.2em;
    }}
    .table-wrap {{
      margin: 1.15em 0 1.45em;
      overflow-x: auto;
    }}
    table {{
      width: 100%;
      border-collapse: collapse;
      border: 1px solid var(--rule);
      font-size: 0.95rem;
    }}
    th, td {{
      border: 1px solid var(--rule);
      padding: 0.48rem 0.56rem;
      vertical-align: top;
    }}
    th {{
      background: #f6f1e8;
      text-align: left;
    }}
    figure {{
      margin: 1.3em 0 1.6em;
    }}
    figure img {{
      display: block;
      width: 100%;
      height: auto;
      border: 1px solid var(--rule);
      background: white;
    }}
    sup, sub {{
      font-size: 0.72em;
      line-height: 0;
      position: relative;
      vertical-align: baseline;
    }}
    sup {{
      top: -0.48em;
    }}
    sub {{
      bottom: -0.18em;
    }}
    @media print {{
      html, body {{
        background: white;
      }}
      main {{
        margin: 0;
        max-width: none;
        box-shadow: none;
        padding: 0;
      }}
      figure, table, p, li {{
        break-inside: avoid;
      }}
    }}
  </style>
</head>
<body>
  <main>
    <article>
{body_html}
    </article>
  </main>
</body>
</html>
"""


def convert_pdf(pdf_path: Path, doc_index: int, total_docs: int) -> tuple[str, str, int]:
    slug = slugify(pdf_path.stem)
    asset_root = ASSET_DIR / slug
    html_path = OUTPUT_DIR / f"{slug}.html"

    with fitz.open(pdf_path) as doc:
        doc_start = time.monotonic()
        page_count = len(doc)
        step = progress_step(page_count)
        repeated_top_keys, repeated_bottom_keys = extract_repeated_edge_keys(doc)
        sequential_margin_numbers = extract_sequential_margin_numbers(doc)
        log(f"[{doc_index}/{total_docs}] Converting {pdf_path.name} ({page_count} pages)")
        all_items: list[DocItem] = []
        for page_number, page in enumerate(doc, start=1):
            page_items = process_page(
                page,
                asset_root,
                slug,
                repeated_top_keys,
                repeated_bottom_keys,
                sequential_margin_numbers,
            )
            all_items.extend(page_items)
            if page_number == 1 or page_number == page_count or page_number % step == 0:
                log(
                    f"[{doc_index}/{total_docs}] {pdf_path.name}: "
                    f"{page_number}/{page_count} pages ({format_percent(page_number, page_count)}%)"
                )
        log(f"[{doc_index}/{total_docs}] {pdf_path.name}: rendering HTML")
        merged_items = merge_boundary_items(all_items)
        body_html = render_body(merged_items)
        document_html = render_document(body_html)
        html_path.write_text(document_html, encoding="utf-8")
        elapsed = round(time.monotonic() - doc_start, 1)
        log(f"[{doc_index}/{total_docs}] Finished {pdf_path.name} in {elapsed}s")
        return pdf_path.name, html_path.relative_to(OUTPUT_DIR).as_posix(), len(doc)


def main() -> None:
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    pdf_paths = sorted(ROOT.glob("*.pdf"))
    if not pdf_paths:
        raise SystemExit("No PDF files found.")

    total_docs = len(pdf_paths)
    log(f"Starting conversion for {total_docs} PDF files")
    entries = [convert_pdf(path, index, total_docs) for index, path in enumerate(pdf_paths, start=1)]
    log(f"Converted {len(entries)} PDF files into {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
