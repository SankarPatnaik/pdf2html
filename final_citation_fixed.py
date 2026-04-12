from __future__ import annotations

import argparse
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
BACKGROUND_IMAGE_AREA_RATIO = 0.65
EDGE_BAND_RATIO = 0.08
MARGIN_BAND_RATIO = 0.12
MARGIN_NUMBER_WIDTH = 48.0
FOOTNOTE_REGION_START = 0.82
FOOTNOTE_FONT_RATIO = 0.88

# Tightened super/sub rules
SUPER_SUB_SIZE_RATIO = 0.90
SUPER_RISE_RATIO = 0.16
SUB_DROP_RATIO = 0.10
SPAN_SPACE_GAP_RATIO = 0.22
SUPERSCRIPT_TOKEN_RE = re.compile(r"^(?:\d{1,3}|[A-Za-z]|[*†‡])$")
SUPERSCRIPT_HTML_RE = re.compile(r"<sup>([^<]+)</sup>")
CITATION_MARKER_TOKEN_RE = re.compile(r"^\d{1,4}[A-Za-z]?$")
FOOTNOTE_LEAD_RE = re.compile(r"^\(?\d{1,4}[A-Za-z]?\)?(?=(?:[.)])?(?:\s|$|[^\d]))")

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
    re.compile(r"^\d{4}\s+insc\s+\d+$", re.I),
    re.compile(r"^\d{4}:dhc:[\w-]+$", re.I),
    re.compile(r"^signature not verified$", re.I),
    re.compile(r"^digitally signed by$", re.I),
    re.compile(r"^reason:?$", re.I),
    re.compile(r"^date:?$", re.I),
]

ORDERED_MARKER_RE = re.compile(
    r"^\(?((?:\d{1,3})|(?:[IVXLCDMivxlcdm]{1,8})|(?:[A-Za-z]))([\.\)])(?:\s+|$)(.*)$"
)
BULLET_MARKER_RE = re.compile(r"^[\u2022\uf0b7\-]\s+(.*)$")
TOC_TITLE_RE = re.compile(r"^(index|contents|table of contents)$", re.I)
TOC_ENTRY_RE = re.compile(r"^(?:[A-Z]\.(?:\d+)?|[IVXLCDM]+\.)\s+\S")
TOC_DOT_LEADER_RE = re.compile(r"^.{4,}\.{5,}\s*\d+\s*$")
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
    rich_text: str
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
    rich_text: str | None = None
    level: int | None = None
    list_style: str | None = None
    ordinal: int | None = None
    html_fragment: str | None = None


@dataclass
class Endnote:
    marker: str
    text: str
    page_num: int
    target_id: str
    backref_id: str | None = None


def slugify(name: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9]+", "-", name).strip("-").lower()
    return safe or "document"


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


def strip_tags(text: str) -> str:
    return re.sub(r"<[^>]+>", "", text or "")


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
    if bbox[3] <= page_height * 0.12:
        if cleaned in {"(D)", "(D", "(d)", "(d)"}:
            return True
        if len(cleaned) <= 20 and any(char in cleaned for char in "$~#%+*") and not re.search(r"[a-z]{2,}", cleaned):
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
        style = "upper-alpha" if token.isupper() else "lower-alpha"
        return style, alpha_to_int(token), remainder
    roman = roman_to_int(token)
    if roman:
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
    return bool(re.search(r"[.!?\"'”’‖»]\s*$", text))


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


def join_rich_text(left: str, right: str) -> str:
    left = left.rstrip()
    right = right.lstrip()
    left_plain = strip_tags(left).rstrip()
    right_plain = strip_tags(right).lstrip()

    if not left:
        return right
    if not right:
        return left
    if left_plain.endswith("-") and right_plain[:1].islower():
        return left[:-1] + right
    if left_plain.endswith("/") or right_plain.startswith("/"):
        return left + right
    if left_plain.endswith(("(", "[", "{", "/")):
        return left + right
    if right_plain.startswith((",", ".", ";", ":", ")", "]", "}")):
        return left + right
    return left + " " + right


def spans_to_rich_text(spans: list[dict]) -> tuple[str, str]:
    if not spans:
        return "", ""

    meaningful_spans = [span for span in spans if normalize_text(span.get("text", ""))]
    if not meaningful_spans:
        return "", ""

    sizes = [float(span.get("size", 0.0) or 0.0) for span in meaningful_spans]
    base_size = median(sizes) if sizes else 0.0

    normal_spans = [span for span in meaningful_spans if float(span.get("size", 0.0) or 0.0) >= base_size * 0.95]
    baseline_group = normal_spans or meaningful_spans
    baseline_top = median(float(span.get("bbox", (0, 0, 0, 0))[1]) for span in baseline_group)
    baseline_bottom = median(float(span.get("bbox", (0, 0, 0, 0))[3]) for span in baseline_group)

    parts_plain: list[str] = []
    parts_rich: list[str] = []
    previous_bbox: tuple[float, float, float, float] | None = None
    previous_size: float | None = None

    for span in meaningful_spans:
        raw_text = span.get("text", "")
        bbox = tuple(span.get("bbox", (0.0, 0.0, 0.0, 0.0)))
        size = float(span.get("size", 0.0) or 0.0)
        text = normalize_text(raw_text)
        if not text:
            continue

        if parts_plain and previous_bbox is not None and previous_size is not None:
            gap = bbox[0] - previous_bbox[2]
            gap_threshold = max(1.0, previous_size * SPAN_SPACE_GAP_RATIO)
            if (
                gap > gap_threshold
                and not parts_plain[-1].endswith((" ", "-", "/", "(", "[", "{"))
                and not text.startswith((",", ".", ";", ":", ")", "]", "}"))
            ):
                parts_plain.append(" ")
                parts_rich.append(" ")

        top = float(bbox[1])
        bottom = float(bbox[3])

        is_small = size < base_size * SUPER_SUB_SIZE_RATIO
        is_sup = (
            is_small
            and SUPERSCRIPT_TOKEN_RE.fullmatch(text) is not None
            and bottom <= baseline_bottom - max(0.8, base_size * SUPER_RISE_RATIO)
            and top <= baseline_top
        )
        is_sub = (
            is_small
            and not is_sup
            and re.fullmatch(r"[\dA-Za-z]+", text) is not None
            and top >= baseline_top + max(0.8, base_size * SUB_DROP_RATIO)
        )

        escaped = html.escape(text)
        if is_sup and parts_rich:
            parts_plain.append(text)
            parts_rich.append(f"<sup>{escaped}</sup>")
        elif is_sub and parts_rich:
            parts_plain.append(text)
            parts_rich.append(f"<sub>{escaped}</sub>")
        else:
            parts_plain.append(text)
            parts_rich.append(escaped)

        previous_bbox = bbox
        previous_size = size

    return "".join(parts_plain), "".join(parts_rich)


def strip_prefix_rich_text_by_plain(plain_text: str, rich_text: str, prefix_plain: str) -> tuple[str, str]:
    if not prefix_plain:
        return plain_text, rich_text
    if not plain_text.startswith(prefix_plain):
        return plain_text, rich_text

    consumed = 0
    index = 0
    out_start = 0

    while index < len(rich_text) and consumed < len(prefix_plain):
        if rich_text[index] == "<":
            tag_end = rich_text.find(">", index)
            if tag_end == -1:
                break
            index = tag_end + 1
            out_start = index
            continue

        if prefix_plain[consumed] == rich_text[index]:
            consumed += 1
            index += 1
            out_start = index
            continue

        break

    return plain_text[len(prefix_plain):], rich_text[out_start:]


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

    centered = abs(((line.x0 + line.x1) / 2) - (page_width / 2)) <= page_width * 0.16
    larger = line.font_size >= median_font * 1.15
    normalized = re.sub(r"[^A-Za-z ]+", "", text).strip().upper()
    if normalized in HEADING_KEYWORDS and (text.strip() == text.strip().upper() or centered or line.bold or larger):
        return True

    letters = [char for char in text if char.isalpha()]
    if not letters:
        return False

    caps_ratio = sum(char.isupper() for char in letters) / len(letters)
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

    while len(cleaned_rows) >= 2:
        first = cleaned_rows[0]
        non_empty = [cell for cell in first if cell]
        if len(non_empty) == 1 and len(non_empty[0]) >= 12:
            cleaned_rows = cleaned_rows[1:]
            continue
        break
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


def extract_tables(page: fitz.Page) -> tuple[list[PageObject], list[tuple[float, float, float, float]], bool]:
    tables: list[PageObject] = []
    table_bboxes: list[tuple[float, float, float, float]] = []
    requires_facsimile = False
    try:
        with redirect_stdout(io.StringIO()):
            table_finder = page.find_tables()
    except Exception:
        return [], [], False

    page_area = page.rect.width * page.rect.height
    for table in table_finder.tables:
        rows = table.extract()
        metrics = table_metrics(rows)
        if not metrics:
            continue
        bbox = tuple(table.bbox)
        coverage = ((bbox[2] - bbox[0]) * (bbox[3] - bbox[1])) / page_area
        if table_should_render_as_html(metrics):
            html_fragment = table_to_html(rows)
            if html_fragment:
                tables.append(PageObject(kind="table", top=bbox[1], value=html_fragment))
                table_bboxes.append(bbox)
            continue
        if table_should_force_facsimile(metrics) and coverage >= 0.18:
            requires_facsimile = True
    return tables, table_bboxes, requires_facsimile


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
                plain_text, _ = spans_to_rich_text(line["spans"])
                text = normalize_text(plain_text)
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
                plain_text, _ = spans_to_rich_text(line["spans"])
                text = normalize_text(plain_text)
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


def is_small_metadata_line(
    text: str,
    bbox: tuple[float, float, float, float],
    font_size: float,
    page_width: float,
) -> bool:
    if font_size > 6.5:
        return False
    if bbox[0] > page_width * 0.28 and bbox[2] < page_width * 0.72:
        return False
    lowered = text.lower()
    return bool(
        "digitally signed" in lowered
        or re.fullmatch(r"date:\s*[\d./:-]+(?:\s*[ap]m)?", lowered)
        or re.fullmatch(r"\d{1,2}:\d{2}:\d{2}\s*[a-z]{2,4}", lowered)
        or re.fullmatch(r"[a-z .'-]{3,40}", lowered)
    )


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
            spans = [span for span in line["spans"] if normalize_text(span["text"])]
            if not spans:
                continue

            bbox = tuple(line["bbox"])
            if any(bbox_within(bbox, table_bbox) for table_bbox in table_bboxes):
                continue

            plain_text, rich_text = spans_to_rich_text(spans)
            plain_text = normalize_text(plain_text)
            if not plain_text:
                continue

            if is_noise_line(plain_text, bbox, page_num, page_count, page_height):
                continue

            if (
                plain_text in sequential_margin_numbers.get(page_num, set())
                and is_margin_number_candidate(plain_text, bbox, page_width)
            ):
                continue

            key = edge_text_key(plain_text)
            if bbox[3] <= page_height * EDGE_BAND_RATIO and key in repeated_top_keys:
                continue
            if bbox[1] >= page_height * (1 - EDGE_BAND_RATIO) and key in repeated_bottom_keys:
                continue

            font_size = max(span["size"] for span in spans)
            if is_small_metadata_line(plain_text, bbox, font_size, page_width):
                continue

            bold = any("bold" in span["font"].lower() or "black" in span["font"].lower() for span in spans)
            lines.append(TextLine(text=plain_text, rich_text=rich_text, bbox=bbox, font_size=font_size, bold=bold))
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
            letters_plain = [compact]
            letters_rich = [current.rich_text]
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
                    letters_plain.append(candidate_compact)
                    letters_rich.append(candidate.rich_text)
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
            if sum(len(fragment) for fragment in letters_plain) >= 4:
                merged.append(
                    TextLine(
                        text="".join(letters_plain),
                        rich_text="".join(letters_rich),
                        bbox=(x0, y0, x1, y1),
                        font_size=font_size,
                        bold=bold,
                    )
                )
                index = next_index
                continue
        merged.append(current)
        index += 1
    return merged


def merge_inline_line_fragments(lines: list[TextLine], page_width: float) -> list[TextLine]:
    if not lines:
        return []

    merged: list[TextLine] = []
    for line in sorted(lines, key=lambda item: (round(((item.y0 + item.y1) / 2) / 4), item.x0, item.y0)):
        if merged:
            previous = merged[-1]
            same_row = (
                abs(line.y0 - previous.y0) <= max(previous.font_size, line.font_size) * 0.35
                and abs(line.y1 - previous.y1) <= max(previous.font_size, line.font_size) * 0.45
            )
            gap = line.x0 - previous.x1
            max_gap = min(page_width * 0.18, max(previous.font_size, line.font_size) * 7.5)
            if same_row and -1.5 <= gap <= max_gap:
                previous.text = join_text(previous.text, line.text)
                previous.rich_text = join_rich_text(previous.rich_text, line.rich_text)
                previous.bbox = (
                    min(previous.x0, line.x0),
                    min(previous.y0, line.y0),
                    max(previous.x1, line.x1),
                    max(previous.y1, line.y1),
                )
                previous.font_size = max(previous.font_size, line.font_size)
                previous.bold = previous.bold or line.bold
                continue
        merged.append(TextLine(text=line.text, rich_text=line.rich_text, bbox=line.bbox, font_size=line.font_size, bold=line.bold))
    return merged


def page_is_toc(lines: list[TextLine]) -> bool:
    if not lines:
        return False

    title_present = any(TOC_TITLE_RE.fullmatch(line.text) for line in lines[:6])
    entry_count = sum(1 for line in lines if TOC_ENTRY_RE.match(line.text))
    dot_leader_count = sum(1 for line in lines if TOC_DOT_LEADER_RE.match(line.text))
    short_ratio = sum(1 for line in lines if len(line.text) <= 90) / len(lines)
    return (title_present and (entry_count >= 4 or dot_leader_count >= 2)) or (entry_count + dot_leader_count >= 8 and short_ratio >= 0.55)


def page_has_complex_layout(lines: list[TextLine], page_num: int) -> bool:
    if not lines or page_num > 3:
        return False

    short_ratio = sum(1 for line in lines if len(line.text) <= 110) / len(lines)
    has_present = any("present:" in line.text.lower() for line in lines)
    special_layout_hits = sum(
        1
        for line in lines
        if re.search(r"\b(present:|coram:|hon'?ble|through:|via video conferencing)\b", line.text, re.I)
    )
    keyword_hits = sum(
        1
        for line in lines
        if re.search(
            r"\b(through|versus|appellant|respondent|petitioner|plaintiff|defendant|decree holder|judgment pronounced on|date of decision|reserved on|pronounced on)\b",
            line.text,
            re.I,
        )
    )
    x_clusters = {round(line.x0 / 36) for line in lines if len(line.text) <= 120}
    if has_present and page_num <= 2 and short_ratio >= 0.35:
        return True
    if special_layout_hits >= 1 and short_ratio >= 0.45 and len(x_clusters) >= 2:
        return True
    return short_ratio >= 0.55 and keyword_hits >= 4 and len(x_clusters) >= 3


def is_footnote_line(line: TextLine, median_font: float, page_height: float) -> bool:
    if line.y0 < page_height * FOOTNOTE_REGION_START:
        return False
    if line.font_size > median_font * FOOTNOTE_FONT_RATIO:
        return False
    return bool(FOOTNOTE_LEAD_RE.match(line.text))


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
    text_length = len(page.get_text().strip())
    raw = page.get_text("dict", sort=True)
    for block in raw["blocks"]:
        if block["type"] != 1:
            continue
        bbox = tuple(block["bbox"])
        if any(bbox_within(bbox, table_bbox, tolerance=5.0) for table_bbox in table_bboxes):
            continue
        area = (bbox[2] - bbox[0]) * (bbox[3] - bbox[1])
        if text_length >= PAGE_FACSIMILE_TEXT_THRESHOLD and area / page_area >= BACKGROUND_IMAGE_AREA_RATIO:
            continue
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
        if current.rich_text is None:
            current.rich_text = html.escape(current.text)
        else:
            current.rich_text = current.rich_text.strip()
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

    table_objects, table_bboxes, table_requires_facsimile = extract_tables(page)
    if table_requires_facsimile:
        return [DocItem(kind="facsimile", page_num=page_num, html_fragment=render_page_facs(page, asset_root, slug))]

    lines = extract_text_lines(page, table_bboxes, repeated_top_keys, repeated_bottom_keys, sequential_margin_numbers)
    lines = merge_inline_line_fragments(lines, page.rect.width)
    lines = merge_spelled_heading_fragments(lines, page.rect.width)

    if page_is_toc(lines) or page_has_complex_layout(lines, page_num):
        return [DocItem(kind="facsimile", page_num=page_num, html_fragment=render_page_facs(page, asset_root, slug))]

    median_font = median(line.font_size for line in lines) if lines else 11.0

    objects = page_objects_for_text(lines)
    objects.extend(table_objects)
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

        if is_footnote_line(line, median_font, page.rect.height):
            if current and current.kind == "footnote" and should_continue_item(current, line, previous_line):
                current.text = join_text(current.text or "", line.text)
                current.rich_text = join_rich_text(current.rich_text or "", line.rich_text)
                previous_line = line
                continue
            flush()
            current = DocItem(kind="footnote", page_num=page_num, text=line.text, rich_text=line.rich_text)
            previous_line = line
            continue

        if is_heading_line(line, median_font, page_width):
            flush()
            items.append(
                DocItem(
                    kind="heading",
                    page_num=page_num,
                    text=line.text,
                    rich_text=line.rich_text,
                    level=heading_level(line, median_font),
                )
            )
            continue

        ordered = parse_ordered_marker(line.text)
        if ordered:
            style, ordinal, _ = ordered
            match = ORDERED_MARKER_RE.match(line.text)
            assert match is not None
            prefix_plain = line.text[:match.start(3)]
            remainder_plain, remainder_rich = strip_prefix_rich_text_by_plain(line.text, line.rich_text, prefix_plain)

            flush()
            current = DocItem(
                kind="ol_item",
                page_num=page_num,
                text=remainder_plain.strip(),
                rich_text=remainder_rich.strip(),
                list_style=style,
                ordinal=ordinal,
            )
            previous_line = line
            continue

        bullet = BULLET_MARKER_RE.match(line.text)
        if bullet:
            prefix_plain = line.text[:bullet.start(1)]
            remainder_plain, remainder_rich = strip_prefix_rich_text_by_plain(line.text, line.rich_text, prefix_plain)

            flush()
            current = DocItem(
                kind="ul_item",
                page_num=page_num,
                text=remainder_plain.strip(),
                rich_text=remainder_rich.strip(),
            )
            previous_line = line
            continue

        if current is None:
            current = DocItem(kind="p", page_num=page_num, text=line.text, rich_text=line.rich_text)
            previous_line = line
            continue

        if should_continue_item(current, line, previous_line):
            current.text = join_text(current.text or "", line.text)
            current.rich_text = join_rich_text(current.rich_text or "", line.rich_text)
            previous_line = line
            continue

        flush()
        current = DocItem(kind="p", page_num=page_num, text=line.text, rich_text=line.rich_text)
        previous_line = line

    flush()
    return items


def merge_boundary_items(items: list[DocItem]) -> list[DocItem]:
    merged: list[DocItem] = []
    for item in items:
        if merged and should_join_across_boundary(merged[-1], item):
            merged[-1].text = join_text(merged[-1].text or "", item.text or "")
            merged[-1].rich_text = join_rich_text(merged[-1].rich_text or "", item.rich_text or "")
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


def render_inline_html(item: DocItem) -> str:
    if item.rich_text is not None:
        return item.rich_text
    return html.escape(item.text or "")


def normalize_citation_marker(marker: str) -> str | None:
    cleaned = html.unescape(strip_tags(marker or "")).strip()
    if CITATION_MARKER_TOKEN_RE.fullmatch(cleaned):
        return cleaned
    return None


def citation_anchor_id(marker: str, page_num: int) -> str:
    suffix = re.sub(r"[^A-Za-z0-9]+", "-", marker).strip("-").lower()
    return f"citation-{suffix or 'note'}-p{page_num}"


def superscript_markers_from_rich_text(rich_text: str | None) -> list[str]:
    if not rich_text:
        return []

    markers: list[str] = []
    for raw_marker in SUPERSCRIPT_HTML_RE.findall(rich_text):
        marker = normalize_citation_marker(raw_marker)
        if marker:
            markers.append(marker)
    return markers


def collect_page_superscript_refs(items: list[DocItem]) -> dict[int, list[str]]:
    refs_by_page: dict[int, list[str]] = defaultdict(list)
    seen_by_page: dict[int, set[str]] = defaultdict(set)

    for item in items:
        if item.kind == "footnote":
            continue
        for marker in superscript_markers_from_rich_text(item.rich_text):
            if marker in seen_by_page[item.page_num]:
                continue
            refs_by_page[item.page_num].append(marker)
            seen_by_page[item.page_num].add(marker)
    return refs_by_page


def strip_footnote_marker(text: str, marker: str) -> str:
    cleaned = text.lstrip()
    index = 0
    if cleaned.startswith("("):
        index += 1
    if not cleaned[index:].startswith(marker):
        return cleaned.strip()

    index += len(marker)
    if index < len(cleaned) and cleaned[index] == ")":
        index += 1
    if index < len(cleaned) and cleaned[index] == ".":
        index += 1
    while index < len(cleaned) and cleaned[index].isspace():
        index += 1
    return cleaned[index:].strip()


def split_footnote_segments(text: str, page_markers: list[str]) -> list[tuple[str, str]]:
    cleaned = normalize_text(strip_tags(text))
    if not cleaned:
        return []

    normalized_markers = [marker for marker in page_markers if normalize_citation_marker(marker)]
    seen_markers: set[str] = set()
    unique_markers: list[str] = []
    for marker in normalized_markers:
        if marker not in seen_markers:
            unique_markers.append(marker)
            seen_markers.add(marker)

    if unique_markers:
        marker_alts = "|".join(re.escape(marker) for marker in sorted(unique_markers, key=len, reverse=True))
        split_re = re.compile(
            rf"(?:(?<=^)|(?<=\s))\(?({marker_alts})\)?(?=(?:[.)])?(?:\s|$|[^\d]))"
        )
        matches = list(split_re.finditer(cleaned))
        if matches:
            segments: list[tuple[str, str]] = []
            for index, match in enumerate(matches):
                start = match.start()
                end = matches[index + 1].start() if index + 1 < len(matches) else len(cleaned)
                marker = match.group(1)
                chunk = cleaned[start:end].strip()
                content = strip_footnote_marker(chunk, marker)
                if content:
                    segments.append((marker, content))
            if segments:
                return segments

    lead_match = re.match(r"^\(?(\d{1,4}[A-Za-z]?)\)?(?=(?:[.)])?(?:\s|$|[^\d]))", cleaned)
    if not lead_match:
        return []

    marker = lead_match.group(1)
    content = strip_footnote_marker(cleaned, marker)
    if not content:
        return []
    return [(marker, content)]


def link_citation_endnotes(items: list[DocItem], page_refs: dict[int, list[str]]) -> tuple[list[DocItem], list[Endnote]]:
    all_ref_markers = {marker for markers in page_refs.values() for marker in markers}
    endnotes: list[Endnote] = []
    endnote_lookup: dict[tuple[int, str], Endnote] = {}
    seen_endnotes: set[tuple[int, str, str]] = set()
    footnote_rewrites: dict[int, DocItem | None] = {}

    for index, item in enumerate(items):
        if item.kind != "footnote":
            continue

        page_markers = page_refs.get(item.page_num, [])
        segments = split_footnote_segments(item.text or "", page_markers)
        if not segments:
            footnote_rewrites[index] = item
            continue

        unmatched_segments: list[tuple[str, str]] = []
        matched_any = False
        for marker, content in segments:
            if marker not in all_ref_markers or marker not in page_markers:
                unmatched_segments.append((marker, content))
                continue

            dedupe_key = (item.page_num, marker, normalize_text(content))
            if dedupe_key not in seen_endnotes:
                endnote = Endnote(
                    marker=marker,
                    text=content,
                    page_num=item.page_num,
                    target_id=citation_anchor_id(marker, item.page_num),
                )
                endnotes.append(endnote)
                endnote_lookup[(item.page_num, marker)] = endnote
                seen_endnotes.add(dedupe_key)
            matched_any = True

        if not matched_any and unmatched_segments:
            footnote_rewrites[index] = item
            continue

        if unmatched_segments:
            reconstructed = " ".join(
                f"{marker}{'' if content.startswith(('(', '[', ',', '.', ';', ':')) else ' '}{content}"
                for marker, content in unmatched_segments
            ).strip()
            footnote_rewrites[index] = (
                DocItem(
                    kind="footnote",
                    page_num=item.page_num,
                    text=reconstructed,
                    rich_text=html.escape(reconstructed),
                )
                if reconstructed
                else None
            )
            continue

        footnote_rewrites[index] = None

    if not endnotes:
        return items, []

    ref_counts: dict[str, int] = defaultdict(int)
    body_items: list[DocItem] = []

    for index, item in enumerate(items):
        if item.kind == "footnote":
            replacement = footnote_rewrites.get(index, item)
            if replacement is not None:
                body_items.append(replacement)
            continue

        if item.rich_text:
            def replace_superscript(match: re.Match[str]) -> str:
                marker = normalize_citation_marker(match.group(1))
                if marker is None:
                    return match.group(0)

                endnote = endnote_lookup.get((item.page_num, marker))
                if endnote is None:
                    return match.group(0)

                ref_counts[endnote.target_id] += 1
                ref_id = f"{endnote.target_id}-ref-{ref_counts[endnote.target_id]}"
                if endnote.backref_id is None:
                    endnote.backref_id = ref_id
                return (
                    f'<sup id="{ref_id}" class="citation-ref">'
                    f'<a href="#{endnote.target_id}">{html.escape(marker)}</a>'
                    f"</sup>"
                )

            item.rich_text = SUPERSCRIPT_HTML_RE.sub(replace_superscript, item.rich_text)

        body_items.append(item)

    return body_items, endnotes


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
            parts.append(f"<h{level}>{render_inline_html(item)}</h{level}>")
            continue

        if item.kind == "p":
            close_list()
            parts.append(f'<p data-page="{item.page_num}">{render_inline_html(item)}</p>')
            continue

        if item.kind == "footnote":
            close_list()
            parts.append(f'<p class="footnote" data-page="{item.page_num}">{render_inline_html(item)}</p>')
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
            parts.append(f"<li>{render_inline_html(item)}</li>")
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
            parts.append(f"<li>{render_inline_html(item)}</li>")
            previous_ordinal = item.ordinal
            continue

    close_list()
    return "\n".join(parts)


def render_endnotes(endnotes: list[Endnote]) -> str:
    linked_endnotes = [endnote for endnote in endnotes if endnote.backref_id]
    if not linked_endnotes:
        return ""

    parts = [
        '<section class="citations" aria-labelledby="citations-heading">',
        '<h2 id="citations-heading">Citations</h2>',
        '<ol class="citation-list">',
    ]
    for endnote in linked_endnotes:
        backref = ""
        if endnote.backref_id:
            backref = (
                f' <a class="citation-backref" href="#{endnote.backref_id}" '
                f'aria-label="Back to citation {html.escape(endnote.marker)}">back</a>'
            )
        parts.append(
            f'<li id="{endnote.target_id}" data-page="{endnote.page_num}">'
            f'<span class="citation-marker">{html.escape(endnote.marker)}</span>'
            f'<span class="citation-text">{html.escape(endnote.text)}{backref}</span>'
            f"</li>"
        )
    parts.append("</ol>")
    parts.append("</section>")
    return "\n".join(parts)


def render_document(body_html: str, citations_html: str = "") -> str:
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
    .footnote {{
      font-size: 0.9rem;
      line-height: 1.45;
      margin-top: 0.5em;
    }}
    .citation-ref a {{
      color: inherit;
      text-decoration: none;
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
    .citations {{
      margin-top: 2.75rem;
      padding-top: 1.4rem;
      border-top: 1px solid var(--rule);
      break-before: page;
      page-break-before: always;
    }}
    .citations h2 {{
      margin-top: 0;
    }}
    .citation-list {{
      list-style: none;
      margin: 0.9rem 0 0;
      padding: 0;
    }}
    .citation-list li {{
      display: grid;
      grid-template-columns: minmax(2.8rem, auto) 1fr;
      gap: 0.85rem;
      align-items: start;
      margin: 0.55rem 0;
      padding: 0;
    }}
    .citation-marker {{
      font-weight: 700;
    }}
    .citation-text {{
      min-width: 0;
    }}
    .citation-backref {{
      color: var(--accent);
      text-decoration: none;
      margin-left: 0.3rem;
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
{citations_html}
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
        page_superscript_refs = collect_page_superscript_refs(all_items)
        linked_items, endnotes = link_citation_endnotes(all_items, page_superscript_refs)
        merged_items = merge_boundary_items(linked_items)
        body_html = render_body(merged_items)
        citations_html = render_endnotes(endnotes)
        document_html = render_document(body_html, citations_html)
        html_path.write_text(document_html, encoding="utf-8")
        elapsed = round(time.monotonic() - doc_start, 1)
        log(f"[{doc_index}/{total_docs}] Finished {pdf_path.name} in {elapsed}s")
        return pdf_path.name, html_path.relative_to(OUTPUT_DIR).as_posix(), len(doc)


def collect_pdf_paths(inputs: list[str]) -> list[Path]:
    if not inputs:
        candidates = ROOT.rglob("*.pdf")
    else:
        paths: list[Path] = []
        for raw in inputs:
            path = Path(raw)
            if not path.is_absolute():
                path = (ROOT / path).resolve()
            if path.is_dir():
                paths.extend(path.rglob("*.pdf"))
            elif path.is_file() and path.suffix.lower() == ".pdf":
                paths.append(path)
        candidates = paths

    pdf_paths: list[Path] = []
    seen: set[Path] = set()
    for path in candidates:
        resolved = path.resolve()
        if OUTPUT_DIR in resolved.parents:
            continue
        if resolved not in seen:
            pdf_paths.append(resolved)
            seen.add(resolved)
    return sorted(pdf_paths)


def main() -> None:
    parser = argparse.ArgumentParser(description="Convert court PDFs to HTML.")
    parser.add_argument(
        "inputs",
        nargs="*",
        help="PDF files or directories to convert. Defaults to all PDFs under the workspace.",
    )
    args = parser.parse_args()

    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    pdf_paths = collect_pdf_paths(args.inputs)
    if not pdf_paths:
        raise SystemExit("No PDF files found.")

    total_docs = len(pdf_paths)
    log(f"Starting conversion for {total_docs} PDF files")
    entries = [convert_pdf(path, index, total_docs) for index, path in enumerate(pdf_paths, start=1)]
    log(f"Converted {len(entries)} PDF files into {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
