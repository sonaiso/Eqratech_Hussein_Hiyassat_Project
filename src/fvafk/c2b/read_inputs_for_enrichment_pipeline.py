"""
مولِّد الكتالوج المُثرى للأدوات النحوية
Enrichment pipeline: reads operators_catalog_split.csv and writes
operators_catalog_split_enriched.csv with derived columns used by the
Arabic grammar dataset tests under tests/c2b/.

Run as a module (e.g. from CI):
    PYTHONPATH=src python -m fvafk.c2b.read_inputs_for_enrichment_pipeline
"""
from __future__ import annotations

import csv
import sys
import unicodedata
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
_HERE = Path(__file__).resolve()
# Locate repository root: climb from src/fvafk/c2b/ → src/ → repo root
_REPO_ROOT = _HERE.parent.parent.parent.parent
_SOURCE_CSV = _REPO_ROOT / "data" / "operators_catalog_split.csv"
_OUTPUT_CSV = _REPO_ROOT / "data" / "operators_catalog_split_enriched.csv"

# Prefixes that commonly attach to operators in running text
# Maximum number of single-letter prefixes that can stack in Arabic
# (e.g. و+ف+ل as in وَفَلَـ)
_MAX_PREFIX_DEPTH = 3
_PREFIX_CHARS = frozenset("وفبكلس")


def _strip_diacritics(text: str) -> str:
    """Remove Arabic harakat / combining marks, keep base letters."""
    return "".join(
        ch for ch in unicodedata.normalize("NFC", text)
        if unicodedata.combining(ch) == 0
    ).replace("ـ", "").strip()


def _detect_prefixes(bare: str) -> str:
    """Return any leading single-letter prefixes found in _PREFIX_CHARS."""
    prefixes = ""
    remainder = bare
    for _ in range(_MAX_PREFIX_DEPTH):  # max Arabic prefix stacking depth
        if remainder and remainder[0] in _PREFIX_CHARS and len(remainder) > 1:
            prefixes += remainder[0]
            remainder = remainder[1:]
        else:
            break
    return prefixes


def enrich(source: Path = _SOURCE_CSV, output: Path = _OUTPUT_CSV) -> Path:
    """
    Read *source* CSV, add enrichment columns, and write to *output*.

    Added columns
    -------------
    operator_bare      : operator text with all diacritics stripped
    detected_prefixes  : leading conjunction / particle prefixes (if any)
    operator_core      : operator_bare after stripping detected_prefixes
    char_count         : number of characters in operator_bare
    """
    if not source.exists():
        raise FileNotFoundError(
            f"Source catalog not found: {source}\n"
            "Expected path: data/operators_catalog_split.csv relative to repo root."
        )

    output.parent.mkdir(parents=True, exist_ok=True)

    extra_fields = ["operator_bare", "detected_prefixes", "operator_core", "char_count"]

    with open(source, encoding="utf-8-sig", newline="") as fin, \
         open(output, "w", encoding="utf-8", newline="") as fout:

        reader = csv.DictReader(fin)
        assert reader.fieldnames is not None, (
            f"Source CSV missing header row. Ensure {source} contains a valid CSV "
            "with column headers."
        )

        writer = csv.DictWriter(fout, fieldnames=list(reader.fieldnames) + extra_fields)
        writer.writeheader()

        for row in reader:
            operator = (row.get("Operator") or "").strip()
            bare = _strip_diacritics(operator)
            prefixes = _detect_prefixes(bare)
            core = bare[len(prefixes):] if prefixes else bare

            row["operator_bare"] = bare
            row["detected_prefixes"] = prefixes
            row["operator_core"] = core
            row["char_count"] = str(len(bare))
            writer.writerow(row)

    return output


def main() -> None:
    try:
        out = enrich()
        print(f"[enrichment] Written: {out}", file=sys.stderr)
    except FileNotFoundError as exc:
        print(f"[enrichment] ERROR: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
