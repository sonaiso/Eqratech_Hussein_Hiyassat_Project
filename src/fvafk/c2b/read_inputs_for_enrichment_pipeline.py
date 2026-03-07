# STRICT MODE: do not strip/normalize diacritics anywhere in this script.
"""
Enrichment pipeline: reads operators_catalog_split.csv and writes
operators_catalog_split_enriched.csv with mechanical columns (prefixes, stem,
compound parts). Configurable via PREFIX_CHARS_FOR_ENRICHMENT.

Run from repo root:
  PYTHONPATH=src python -m fvafk.c2b.read_inputs_for_enrichment_pipeline
  PYTHONPATH=src python -m fvafk.c2b.read_inputs_for_enrichment_pipeline --src data/operators_catalog_split.csv --out data/operators_catalog_split_enriched.csv
"""
from __future__ import annotations

import argparse
import ast
import csv
import json
from pathlib import Path
from typing import List, Optional, Tuple

SCHEMA_VERSION = 1

BASE_COLUMNS = [
    "Group Number",
    "Arabic Group Name",
    "English Group Name",
    "Operator",
    "Purpose/Usage",
    "Example",
    "Note",
]

# Insert these immediately after Note, before any project_* columns.
MECH_COLUMNS_AFTER_NOTE = [
    "operator_has_diacritics",
    "operator_prefixes",
    "operator_is_prefixed",
    "operator_stem",
    "operator_compound_parts",
    "operator_compound_count",
]

DERIVED_COLUMNS = [
    "schema_version",
    "row_id",
    "project_quran_evidence_list_json",
    "project_quran_evidence_count",
    "project_modules_list_json",
    "project_modules_count",
]

# Arabic marks (used only for "has diacritics" detection and parsing prefix+mark variants)
FATHATAN = "\u064B"
DAMMATAN = "\u064C"
KASRATAN = "\u064D"
FATHA = "\u064E"
DAMMA = "\u064F"
KASRA = "\u0650"
SHADDA = "\u0651"
SUKUN = "\u0652"
DAGGER_ALIF = "\u0670"

ARABIC_MARKS: Tuple[str, ...] = (
    FATHATAN, DAMMATAN, KASRATAN, FATHA, DAMMA, KASRA, SHADDA, SUKUN, DAGGER_ALIF
)

# Choose your peeling set here:
# - conservative: ("و","ف","س")
# - full (OperatorsCatalog-like): ("و","ف","ب","ك","ل","س")
PREFIX_CHARS_FOR_ENRICHMENT: Tuple[str, ...] = ("و", "ف", "س")


def _has_diacritics(text: str) -> bool:
    if not text:
        return False
    return any(ch in ARABIC_MARKS for ch in text)


def _parse_maybe_list(value: object) -> List[str]:
    """
    Accept:
    - list -> list[str]
    - string that looks like JSON list (["a","b"]) or Python list (['a','b']) -> parse to list[str]
    - otherwise string -> [s] (caller may then split on | or ; for canonical formats).
    No diacritic stripping—only parse containers.
    """
    if value is None:
        return []
    if isinstance(value, list):
        return [str(x).strip() for x in value if str(x).strip()]
    s = (value if isinstance(value, str) else str(value)).strip()
    if not s:
        return []
    # Try JSON array
    try:
        parsed = json.loads(s)
        if isinstance(parsed, list):
            return [str(x).strip() for x in parsed if str(x).strip()]
    except (json.JSONDecodeError, TypeError):
        pass
    # Try Python literal list
    try:
        parsed = ast.literal_eval(s)
        if isinstance(parsed, list):
            return [str(x).strip() for x in parsed if str(x).strip()]
    except (ValueError, SyntaxError, TypeError):
        pass
    # Single string (caller may split on | or ; for canonical formats)
    return [s]


def _prefix_variants(letter: str) -> List[str]:
    # No stripping. Accept prefix letter optionally followed by ONE mark.
    return [letter] + [letter + m for m in ARABIC_MARKS]


PREFIX_VARIANTS: Tuple[str, ...] = tuple(
    p for ch in PREFIX_CHARS_FOR_ENRICHMENT for p in _prefix_variants(ch)
)


def _peel_prefixes_vowelized(token: str, max_prefixes: int = 3) -> Tuple[str, str]:
    """
    Peel up to max_prefixes from the start of a *vowelized* token.
    Prefixes can be 'و' or 'وَ' etc. We do not strip anything.
    Returns (prefixes_concat, remainder).
    """
    prefixes = ""
    remainder = token

    for _ in range(max_prefixes):
        matched = False
        for p in PREFIX_VARIANTS:
            if remainder.startswith(p) and len(remainder) > len(p):
                prefixes += p
                remainder = remainder[len(p):]
                matched = True
                break
        if not matched:
            break

    return prefixes, remainder


def _compound_split_vowelized(token: str, operators_set: set) -> List[str]:
    """
    Try to split token into [op1, op2] where both exist in operators_set.
    Prefer longest op1. All comparisons are vowelized, no stripping.
    """
    # Prefer longest first
    candidates = sorted(operators_set, key=len, reverse=True)
    for op1 in candidates:
        if token.startswith(op1) and len(op1) < len(token):
            rest = token[len(op1):]
            if rest in operators_set:
                return [op1, rest]
    return []


def _ensure_required_columns(fieldnames: Optional[List[str]]) -> None:
    if not fieldnames:
        raise ValueError("CSV has no header.")
    missing = [c for c in BASE_COLUMNS if c not in fieldnames]
    if missing:
        raise ValueError(f"Missing required columns: {missing}. Found: {fieldnames}")


def enrich_operators_catalog(
    src_csv: Path = Path("data/operators_catalog_split.csv"),
    out_csv: Path = Path("data/operators_catalog_split_enriched.csv"),
) -> None:
    if not src_csv.exists():
        raise FileNotFoundError(f"Source CSV not found: {src_csv}")

    out_csv.parent.mkdir(parents=True, exist_ok=True)

    with src_csv.open("r", encoding="utf-8-sig", newline="") as f_in:
        reader = csv.DictReader(f_in)
        _ensure_required_columns(reader.fieldnames)

        input_columns = list(reader.fieldnames or [])

        # Build output columns while preserving existing order, but inserting MECH_COLUMNS_AFTER_NOTE
        output_columns: List[str] = []
        inserted_mech = False
        for col in input_columns:
            output_columns.append(col)
            if col == "Note" and not inserted_mech:
                for mcol in MECH_COLUMNS_AFTER_NOTE:
                    if mcol not in output_columns:
                        output_columns.append(mcol)
                inserted_mech = True

        # If Note wasn't present for some reason, append mech at end (shouldn't happen)
        if not inserted_mech:
            for mcol in MECH_COLUMNS_AFTER_NOTE:
                if mcol not in output_columns:
                    output_columns.append(mcol)

        # Append derived columns (stable order)
        for c in DERIVED_COLUMNS:
            if c not in output_columns:
                output_columns.append(c)

        # Precompute operator set (vowelized) for compound splitting
        rows_cache: List[dict] = list(reader)
        operators_set = set((r.get("Operator") or "").strip() for r in rows_cache if (r.get("Operator") or "").strip())

        with out_csv.open("w", encoding="utf-8", newline="") as f_out:
            writer = csv.DictWriter(f_out, fieldnames=output_columns)
            writer.writeheader()

            for idx, row in enumerate(rows_cache, start=1):
                op = (row.get("Operator") or "").strip()
                if not op:
                    continue

                # Mechanical enrichment (strict: keep vowelized forms)
                has_d = 1 if _has_diacritics(op) else 0
                # If Operator is exactly in operators_set, never peel prefixes (e.g. فِي stays فِي)
                if op in operators_set:
                    prefixes, remainder = "", op
                else:
                    prefixes, remainder = _peel_prefixes_vowelized(op, max_prefixes=3)
                is_prefixed = 1 if prefixes else 0

                compound_parts = _compound_split_vowelized(op, operators_set)
                compound_str = "|".join(compound_parts) if compound_parts else ""
                compound_count = str(len(compound_parts)) if compound_parts else "0"

                row["operator_has_diacritics"] = str(has_d)
                row["operator_prefixes"] = prefixes
                row["operator_is_prefixed"] = str(is_prefixed)
                row["operator_stem"] = remainder
                row["operator_compound_parts"] = compound_str
                row["operator_compound_count"] = compound_count

                # Existing derived JSON/count columns (only meaningful if project_* columns exist in src)
                evidence_raw = row.get("project_quran_evidence_phrases", "")
                modules_raw = row.get("project_modules", "")

                evidence_list = _parse_maybe_list(evidence_raw)
                modules_list = _parse_maybe_list(modules_raw)

                # If evidence/modules are single strings, support the canonical delimited formats too
                if len(evidence_list) == 1 and "|" in evidence_list[0]:
                    evidence_list = [p.strip() for p in evidence_list[0].split("|") if p.strip()]
                if len(modules_list) == 1 and ";" in modules_list[0]:
                    modules_list = [p.strip() for p in modules_list[0].split(";") if p.strip()]

                row["schema_version"] = str(SCHEMA_VERSION)
                row["row_id"] = str(idx)
                row["project_quran_evidence_list_json"] = json.dumps(evidence_list, ensure_ascii=False)
                row["project_quran_evidence_count"] = str(len(evidence_list))
                row["project_modules_list_json"] = json.dumps(modules_list, ensure_ascii=False)
                row["project_modules_count"] = str(len(modules_list))

                writer.writerow(row)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--src", default="data/operators_catalog_split.csv")
    p.add_argument("--out", default="data/operators_catalog_split_enriched.csv")
    args = p.parse_args()
    enrich_operators_catalog(Path(args.src), Path(args.out))


if __name__ == "__main__":
    main()
