#!/usr/bin/env python3
"""
QA check for operators catalog enriched output.
- Key clitics (بِ, لِ, وَ, فَ, كَ) must have project_quran_evidence_count > 0.
- فِي must not be peeled (operator_prefixes empty, operator_stem = فِي).
- Defaults coverage: if project_effect_signature is non-empty, require
  project_usage_universal_ar and project_i3rab_template non-empty.
- No header-artifact row: no record has Operator == "Operator" (duplicate header).
- Row count sanity: total rows > 0; row_id unique if present; warn on duplicate (Group, Operator, Purpose).
Run from repo root after generate_operators_catalog_enriched.sh.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

ENRICHED_CSV = Path("data/operators_catalog_split_project_enriched.csv")
CLITICS_NEED_EVIDENCE = ("بِ", "لِ", "وَ", "فَ", "كَ")
FII_OPERATOR = "فِي"


def main() -> int:
    if not ENRICHED_CSV.exists():
        print(f"QA fail: {ENRICHED_CSV} not found. Run generate_operators_catalog_enriched.sh first.")
        return 1

    seen = {op: None for op in CLITICS_NEED_EVIDENCE}
    fii_prefixes = None
    fii_stem = None
    defaults_violations: list[str] = []
    header_artifact_seen = False
    total_rows = 0
    row_ids: list[str] = []
    triples: list[tuple[str, str, str]] = []

    with ENRICHED_CSV.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            total_rows += 1
            rid = (row.get("row_id") or "").strip()
            if rid:
                row_ids.append(rid)
            grp = (row.get("Arabic Group Name") or "").strip()
            op = (row.get("Operator") or "").strip()
            purpose = (row.get("Purpose/Usage") or "").strip()
            triples.append((grp, op, purpose))
            if (row.get("Operator") or "").strip() == "Operator" and (row.get("Arabic Group Name") or "").strip() == "Arabic Group Name":
                header_artifact_seen = True
            if op in seen and seen[op] is None:
                count_s = (row.get("project_quran_evidence_count") or "").strip()
                try:
                    seen[op] = int(count_s) if count_s else 0
                except ValueError:
                    seen[op] = 0
            if op == FII_OPERATOR:
                fii_prefixes = (row.get("operator_prefixes") or "").strip()
                fii_stem = (row.get("operator_stem") or "").strip()

            # Defaults coverage: signature present => usage (and template unless allowed blank)
            sig = (row.get("project_effect_signature") or "").strip()
            usage = (row.get("project_usage_universal_ar") or "").strip()
            template = (row.get("project_i3rab_template") or "").strip()
            template_optional = sig in ("MUQATTAAT",)  # signatures that may have blank template
            if sig and (not usage or (not template_optional and not template)):
                defaults_violations.append(f"{op!r} (sig={sig}): missing usage or template")

    failed = False

    # Row count sanity
    if total_rows == 0:
        print("QA fail: total rows is 0.")
        failed = True
    else:
        print(f"QA pass: total rows = {total_rows}")
    if row_ids and len(row_ids) != len(set(row_ids)):
        print("QA fail: row_id values are not unique.")
        failed = True
    elif row_ids:
        print("QA pass: row_id unique")
    if len(triples) != len(set(triples)):
        dupes = len(triples) - len(set(triples))
        print(f"QA warn: {dupes} duplicate (Arabic Group Name, Operator, Purpose/Usage) triple(s)")

    for op in CLITICS_NEED_EVIDENCE:
        count = seen.get(op)
        if count is None:
            print(f"QA skip: operator {op!r} not in catalog (no row to check).")
            continue
        elif count <= 0:
            print(f"QA fail: {op!r} has project_quran_evidence_count={count} (expected > 0).")
            failed = True
        else:
            print(f"QA pass: {op!r} evidence count = {count}")

    if fii_prefixes is None or fii_stem is None:
        print(f"QA fail: {FII_OPERATOR!r} not found in CSV.")
        failed = True
    elif fii_prefixes != "" or fii_stem != FII_OPERATOR:
        print(f"QA fail: فِي should not be peeled (prefixes={fii_prefixes!r}, stem={fii_stem!r}).")
        failed = True
    else:
        print(f"QA pass: فِي not peeled (prefixes='', stem='فِي')")

    # No header-artifact row
    if header_artifact_seen:
        print("QA fail: header-artifact row (Operator='Operator') found in enriched CSV.")
        failed = True
    else:
        print("QA pass: no header-artifact row")

    # Defaults coverage
    if defaults_violations:
        for v in defaults_violations:
            print(f"QA fail: defaults coverage — {v}")
        failed = True
    else:
        print("QA pass: defaults coverage (signature => usage + template)")

    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
