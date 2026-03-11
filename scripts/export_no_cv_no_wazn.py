#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
من out.csv (مخرجات الـ pipeline) يُنتج:
- no_cv.csv: كلمات يُفترض أن يكون لها cv/cv_advanced لكنها فارغة (مع استبعاد الأدوات والحروف).
- no_wazn.csv: كلمات لها جذر لكن بدون وزن (مع استبعاد الأدوات والحروف).

استخدام:
  # 1) إعادة توليد out.csv (بعد تعديل STRIPPED_CORRECTIONS أو no_root):
  #    PYTHONPATH=src python3 -m fvafk.cli -i data/quran-simple-clean.txt --limit-lines 500 --morphology --output-csv out.csv --arabic-tags
  # 2) استخراج no_cv و no_wazn:
  PYTHONPATH=src python3 scripts/export_no_cv_no_wazn.py --input out.csv
  PYTHONPATH=src python3 scripts/export_no_cv_no_wazn.py --input out.csv --no-cv no_cv.csv --no-wazn no_wazn.csv
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

# أنواع لا نعتبرها "يجب أن يكون لها CV" أو "يجب أن يكون لها وزن" (أدوات، حروف، مبنيات، ضمائر، إشارة، أسماء علم)
EXCLUDE_KIND = frozenset({
    "operator", "particle", "mabni", "demonstrative", "pronoun", "name",
    "أداة", "حرف", "مبني", "إشارة", "ضمير", "اسم علم",
})


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", "-i", default="out.csv", help="Input CSV from pipeline (e.g. out.csv)")
    p.add_argument("--no-cv", default="no_cv.csv", help="Output CSV: words that should have CV but did not")
    p.add_argument("--no-wazn", default="no_wazn.csv", help="Output CSV: words with root but no wazn")
    args = p.parse_args()

    path_in = Path(args.input)
    if not path_in.exists():
        print(f"Error: input file not found: {path_in}")
        return 1

    rows_no_cv: list[dict[str, str]] = []
    rows_no_wazn: list[dict[str, str]] = []

    with open(path_in, encoding="utf-8") as f:
        reader = csv.DictReader(f)
        fieldnames = reader.fieldnames or []
        for row in reader:
            kind = (row.get("kind") or "").strip()
            cv = (row.get("cv") or "").strip()
            word_wazn = (row.get("word_wazn") or "").strip()
            template = (row.get("template") or "").strip()
            root = (row.get("root") or "").strip()

            is_excluded = kind in EXCLUDE_KIND

            # no_cv: كلمة محتوى (غير مستبعدة) وبدون cv
            if not is_excluded and not cv:
                rows_no_cv.append(row)

            # no_wazn: كلمة محتوى، لها جذر، وبدون وزن
            if not is_excluded and root and not word_wazn and not template:
                rows_no_wazn.append(row)

    # كتابة no_cv.csv
    if fieldnames:
        out_cv = Path(args.no_cv)
        out_cv.parent.mkdir(parents=True, exist_ok=True)
        with open(out_cv, "w", encoding="utf-8", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            w.writerows(rows_no_cv)
        print(f"Wrote {len(rows_no_cv)} rows to {out_cv}")

    # كتابة no_wazn.csv
    if fieldnames:
        out_wazn = Path(args.no_wazn)
        out_wazn.parent.mkdir(parents=True, exist_ok=True)
        with open(out_wazn, "w", encoding="utf-8", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            w.writerows(rows_no_wazn)
        print(f"Wrote {len(rows_no_wazn)} rows to {out_wazn}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
