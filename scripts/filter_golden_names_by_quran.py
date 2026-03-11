#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Filter data/golden_name_base.csv so that only entries that appear in
data/quran-simple-clean.txt are kept. Golden names must exist in the Quran text.
"""
from __future__ import annotations

import csv
import unicodedata
from pathlib import Path


def strip_diacritics(text: str) -> str:
    """Match special_words_catalog normalization."""
    return "".join(
        c for c in unicodedata.normalize("NFC", (text or ""))
        if unicodedata.combining(c) == 0
    ).replace("\u0640", "").strip()


def build_quran_bare_set(quran_path: Path) -> set[str]:
    """Collect bare form of every token in Quran (sura|aya|text)."""
    out = set()
    with open(quran_path, encoding="utf-8") as f:
        for line in f:
            parts = line.strip().split("|")
            if len(parts) < 3:
                continue
            for token in parts[2].split():
                bare = strip_diacritics(token)
                if bare:
                    out.add(bare)
    return out


def row_appears_in_quran(row: dict, quran_bare: set[str]) -> bool:
    """True if base, best_vocalized, or any variant_top form exists in Quran."""
    base = (row.get("base") or row.get("seed") or "").strip()
    if not base:
        return True  # keep rows with no base
    bare_base = strip_diacritics(base)
    forms = [bare_base]
    best = (row.get("best_vocalized") or "").strip()
    if best:
        forms.append(strip_diacritics(best))
    for part in (row.get("variants_top") or "").strip().split(";"):
        part = part.strip()
        form = part[: part.index("(")].strip() if "(" in part else part
        if form:
            forms.append(strip_diacritics(form))
    for bare_form in forms:
        if not bare_form:
            continue
        if " " in bare_form:
            if all(strip_diacritics(w) in quran_bare for w in bare_form.split()):
                return True
        elif bare_form in quran_bare:
            return True
    return False


def main() -> int:
    base_dir = Path(__file__).resolve().parent.parent
    quran_path = base_dir / "data" / "quran-simple-clean.txt"
    golden_path = base_dir / "data" / "golden_name_base.csv"
    if not quran_path.exists():
        print(f"Missing: {quran_path}")
        return 1
    if not golden_path.exists():
        print(f"Missing: {golden_path}")
        return 1

    quran_bare = build_quran_bare_set(quran_path)
    print(f"Quran bare tokens: {len(quran_bare)}")

    rows = []
    with open(golden_path, encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        fieldnames = list(reader.fieldnames or [])
        for row in reader:
            if row_appears_in_quran(row, quran_bare):
                rows.append(row)
            else:
                base = row.get("base") or row.get("seed") or ""
                print(f"  Dropped (not in Quran): {base!r}")

    with open(golden_path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    print(f"Kept {len(rows)} rows; wrote {golden_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
