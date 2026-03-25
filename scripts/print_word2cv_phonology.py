#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Proof / debug: phonology (CV + cv_advanced) using **only** ``src/word-2-cv.py``.

Does not import fvafk, pipeline, or C2a — uses ``src/word2cv_authority.py`` (same
logic as ``c1.cv_analysis`` / L6_PHONOLOGY).

Usage (from repo root):
  python3 scripts/print_word2cv_phonology.py "الرَّحْمَنُ"
  python3 scripts/print_word2cv_phonology.py "الرَّحْمَنُ عَلَى الْعَرْشِ"
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(repo / "src"))
    from word2cv_authority import compute_authoritative_cv_analysis, load_word2cv_module

    p = argparse.ArgumentParser(
        description="Print CV / cv_advanced from src/word-2-cv.py only (normalize + analyze per Arabic token)."
    )
    p.add_argument("text", help="Arabic text (one or more words)")
    p.add_argument(
        "--raw",
        action="store_true",
        help="Also print NFC-normalized input token before hamza/harakat fixes",
    )
    args = p.parse_args()

    m = load_word2cv_module()
    normalize_word = m.normalize_word
    raw = args.text
    normalized_input = normalize_word(raw)
    print("input (NFC, tatweel stripped):", repr(normalized_input))
    print()

    r = compute_authoritative_cv_analysis(raw)
    words = r.get("words") or []
    if not words:
        print("no Arabic tokens found.")
        return 1

    for i, row in enumerate(words):
        tok = row["word"]
        print(f"--- token {i + 1}: {tok!r} ---")
        if args.raw:
            print("  surface (normalize_word only):", repr(tok))
        if row.get("excluded"):
            print("  status: EXCLUDED (should_exclude / muqattaat / etc.)")
            print("  cv:", repr(row.get("cv", "")))
            print("  cv_advanced:", repr(row.get("cv_advanced", "")))
        else:
            print("  word_normalized:", repr(row["word_normalized"]))
            print("  cv:           ", row["cv"])
            print("  cv_advanced:  ", row["cv_advanced"])
            print("  cv_law_ok:    ", row["cv_law_ok"], f"({row['cv_law_reason']})")
        print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
