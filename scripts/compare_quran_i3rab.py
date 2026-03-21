#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compare L11 iʿrāb strings to `data/quran_i3rab.csv` gold.

Writes:
  - erqa_i3rab.csv — cumulative matches (append; includes ayah_word_index for stable keys)
  - wrong_i3rab.csv — failures from **this run only** (overwrite)

Usage (from repo root):
  PYTHONPATH=src python3 scripts/compare_quran_i3rab.py \\
    --gold data/quran_i3rab.csv --erqa erqa_i3rab.csv --wrong wrong_i3rab.csv

Stop: all gold rows covered in erqa, or current-run wrong count exceeds --max-wrong (default 100).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def _project_root() -> Path:
    return Path(__file__).resolve().parent.parent


def main() -> int:
    root = _project_root()
    ap = argparse.ArgumentParser(description="Compare pipeline L11 i3rab to Quranic gold CSV")
    ap.add_argument("--gold", type=Path, default=root / "data" / "quran_i3rab.csv", help="Gold CSV path")
    ap.add_argument("--erqa", type=Path, default=root / "erqa_i3rab.csv", help="Cumulative matches output")
    ap.add_argument("--wrong", type=Path, default=root / "wrong_i3rab.csv", help="Current-run failures output")
    ap.add_argument("--max-wrong", type=int, default=100, help="Stop when wrong rows this run exceed this value")
    ap.add_argument("--json-summary", action="store_true", help="Print summary JSON to stdout")
    args = ap.parse_args()

    gold = args.gold.resolve()
    if not gold.is_file():
        print(f"Gold CSV not found: {gold}", file=sys.stderr)
        return 1

    sys.path.insert(0, str(root / "src"))

    from orchestrator import run_pipeline
    from orchestrator.quran_gold.i3rab_compare_pipeline import (
        extract_l11_i3rab_sequence,
        run_compare_pass,
    )

    def system_i3rab_for_ayah(surah: int, ayah: int, words: list[str]):
        text = " ".join(words)
        pipeline = run_pipeline(
            text,
            source={"entrypoint": "compare_quran_i3rab", "surah": surah, "ayah": ayah},
        )
        return extract_l11_i3rab_sequence(pipeline, len(words))

    summary = run_compare_pass(
        str(gold),
        str(args.erqa.resolve()),
        str(args.wrong.resolve()),
        system_i3rab_for_ayah,
        max_wrong_run=args.max_wrong,
    )
    if args.json_summary:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
    else:
        print(
            "done:",
            f"new_matches={summary['new_matches']}",
            f"wrong_this_run={summary['wrong_this_run']}",
            f"remaining_pending={summary['remaining_pending']}",
            f"stopped={summary['stopped_reason']}",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
