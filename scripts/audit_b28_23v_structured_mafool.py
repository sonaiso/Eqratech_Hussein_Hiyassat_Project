#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Batch 28.23V — structured-debug aggregates for gold mafool_bih rows (comparison-equivalent).

Uses the same ayah visit order and --max-rows cap as run_quran_i3rab_comparison with
canonical gold_csv ayah text. Does not write under data/.

Usage:
  PYTHONPATH=src python3 scripts/audit_b28_23v_structured_mafool.py --max-rows 2000
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any, List, Tuple

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))


def _read_gold_indexed(gold_path: Path) -> List[Tuple[int, Any]]:
    from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows

    rows = _read_gold_rows(str(gold_path))
    return list(enumerate(rows))


def _all_ayah_keys_sorted(indexed: List[Tuple[int, Any]]) -> list[tuple[int, int]]:
    return sorted({(r.surah, r.ayah) for _, r in indexed})


def _ayah_text_gold_csv(indexed: List[Tuple[int, Any]], surah: int, ayah: int) -> str:
    from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed

    return reconstruct_ayah_text_from_indexed(indexed, surah, ayah)


def main() -> int:
    ap = argparse.ArgumentParser(description="28.23V structured-debug mafool_bih audit")
    ap.add_argument("--gold", type=Path, default=ROOT / "data" / "quran_i3rab.csv")
    ap.add_argument("--max-rows", type=int, default=2000)
    ap.add_argument(
        "--max-repair-attempts",
        type=int,
        default=2,
        help="Same default as run_quran_i3rab_comparison",
    )
    args = ap.parse_args()

    from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah

    indexed = _read_gold_indexed(args.gold.resolve())
    to_visit = _all_ayah_keys_sorted(indexed)
    erqa_keys: set = set()
    max_rows = int(args.max_rows)
    max_rep = max(1, int(args.max_repair_attempts))

    rows_used = 0
    reason_c = Counter()
    tier_c = Counter()
    mafool_n = 0
    mafool_no_match = 0
    mafool_strict = 0

    for surah, ayah in to_visit:
        n_in_ayah = sum(1 for _, r in indexed if r.surah == surah and r.ayah == ayah)
        if max_rows > 0 and rows_used + n_in_ayah > max_rows:
            break
        rows_used += n_in_ayah

        ayah_text = _ayah_text_gold_csv(indexed, surah, ayah)
        res: Any = None
        for attempt in range(max_rep):
            res = evaluate_ayah(
                surah,
                ayah,
                indexed,
                erqa_keys,
                ayah_text or "",
                repair_pass=attempt,
                require_strict_comparator=True,
            )
            if res.decision == AyahDecision.PASS_STRICT:
                break
        assert res is not None

        for sd in res.structured_debug_rows or []:
            if (sd.get("gold_role") or "").strip() != "mafool_bih":
                continue
            mafool_n += 1
            reason = (sd.get("reason") or "").strip() or "(empty)"
            tier = (sd.get("comparator_tier") or "").strip() or "(empty)"
            reason_c[reason] += 1
            tier_c[tier] += 1
            if reason == "no_match":
                mafool_no_match += 1
            if tier == "strict_structural_match":
                mafool_strict += 1

    out = {
        "batch": "28.23V",
        "max_rows_cap": max_rows,
        "rows_used_in_window": rows_used,
        "gold_role_mafool_bih_structured_rows": mafool_n,
        "mafool_bih_reason_no_match": mafool_no_match,
        "mafool_bih_comparator_tier_strict_structural_match": mafool_strict,
        "reason_histogram": dict(reason_c.most_common()),
        "comparator_tier_histogram": dict(tier_c.most_common()),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
