#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
eval_mishkat.py - Official root-evaluation helper against Mishkat gold.

Usage:
  PYTHONPATH=src python3 scripts/eval_mishkat.py \
    --pipeline-output out_with_sources.csv \
    --gold data/mishkat_word_root.csv \
    --all-norms
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from fvafk.c2b.root_resolver.evaluator import evaluate, load_csv


def _root_raw(v: Optional[str]) -> str:
    return (v or "").strip().replace(" ", "")


def _root_all_norms(v: Optional[str]) -> str:
    s = _root_raw(v).replace("-", "")
    s = "".join(ch for ch in s if not (0x064B <= ord(ch) <= 0x0652 or ord(ch) == 0x0670))
    s = s.replace("أ", "ا").replace("إ", "ا").replace("آ", "ا").replace("ٱ", "ا")
    s = s.replace("ى", "ي")
    if len(s) >= 1 and s[0] == "ا":
        s = "ء" + s[1:]
    return s


def _aligned_pairs(pred_rows: List[Dict[str, str]], gold_rows: List[Dict[str, str]]) -> List[Tuple[Dict[str, str], Optional[Dict[str, str]]]]:
    # Reuse evaluator word alignment behavior indirectly by running evaluate input style:
    from fvafk.c2b.root_resolver.evaluator import align_rows

    return align_rows(pred_rows, gold_rows, word_key="word")


def _score_pairs(
    pairs: List[Tuple[Dict[str, str], Optional[Dict[str, str]]]],
    *,
    normalizer,
    source_key: str = "root_source",
) -> Dict[str, object]:
    total = 0
    correct = 0
    by_source: Dict[str, Dict[str, int]] = {}

    for pred, gold in pairs:
        if gold is None:
            continue
        p = normalizer(pred.get("root"))
        g = normalizer(gold.get("root"))
        total += 1
        src = (pred.get(source_key) or "").strip() or "unknown"
        by_source.setdefault(src, {"total": 0, "correct": 0})
        by_source[src]["total"] += 1
        if p == g:
            correct += 1
            by_source[src]["correct"] += 1

    per_source = {
        s: {
            "total": m["total"],
            "correct": m["correct"],
            "accuracy": (m["correct"] / m["total"]) if m["total"] else 0.0,
        }
        for s, m in by_source.items()
    }
    return {
        "total": total,
        "correct": correct,
        "accuracy": (correct / total) if total else 0.0,
        "per_source": per_source,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Evaluate pipeline roots against Mishkat gold.")
    ap.add_argument("--pipeline-output", required=True, type=Path, help="Pipeline CSV (e.g. out_with_sources.csv)")
    ap.add_argument("--gold", required=True, type=Path, help="Mishkat gold CSV (word,root,count)")
    ap.add_argument("--all-norms", action="store_true", help="Also print expanded normalization metric")
    args = ap.parse_args()

    pred = load_csv(args.pipeline_output)
    gold = load_csv(args.gold)
    if not pred:
        print("No rows in pipeline output.")
        return 1
    if not gold:
        print("No rows in gold file.")
        return 1

    print("=== Mishkat Evaluation (default evaluator) ===")
    default_result = evaluate(pred, gold, root_key="root", source_key="root_source")
    print(default_result)

    if args.all_norms:
        print("\n=== Mishkat Evaluation (strict raw roots) ===")
        pairs = _aligned_pairs(pred, gold)
        strict_result = _score_pairs(pairs, normalizer=_root_raw, source_key="root_source")
        print(strict_result)

        print("\n=== Mishkat Evaluation (expanded normalization) ===")
        expanded_result = _score_pairs(pairs, normalizer=_root_all_norms, source_key="root_source")
        print(expanded_result)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
