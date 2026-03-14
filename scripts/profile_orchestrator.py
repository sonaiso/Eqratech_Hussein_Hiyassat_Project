#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Stage 11 — Run orchestrator on canonical inputs and print profiling report.

Usage:
  PYTHONPATH=src python3 scripts/profile_orchestrator.py
  PYTHONPATH=src python3 scripts/profile_orchestrator.py --json report.json
"""

from __future__ import annotations

import argparse
import json
import sys

BENCHMARK_INPUTS = [
    "وَ",
    "في",
    "!",
    "يَا رَبِّ",
    "كَاتِبٌ",
    "إِنَّ اللَّهَ غَفُورٌ",
]


def main() -> int:
    ap = argparse.ArgumentParser(description="Profile orchestrator on canonical inputs")
    ap.add_argument("--json", metavar="FILE", help="Write JSON report to file")
    ap.add_argument("--render", choices=["compact", "detailed", "debug"], default="detailed", help="Render mode for each run")
    args = ap.parse_args()

    from orchestrator import run

    results = []
    total_times = []
    slowest_per_run = []

    for text in BENCHMARK_INPUTS:
        pipeline = run(text, render_mode=args.render, profile=True)
        pf = pipeline.get("profiling") or {}
        total_ms = pf.get("total_time_ms") or 0
        slowest_id = pf.get("slowest_stage_id") or ""
        slowest_ms = pf.get("slowest_stage_time_ms") or 0
        total_times.append(total_ms)
        slowest_per_run.append((slowest_id, slowest_ms))
        results.append({
            "input": text[:40] + ("…" if len(text) > 40 else ""),
            "total_time_ms": total_ms,
            "slowest_stage_id": slowest_id,
            "slowest_stage_time_ms": slowest_ms,
        })

    # Summary
    n = len(total_times)
    avg_total = sum(total_times) / n if n else 0
    min_total = min(total_times) if total_times else 0
    max_total = max(total_times) if total_times else 0

    # Aggregate slowest stage frequency
    slowest_counts: dict[str, int] = {}
    for sid, _ in slowest_per_run:
        slowest_counts[sid] = slowest_counts.get(sid, 0) + 1

    print("=== Orchestrator profiling report ===")
    print(f"Inputs: {n}")
    print(f"Average total time: {avg_total:.2f} ms")
    print(f"Min total time: {min_total:.2f} ms")
    print(f"Max total time: {max_total:.2f} ms")
    print("\nSlowest stage per run:")
    for (text, r) in zip(BENCHMARK_INPUTS, results):
        print(f"  {text[:30]!r}: {r['slowest_stage_id']} ({r['slowest_stage_time_ms']} ms)")
    print("\nAggregate slowest stage frequency:")
    for sid, count in sorted(slowest_counts.items(), key=lambda x: -x[1]):
        print(f"  {sid}: {count}")

    report = {
        "inputs_count": n,
        "average_total_time_ms": round(avg_total, 2),
        "min_total_time_ms": min_total,
        "max_total_time_ms": max_total,
        "per_run": results,
        "slowest_stage_frequency": slowest_counts,
    }

    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        print(f"\nWrote JSON report to {args.json}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
