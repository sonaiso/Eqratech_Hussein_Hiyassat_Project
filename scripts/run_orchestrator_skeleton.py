#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Run the Stage 3 orchestrator skeleton on raw text.

Usage:
  PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py "إِنَّ اللَّهَ غَفُورٌ"
  PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --json "إِنَّ اللَّهَ غَفُورٌ"
"""

from __future__ import annotations

import argparse
import json
import sys

def main() -> int:
    ap = argparse.ArgumentParser(description="Run pipeline orchestrator skeleton (Stage 3)")
    ap.add_argument("text", nargs="?", default="", help="Raw Arabic text to process")
    ap.add_argument("--json", action="store_true", help="Output full pipeline as JSON")
    ap.add_argument("--summary", action="store_true", help="Output only layer status summary")
    args = ap.parse_args()
    text = (args.text or "").strip()
    if not text and not sys.stdin.isatty():
        text = sys.stdin.read().strip()
    if not text:
        ap.error("Provide text as argument, e.g. scripts/run_orchestrator_skeleton.py 'إِنَّ اللَّهَ غَفُورٌ'")
        return 1

    # Import here so PYTHONPATH=src is enough
    from orchestrator import run
    from orchestrator.validation import validate_pipeline_shape

    pipeline = run(text, source={"entrypoint": "run_orchestrator_skeleton"})
    ok, issues = validate_pipeline_shape(pipeline)
    if not ok:
        print("Validation issues:", issues, file=sys.stderr)

    if args.json:
        # Full pipeline (layer_outputs can be large)
        print(json.dumps(pipeline, indent=2, ensure_ascii=False))
    elif args.summary:
        summary = {
            "request_id": pipeline.get("request_id"),
            "original_text": pipeline.get("original_text", "")[:80],
            "layer_status": {k: v.get("status") for k, v in (pipeline.get("layer_outputs") or {}).items()},
        }
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print("request_id:", pipeline.get("request_id"))
        print("original_text:", (pipeline.get("original_text") or "")[:60], "...")
        print("layer_outputs:", list((pipeline.get("layer_outputs") or {}).keys()))
        for sid, lo in (pipeline.get("layer_outputs") or {}).items():
            print(f"  {sid}: {lo.get('status')}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
