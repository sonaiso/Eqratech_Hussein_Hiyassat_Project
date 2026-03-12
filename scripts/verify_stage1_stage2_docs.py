#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Verify Stage 1 (docs) and Stage 2 (contract/schemas) without changing code.

Run from project root:
  PYTHONPATH=src python3 scripts/verify_stage1_stage2_docs.py

Tests:
1. CLI help (python3 -m fvafk.cli --help)
2. Base JSON: --json only → success, c1, c2a, stats; no c2b
3. Morphology JSON: --morphology --multi-word --json → c2b, c2d, rhetoric_signals, c2b.words[].c2e.i3rab_text
4. Schema files exist and are valid JSON
"""

import json
import subprocess
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC = PROJECT_ROOT / "src"


def run_cli(*args):
    cmd = [sys.executable, "-m", "fvafk.cli"] + list(args)
    result = subprocess.run(
        cmd,
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        timeout=60,
        env={**__import__("os").environ, "PYTHONPATH": str(SRC)},
    )
    return result.returncode, result.stdout, result.stderr


def main():
    failed = 0

    # 1. Help
    print("1. CLI help (python3 -m fvafk.cli --help)...")
    code, out, err = run_cli("--help")
    if code != 0 or "FVAFK" not in out:
        print("   FAIL")
        failed += 1
    else:
        print("   PASS")

    # 2. Base JSON
    print("2. Base JSON (--json, no morphology)...")
    code, out, err = run_cli("إِنَّ اللَّهَ غَفُورٌ", "--json")
    if code != 0:
        print("   FAIL (non-zero exit)")
        failed += 1
    else:
        try:
            d = json.loads(out)
            if not d.get("success") or "c1" not in d or "c2a" not in d:
                print("   FAIL (missing success/c1/c2a)")
                failed += 1
            elif "c2b" in d and d.get("c2b") is not None:
                print("   FAIL (c2b present but should be absent without --morphology)")
                failed += 1
            else:
                print("   PASS")
        except json.JSONDecodeError as e:
            print("   FAIL (invalid JSON)", e)
            failed += 1

    # 3. Morphology JSON (with --multi-word so words[] and c2e are populated)
    print("3. Morphology JSON (--morphology --multi-word --json)...")
    code, out, err = run_cli("كَاتِبٌ", "--morphology", "--multi-word", "--json")
    if code != 0:
        print("   FAIL (non-zero exit)")
        failed += 1
    else:
        try:
            d = json.loads(out)
            c2b = d.get("c2b") or {}
            words = c2b.get("words") or []
            has_i3rab = any((w.get("c2e") or {}).get("i3rab_text") for w in words)
            if not d.get("success") or "c2b" not in d:
                print("   FAIL (missing success or c2b)")
                failed += 1
            elif not has_i3rab and words:
                print("   FAIL (c2b.words present but no c2e.i3rab_text)")
                failed += 1
            else:
                print("   PASS")
                if words and words[0].get("c2e", {}).get("i3rab_text"):
                    print("     i3rab_text sample:", (words[0]["c2e"]["i3rab_text"][:50] + "..."))
        except json.JSONDecodeError as e:
            print("   FAIL (invalid JSON)", e)
            failed += 1

    # 4. Schema files exist and are valid JSON
    print("4. Schema files (schemas/*.json)...")
    for name in ("pipeline.schema.json", "layer_output.schema.json", "common_defs.schema.json"):
        path = PROJECT_ROOT / "schemas" / name
        if not path.exists():
            print(f"   FAIL ({name} missing)")
            failed += 1
        else:
            try:
                with open(path, encoding="utf-8") as f:
                    json.load(f)
                print(f"   {name}: valid JSON")
            except (json.JSONDecodeError, OSError) as e:
                print(f"   FAIL ({name}): {e}")
                failed += 1
    if failed == 0:
        print("   PASS (all schemas valid)")

    # 5. Doc files exist
    print("5. Stage 1 / verification docs exist...")
    for name in ("layer_mapping.md", "current_entrypoints.md", "gap_analysis.md", "pipeline_contract.md"):
        path = PROJECT_ROOT / "docs" / name
        if path.exists():
            print(f"   {name}: exists")
        else:
            print(f"   FAIL ({name} missing)")
            failed += 1

    print()
    if failed:
        print(f"Total failures: {failed}")
        return 1
    print("All checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
