#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Append timestamped entries to the project memory documents.

Usage:
  python3 scripts/update_architecture_log.py --target architecture --components "L10B,L11B" --intent "passive-aware tightening" --risk medium
  python3 scripts/update_architecture_log.py --target research --components "L8B" --intent "valency seed integration" --risk low

Updates:
  - architecture -> docs/architecture/PIPELINE_MASTER_MEMORY.md (Change Log)
  - research     -> docs/research/FVAFK_MASTER_EVOLUTION.md (Engine Evolution Log)
"""

from __future__ import annotations

import argparse
import os
from datetime import datetime, timezone

# Project root: script lives in scripts/
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ARCH_PATH = os.path.join(ROOT, "docs", "architecture", "PIPELINE_MASTER_MEMORY.md")
RESEARCH_PATH = os.path.join(ROOT, "docs", "research", "FVAFK_MASTER_EVOLUTION.md")


def append_architecture_entry(components: str, intent: str, risk: str) -> None:
    path = ARCH_PATH
    if not os.path.isfile(path):
        raise FileNotFoundError(f"Architecture memory not found: {path}")
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    line = f"| {ts} | {components} | {intent} (risk: {risk}) |\n"
    # Insert before the last "---" + "End of PIPELINE_MASTER_MEMORY"
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    marker = "\n---\n\n*End of PIPELINE_MASTER_MEMORY*"
    if marker not in content:
        # Fallback: append before last line
        content = content.rstrip() + "\n" + line
    else:
        content = content.replace(marker, "\n" + line + marker)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"Appended to {path}")


def append_research_entry(components: str, intent: str, risk: str) -> None:
    path = RESEARCH_PATH
    if not os.path.isfile(path):
        raise FileNotFoundError(f"Research evolution doc not found: {path}")
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    # Table columns: Date | Change | Notes
    line = f"| {ts} | {intent} (risk: {risk}) | {components} |\n"
    # Insert new row after the evolution log table, before "## AUTO-UPDATE RULE"
    marker = "\n\n---\n\n## AUTO-UPDATE RULE"
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    if marker not in content:
        content = content.rstrip() + "\n" + line
    else:
        content = content.replace(marker, "\n" + line + marker)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"Appended to {path}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Append timestamped entry to architecture/research memory.")
    parser.add_argument("--target", required=True, choices=["architecture", "research"], help="Target document")
    parser.add_argument("--components", required=True, help="Modified components (e.g. L10B,L11B)")
    parser.add_argument("--intent", required=True, help="Scientific intention / change description")
    parser.add_argument("--risk", default="medium", choices=["low", "medium", "high"], help="Risk level")
    args = parser.parse_args()
    if args.target == "architecture":
        append_architecture_entry(args.components, args.intent, args.risk)
    else:
        append_research_entry(args.components, args.intent, args.risk)


if __name__ == "__main__":
    main()
