# -*- coding: utf-8 -*-
"""
CSV / JSON sinks for Batch 28.3 quarantine policy (tooling only).
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence, Tuple

STRUCTURED_DEBUG_FIELDS = (
    "surah",
    "ayah",
    "word",
    "gold_i3rab_raw",
    "gold_family",
    "gold_role",
    "gold_case_bucket",
    "gold_marker",
    "l17_family",
    "l17_role",
    "l17_case_bucket",
    "l17_marker",
    "comparator_tier",
    "strict_acceptance_eligible",
    "reason",
    "parser_confidence",
    "parser_limitations",
    "ayah_word_index",
)


def write_structured_debug_csv(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(STRUCTURED_DEBUG_FIELDS))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in STRUCTURED_DEBUG_FIELDS})


REPAIR_LOG_FIELDS = (
    "timestamp",
    "surah",
    "ayah",
    "row_index",
    "word",
    "issue_type",
    "attempt_no",
    "action_taken",
    "result_status",
    "notes",
)

AYAH_REVIEW_FIELDS = (
    "surah",
    "ayah",
    "status",
    "reason",
    "rows_total",
    "rows_accepted",
    "rows_rejected",
    "rows_skipped_alignment",
    "repair_attempts",
    "last_action",
)


def append_repair_log(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    exists = path.is_file() and path.stat().st_size > 0
    with open(path, "a", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(REPAIR_LOG_FIELDS))
        if not exists:
            w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in REPAIR_LOG_FIELDS})


def upsert_ayah_review_queue(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    """Merge by (surah, ayah): replace existing row with same key."""
    path.parent.mkdir(parents=True, exist_ok=True)
    existing: Dict[Tuple[int, int], Dict[str, Any]] = {}
    if path.is_file() and path.stat().st_size > 0:
        with open(path, encoding="utf-8-sig") as f:
            for r in csv.DictReader(f):
                try:
                    k = (int(r["surah"]), int(r["ayah"]))
                    existing[k] = dict(r)
                except (KeyError, ValueError):
                    continue
    for r in rows:
        k = (int(r["surah"]), int(r["ayah"]))
        existing[k] = {fn: str(r.get(fn, "")) for fn in AYAH_REVIEW_FIELDS}
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(AYAH_REVIEW_FIELDS))
        w.writeheader()
        for k in sorted(existing.keys()):
            w.writerow(existing[k])


def write_progress_state(path: Path, state: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(dict(state), ensure_ascii=False, indent=2), encoding="utf-8")


def write_batch_summary(path: Path, summary: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(dict(summary), ensure_ascii=False, indent=2), encoding="utf-8")


def load_progress_state(path: Path) -> Dict[str, Any]:
    if not path.is_file():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def git_head_short() -> str:
    import subprocess

    try:
        p = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()[:40]
    except OSError:
        pass
    return ""
