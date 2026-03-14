# -*- coding: utf-8 -*-
"""
Stage 11 — Performance profiling for the orchestrator pipeline.

Collects per-stage elapsed time and builds a top-level profiling summary.
No analyzer logic; measurement only.
"""

from __future__ import annotations

from typing import Any, Dict, List

from .types import STAGE_ORDER


def build_profiling_summary(
    per_stage_records: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """
    Build top-level profiling summary from per-stage records.
    Each record: layer_id, elapsed_ms, status, warnings_count, errors_count.
    """
    per_stage: Dict[str, Dict[str, Any]] = {}
    total_time_ms = 0.0
    stages_run_count = 0
    stages_skipped_count = 0
    slowest_stage_id: str | None = None
    slowest_stage_time_ms: float = 0.0

    for r in per_stage_records:
        layer_id = r.get("layer_id") or ""
        elapsed = float(r.get("elapsed_ms") or 0.0)
        status = r.get("status") or "missing"
        per_stage[layer_id] = {
            "elapsed_ms": round(elapsed, 2),
            "status": status,
            "warnings_count": r.get("warnings_count", 0),
            "errors_count": r.get("errors_count", 0),
        }
        total_time_ms += elapsed
        if status == "skipped":
            stages_skipped_count += 1
        else:
            stages_run_count += 1
        if elapsed > slowest_stage_time_ms:
            slowest_stage_time_ms = elapsed
            slowest_stage_id = layer_id

    # Ensure all stage IDs have an entry (fill missing with 0)
    for sid in STAGE_ORDER:
        if sid not in per_stage:
            per_stage[sid] = {
                "elapsed_ms": 0.0,
                "status": "missing",
                "warnings_count": 0,
                "errors_count": 0,
            }

    return {
        "total_time_ms": round(total_time_ms, 2),
        "stage_count": len(STAGE_ORDER),
        "stages_run_count": stages_run_count,
        "stages_skipped_count": stages_skipped_count,
        "slowest_stage_id": slowest_stage_id,
        "slowest_stage_time_ms": round(slowest_stage_time_ms, 2),
        "per_stage": per_stage,
    }
