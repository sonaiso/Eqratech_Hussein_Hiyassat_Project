# -*- coding: utf-8 -*-
"""Batch 28.11 — summary JSON + before/after baseline (ayah completion targeting)."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

# Pre-28.11 reference (--limit 200, gold_csv) after Batch 28.10
BATCH_28_11_BASELINE_LIMIT200: Dict[str, Any] = {
    "pass_strict_ayahs": 1,
    "near_pass_1_count": 2,
    "near_pass_2_count": 2,
    "candidate_real_accept_rows": 29,
    "rows_blocked_by_l17_core": 33,
    "alignment_coverage": 1.0,
}

# Ayah unlock labels before 28.11 (from Batch 28.9 CSV snapshot, first surahs)
BATCH_28_11_BASELINE_AYAH_STATUS: Dict[str, str] = {
    "1:1": "NEAR_PASS_1",
    "1:2": "NEAR_PASS_2",
    "1:3": "PASS_STRICT",
    "1:4": "NEAR_PASS_2",
    "2:1": "NEAR_PASS_1",
}


def build_batch_28_11_summary(
    *,
    batch_28_5: Dict[str, Any],
    batch_28_9: Optional[Dict[str, Any]],
    pass_strict_ayahs: int,
    alignment_coverage: float,
    target_ayahs: List[Dict[str, Any]],
    promoted_ayah_rows: List[Dict[str, Any]],
    still_blocked_targets: List[Dict[str, Any]],
    baseline: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    base = baseline or BATCH_28_11_BASELINE_LIMIT200
    b9 = batch_28_9 or {}
    np1b = int(base.get("near_pass_1_count") or 0)
    np2b = int(base.get("near_pass_2_count") or 0)
    np1a = int(b9.get("near_pass_1_count") or 0)
    np2a = int(b9.get("near_pass_2_count") or 0)

    reasons_ctr: Dict[str, int] = {}
    for r in still_blocked_targets:
        k = (r.get("blocker_type") or "unknown").strip()
        reasons_ctr[k] = reasons_ctr.get(k, 0) + 1
    still_summary = [f"{k}:{v}" for k, v in sorted(reasons_ctr.items(), key=lambda x: -x[1])][:12]

    prom_rows = 0
    for p in promoted_ayah_rows:
        try:
            prom_rows += int(p.get("rows_promoted") or 0)
        except ValueError:
            prom_rows += 1

    return {
        "target_ayah_count": len(target_ayahs),
        "target_ayahs": [f'{t.get("surah")}:{t.get("ayah")}' for t in target_ayahs],
        "near_pass_1_count_before": np1b,
        "near_pass_1_count_after": np1a,
        "near_pass_2_count_before": np2b,
        "near_pass_2_count_after": np2a,
        "pass_strict_ayahs_before": int(base.get("pass_strict_ayahs") or 0),
        "pass_strict_ayahs_after": pass_strict_ayahs,
        "candidate_real_accept_rows_before": int(base.get("candidate_real_accept_rows") or 0),
        "candidate_real_accept_rows_after": int(batch_28_5.get("candidate_real_accept_rows") or 0),
        "rows_blocked_by_l17_core_before": int(base.get("rows_blocked_by_l17_core") or 0),
        "rows_blocked_by_l17_core_after": int(batch_28_5.get("rows_blocked_by_l17_core") or 0),
        "alignment_coverage_before": float(base.get("alignment_coverage") or 1.0),
        "alignment_coverage_after": round(float(alignment_coverage), 4),
        "promoted_ayahs_count": len(promoted_ayah_rows),
        "promoted_rows_inside_promoted_ayahs": prom_rows,
        "still_blocked_target_ayahs_count": len(still_blocked_targets),
        "still_blocked_reasons_summary": still_summary,
    }


def write_before_after_json(repo_root: Path, summary: Dict[str, Any]) -> None:
    p = repo_root / "data" / "quran_i3rab_batch_28_11_before_after.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        json.dumps(
            {"batch": "28.11", "baseline_key": "BATCH_28_11_BASELINE_LIMIT200", "summary": summary},
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )
