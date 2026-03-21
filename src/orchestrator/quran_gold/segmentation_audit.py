# -*- coding: utf-8 -*-
"""
Ayah-level segmentation audit for Quran iʿrāb gold vs pipeline comparison.

Writes diagnostic CSVs only — does not change orchestrator behavior.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple

from orchestrator.quran_gold.alignment import normalize_arabic_surface, strip_match_noise


@dataclass
class AyahAuditRow:
    surah: int
    ayah: int
    gold_row_count: int
    pipeline_token_count: int
    aligned_count: int
    missing_count: int
    ambiguous_count: int
    token_counts_differ: bool
    order_drift: bool
    reason_summary: str


def write_ayah_audit_csv(path: str, rows: Sequence[AyahAuditRow]) -> None:
    fn = (
        "surah",
        "ayah",
        "gold_row_count",
        "pipeline_token_count",
        "aligned_count",
        "missing_count",
        "ambiguous_count",
        "token_counts_differ",
        "order_drift",
        "reason_summary",
    )
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fn))
        w.writeheader()
        for r in rows:
            w.writerow(
                {
                    "surah": r.surah,
                    "ayah": r.ayah,
                    "gold_row_count": r.gold_row_count,
                    "pipeline_token_count": r.pipeline_token_count,
                    "aligned_count": r.aligned_count,
                    "missing_count": r.missing_count,
                    "ambiguous_count": r.ambiguous_count,
                    "token_counts_differ": str(r.token_counts_differ).lower(),
                    "order_drift": str(r.order_drift).lower(),
                    "reason_summary": r.reason_summary,
                }
            )


def build_token_inventory_rows(
    surah: int,
    ayah: int,
    gold_words: Sequence[str],
    gold_global_indices: Sequence[Optional[int]],
    pipeline_tokens: Sequence[str],
) -> List[Dict[str, Any]]:
    """
    Side-by-side inventory: gold words and pipeline tokens with normalized surfaces.
    gold_global_indices: parallel to gold_words, global CSV row index or None.
    """
    rows: List[Dict[str, Any]] = []
    for i, gw in enumerate(gold_words):
        rows.append(
            {
                "surah": surah,
                "ayah": ayah,
                "source_type": "gold_word",
                "token_index": i,
                "surface": gw,
                "normalized_surface": strip_match_noise(gw),
                "row_index_if_gold": "" if i >= len(gold_global_indices) or gold_global_indices[i] is None else str(gold_global_indices[i]),
            }
        )
    for j, pt in enumerate(pipeline_tokens):
        rows.append(
            {
                "surah": surah,
                "ayah": ayah,
                "source_type": "pipeline_token",
                "token_index": j,
                "surface": pt,
                "normalized_surface": strip_match_noise(pt),
                "row_index_if_gold": "",
            }
        )
    return rows


def write_ayah_token_debug_csv(path: str, rows: Sequence[Dict[str, Any]]) -> None:
    fn = ("surah", "ayah", "source_type", "token_index", "surface", "normalized_surface", "row_index_if_gold")
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fn))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fn})


def summarize_ayah_reason(
    token_counts_differ: bool,
    order_drift: bool,
    missing_count: int,
    ambiguous_count: int,
) -> str:
    parts: List[str] = []
    if token_counts_differ:
        parts.append("token_count_mismatch")
    if order_drift:
        parts.append("order_drift")
    if missing_count:
        parts.append(f"missing={missing_count}")
    if ambiguous_count:
        parts.append(f"ambiguous={ambiguous_count}")
    return ";".join(parts) if parts else "ok"
