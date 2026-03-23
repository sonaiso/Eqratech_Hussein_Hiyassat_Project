# -*- coding: utf-8 -*-
"""
PASS_STRICT discovery and isolated bounded writes (Batch 28.6). Tooling only.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from orchestrator.quran_gold.ayah_batch_runner import AyahBatchResult, AyahDecision
from orchestrator.quran_gold.truth_audit import aggregate_batch_28_5_counters

PASS_STRICT_CANDIDATE_FIELDS = (
    "surah",
    "ayah",
    "decision_status",
    "accepted_row_count",
    "wrong_row_count",
    "alignment_coverage",
    "strict_tier_count",
    "exact_tier_count",
    "rows_blocked_by_l17_core",
    "rows_blocked_by_true_conflict",
    "rows_unlockable_now",
    "reason_summary",
)


def discovery_row_from_result(ar: AyahBatchResult, surah: int, ayah: int) -> Dict[str, Any]:
    tiers = [r.get("comparator_tier", "") for r in ar.structured_debug_rows]
    strict_n = sum(1 for t in tiers if t == "strict_structural_match")
    exact_n = sum(1 for t in tiers if t == "exact_text_match")
    rt = ar.rows_total or 1
    align_cov = (rt - ar.rows_skipped_alignment) / rt
    b = aggregate_batch_28_5_counters(ar.truth_audit_rows)
    return {
        "surah": surah,
        "ayah": ayah,
        "decision_status": ar.decision.value,
        "accepted_row_count": len(ar.new_erqa_payloads),
        "wrong_row_count": len(ar.wrong_payloads),
        "alignment_coverage": round(align_cov, 4),
        "strict_tier_count": strict_n,
        "exact_tier_count": exact_n,
        "rows_blocked_by_l17_core": b["rows_blocked_by_l17_core"],
        "rows_blocked_by_true_conflict": b["rows_blocked_by_true_conflict"],
        "rows_unlockable_now": b["rows_unlockable_now"],
        "reason_summary": (ar.reason or "")[:500],
    }


def write_pass_strict_candidates_csv(path: Path, rows: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(PASS_STRICT_CANDIDATE_FIELDS))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in PASS_STRICT_CANDIDATE_FIELDS})


def load_candidates_csv_as_dict(path: Path) -> Dict[Tuple[int, int], Dict[str, Any]]:
    """Load candidate CSV into a map by (surah, ayah). Missing file → {}."""
    if not path.is_file():
        return {}
    out: Dict[Tuple[int, int], Dict[str, Any]] = {}
    with open(path, encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            try:
                k = (int((row.get("surah") or "").strip()), int((row.get("ayah") or "").strip()))
            except ValueError:
                continue
            out[k] = dict(row)
    return out


def load_pass_strict_ayah_keys(path: Path) -> List[Tuple[int, int]]:
    """Load (surah, ayah) where decision_status == PASS_STRICT."""
    if not path.is_file():
        return []
    out: List[Tuple[int, int]] = []
    with open(path, encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            if (row.get("decision_status") or "").strip() != AyahDecision.PASS_STRICT.value:
                continue
            try:
                s = int((row.get("surah") or "").strip())
                a = int((row.get("ayah") or "").strip())
            except ValueError:
                continue
            out.append((s, a))
    out.sort(key=lambda t: (t[0], t[1]))
    return out


def build_discovery_summary(
    candidate_rows: List[Dict[str, Any]],
    *,
    ayahs_scanned: int,
    first_10_pass_strict: List[Tuple[int, int]],
    first_10_unlockable: List[Tuple[int, int]],
    top_l17: List[Dict[str, Any]],
    top_conflict: List[Dict[str, Any]],
) -> Dict[str, Any]:
    def _count(st: str) -> int:
        return sum(1 for r in candidate_rows if r.get("decision_status") == st)

    return {
        "ayahs_scanned": ayahs_scanned,
        "pass_strict_ayahs": _count(AyahDecision.PASS_STRICT.value),
        "fail_alignment_ayahs": _count(AyahDecision.FAIL_ALIGNMENT.value),
        "fail_comparator_ayahs": _count(AyahDecision.FAIL_COMPARATOR.value),
        "fail_analysis_ayahs": _count(AyahDecision.FAIL_ANALYSIS.value),
        "review_needed_ayahs": _count(AyahDecision.REVIEW_NEEDED.value),
        "first_10_pass_strict_ayahs": [{"surah": s, "ayah": a} for s, a in first_10_pass_strict],
        "first_10_unlockable_ayahs": [{"surah": s, "ayah": a} for s, a in first_10_unlockable],
        "top_10_blocked_by_l17_core": top_l17,
        "top_10_blocked_by_true_conflict": top_conflict,
    }


def write_json(path: Path, obj: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)


def read_json(path: Path) -> Dict[str, Any]:
    if not path.is_file():
        return {}
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def ensure_fresh_batch_dir(batch_dir: Path) -> None:
    if batch_dir.exists():
        if any(batch_dir.iterdir()):
            raise FileExistsError(f"Batch directory not empty: {batch_dir}")


REVIEW_SAMPLE_FIELDS = (
    "surah",
    "ayah",
    "word",
    "gold_i3rab",
    "system_i3rab",
    "decision_tier",
    "decision_status",
    "analyzer_source",
    "notes",
)


def rank_ayahs_by_metric(
    candidate_rows: List[Dict[str, Any]], field: str, limit: int = 10
) -> List[Dict[str, Any]]:
    rows = [r for r in candidate_rows if int(r.get(field) or 0) > 0]
    rows.sort(key=lambda r: -int(r.get(field) or 0))
    out: List[Dict[str, Any]] = []
    seen: set[Tuple[int, int]] = set()
    for r in rows:
        try:
            k = (int(r["surah"]), int(r["ayah"]))
        except (KeyError, ValueError):
            continue
        if k in seen:
            continue
        seen.add(k)
        out.append({"surah": k[0], "ayah": k[1], field: int(r.get(field) or 0)})
        if len(out) >= limit:
            break
    return out


def write_review_sample_csv(
    path: Path,
    accepted_rows: List[Dict[str, Any]],
    rejected_sample: List[Dict[str, Any]],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rows: List[Dict[str, Any]] = []
    for er in accepted_rows:
        rows.append(
            {
                "surah": er.get("surah", ""),
                "ayah": er.get("ayah", ""),
                "word": er.get("word", ""),
                "gold_i3rab": er.get("gold_i3rab", ""),
                "system_i3rab": er.get("system_i3rab", ""),
                "decision_tier": er.get("match_type", ""),
                "decision_status": "PASS_STRICT",
                "analyzer_source": er.get("analyzer_source", ""),
                "notes": er.get("notes", ""),
            }
        )
    for w in rejected_sample:
        rows.append(
            {
                "surah": w.get("surah", ""),
                "ayah": w.get("ayah", ""),
                "word": w.get("word", ""),
                "gold_i3rab": w.get("gold_i3rab", ""),
                "system_i3rab": w.get("system_i3rab", ""),
                "decision_tier": w.get("notes", ""),
                "decision_status": "rejected_sample",
                "analyzer_source": w.get("analyzer_source", ""),
                "notes": w.get("mismatch_reason", ""),
            }
        )
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        wr = csv.DictWriter(f, fieldnames=list(REVIEW_SAMPLE_FIELDS))
        wr.writeheader()
        for r in rows:
            wr.writerow({k: r.get(k, "") for k in REVIEW_SAMPLE_FIELDS})
