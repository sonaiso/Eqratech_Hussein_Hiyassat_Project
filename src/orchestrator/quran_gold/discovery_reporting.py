# -*- coding: utf-8 -*-
"""
Discovery-only reporting (Batch 28.7): buckets, per-row/ayah CSVs, trapped strict rows, ranking.

Does not change comparator acceptance; classification is for visibility only.
"""

from __future__ import annotations

import csv
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from orchestrator.quran_gold.comparator import ComparatorTier

STRICT_TIERS = frozenset(
    {
        ComparatorTier.EXACT_TEXT_MATCH.value,
        ComparatorTier.STRICT_STRUCTURAL_MATCH.value,
    }
)


def classify_discovery_bucket(truth: Dict[str, Any]) -> str:
    """Map truth_audit row to Batch 28.7 discovery bucket."""
    ab = (truth.get("audit_bucket") or "").strip()
    tier = (truth.get("comparator_tier_current") or "").strip()
    pu = truth.get("potentially_unlockable_without_l17_core") == "true"
    blocker = (truth.get("acceptance_blocker") or "").strip()

    if ab == "ALIGNMENT_FAILED":
        return "blocked_by_alignment_or_segmentation"

    if ab in ("ALREADY_SATISFIED_ERQA", "ACCEPTED_STRICT_TIER") or tier in STRICT_TIERS:
        return "already_strictly_acceptable_now"

    if ab == "GOLD_PARSED_STRUCTURE_TOO_WEAK":
        return "blocked_by_gold_prose_compression"

    if ab == "GOLD_LONG_PROSE_L11_CONFLICT":
        return "blocked_by_true_gold_system_conflict"

    if ab == "GOLD_LONG_PROSE_L17_UNAVAILABLE" and blocker == "l17_unresolved" and not pu:
        return "blocked_by_l17_or_core_analysis"

    if pu and ab not in ("ALREADY_SATISFIED_ERQA", "ACCEPTED_STRICT_TIER"):
        return "likely_unlockable_with_tooling_only"

    if ab in (
        "L11_EXACT_TEXT_POSSIBLE_BUT_NORMALIZATION_BLOCKED",
        "L11_STRONG_STRUCTURAL_MATCH_POSSIBLE",
        "L17_STRONG_STRUCTURAL_MATCH_POSSIBLE",
    ):
        return "likely_unlockable_with_tooling_only"

    if ab == "ANALYZER_EMPTY_OR_LOW_SIGNAL":
        return "blocked_by_l17_or_core_analysis"

    return "needs_manual_review"


def recommended_next_action_for_row(bucket: str, truth: Dict[str, Any]) -> str:
    if bucket == "already_strictly_acceptable_now":
        return "PASS_NOW"
    if bucket == "likely_unlockable_with_tooling_only":
        return "TOOLING_ONLY_NEXT"
    if bucket == "blocked_by_l17_or_core_analysis":
        return "NEEDS_CORE_ANALYSIS"
    if bucket == "blocked_by_true_gold_system_conflict":
        return "TRUE_CONFLICT_REVIEW"
    if bucket == "blocked_by_alignment_or_segmentation":
        return "MANUAL_REVIEW"
    if bucket == "blocked_by_gold_prose_compression":
        return "TOOLING_ONLY_NEXT"
    return "MANUAL_REVIEW"


def row_level_discovery_record(
    *,
    row_index: int,
    truth: Dict[str, Any],
    structured: Optional[Dict[str, Any]],
    alignment_status: str,
) -> Dict[str, Any]:
    bucket = classify_discovery_bucket(truth)
    tier = (truth.get("comparator_tier_current") or "")
    if structured and not tier:
        tier = (structured.get("comparator_tier") or "")
    pu = truth.get("potentially_unlockable_without_l17_core") == "true"
    ab = truth.get("audit_bucket", "")
    requires_l17 = ab == "GOLD_LONG_PROSE_L17_UNAVAILABLE" and not pu
    requires_manual = bucket == "needs_manual_review" or bucket == "blocked_by_true_gold_system_conflict"

    evidence = f"audit_bucket={ab};blocker={truth.get('acceptance_blocker','')};best_tier={truth.get('best_possible_safe_tier','')}"

    return {
        "row_index": row_index,
        "surah": truth.get("surah", ""),
        "ayah": truth.get("ayah", ""),
        "word": truth.get("word", ""),
        "gold_i3rab": truth.get("gold_i3rab", ""),
        "current_system_i3rab": truth.get("l11_i3rab", ""),
        "current_match_tier": tier,
        "alignment_status": alignment_status,
        "discovery_bucket": bucket,
        "likely_unlockable_without_l17_core": str(pu).lower(),
        "likely_unlockable_without_pipeline_changes": str(
            bucket == "likely_unlockable_with_tooling_only"
        ).lower(),
        "requires_l17_core": str(requires_l17).lower(),
        "requires_manual_review": str(requires_manual).lower(),
        "evidence_summary": evidence[:500],
        "blocking_reason": truth.get("acceptance_blocker", "") or ab,
        "recommended_next_action": recommended_next_action_for_row(bucket, truth),
    }


def _alignment_status_for_row(
    truth: Dict[str, Any],
    align_by_gi: Dict[int, Dict[str, Any]],
    gi: int,
) -> str:
    if truth.get("audit_bucket") == "ALIGNMENT_FAILED":
        r = align_by_gi.get(gi) or {}
        return (r.get("alignment_status") or "skipped_alignment").strip() or "alignment_failed"
    return "aligned"


def build_discovery_rows_for_ayah(
    surah: int,
    ayah: int,
    truth_rows: List[Dict[str, Any]],
    structured_rows: List[Dict[str, Any]],
    alignment_rows: List[Dict[str, Any]],
    gi_by_word_index: Dict[int, int],
) -> List[Dict[str, Any]]:
    struct_by_wi = {int(s.get("ayah_word_index", -1)): s for s in structured_rows if str(s.get("ayah_word_index", "")).isdigit()}
    align_by_gi = {}
    for a in alignment_rows:
        try:
            gix = int(a.get("row_index", -1))
        except (TypeError, ValueError):
            continue
        align_by_gi[gix] = a

    out: List[Dict[str, Any]] = []
    for truth in truth_rows:
        if int(truth.get("surah", -1)) != surah or int(truth.get("ayah", -1)) != ayah:
            continue
        wi = int(truth.get("ayah_word_index", -1))
        gi = gi_by_word_index.get(wi, -1)
        st = struct_by_wi.get(wi)
        al = _alignment_status_for_row(truth, align_by_gi, gi)
        out.append(
            row_level_discovery_record(
                row_index=gi,
                truth=truth,
                structured=st,
                alignment_status=al,
            )
        )
    return out


def per_ayah_discovery_summary(
    surah: int,
    ayah: int,
    truth_rows: List[Dict[str, Any]],
    ayah_decision: Any,
) -> Dict[str, Any]:
    buckets = [classify_discovery_bucket(t) for t in truth_rows]
    total = len(truth_rows)
    strict_now = sum(1 for b in buckets if b == "already_strictly_acceptable_now")
    tooling = sum(1 for b in buckets if b == "likely_unlockable_with_tooling_only")
    core = sum(1 for b in buckets if b == "blocked_by_l17_or_core_analysis")
    conflict = sum(1 for b in buckets if b == "blocked_by_true_gold_system_conflict")
    prose = sum(1 for b in buckets if b == "blocked_by_gold_prose_compression")
    align_b = sum(1 for b in buckets if b == "blocked_by_alignment_or_segmentation")
    pass_strict = str(ayah_decision) == "PASS_STRICT"
    likely_after_tooling = (not pass_strict) and tooling > 0 and (tooling + strict_now) >= total - align_b

    if pass_strict:
        action = "PASS_NOW"
    elif likely_after_tooling and conflict == 0:
        action = "TOOLING_ONLY_NEXT"
    elif core > conflict and core > 0:
        action = "NEEDS_CORE_ANALYSIS"
    elif conflict > 0:
        action = "TRUE_CONFLICT_REVIEW"
    elif align_b > total // 2:
        action = "MANUAL_REVIEW"
    else:
        action = "MANUAL_REVIEW"

    return {
        "surah": surah,
        "ayah": ayah,
        "total_rows": total,
        "strict_acceptable_rows_now": strict_now,
        "tooling_unlockable_rows": tooling,
        "core_blocked_rows": core,
        "true_conflict_rows": conflict,
        "gold_prose_blocked_rows": prose,
        "alignment_blocked_rows": align_b,
        "pass_strict_now": str(pass_strict).lower(),
        "likely_pass_strict_after_tooling_only": str(likely_after_tooling).lower(),
        "recommended_action": action,
    }


def collect_trapped_strict_rows(
    surah: int,
    ayah: int,
    ayah_decision: Any,
    structured_rows: List[Dict[str, Any]],
    reason: str,
    wi_to_gi: Dict[int, int],
) -> List[Dict[str, Any]]:
    """Rows with strict comparator tier while whole ayah is not PASS_STRICT."""
    if str(ayah_decision) == "PASS_STRICT":
        return []
    strict_like = [
        s
        for s in structured_rows
        if (s.get("comparator_tier") or "") in STRICT_TIERS
        and (s.get("strict_acceptance_eligible", "").lower() == "true")
    ]
    n_strict = sum(
        1
        for s in structured_rows
        if (s.get("comparator_tier") or "") in STRICT_TIERS
    )
    total = len(structured_rows)
    out: List[Dict[str, Any]] = []
    for s in strict_like:
        try:
            wi = int(s.get("ayah_word_index", -1))
        except (TypeError, ValueError):
            wi = -1
        gri = wi_to_gi.get(wi, "")
        out.append(
            {
                "surah": surah,
                "ayah": ayah,
                "word": s.get("word", ""),
                "row_index": str(gri),
                "strict_tier": s.get("comparator_tier", ""),
                "ayah_failure_reason": reason,
                "ayah_strict_row_count": str(n_strict),
                "ayah_total_rows": str(total),
                "recommended_action": "TOOLING_ONLY_NEXT" if n_strict == total else "MANUAL_REVIEW",
            }
        )
    return out


def unlock_score_and_recommendation(row: Dict[str, Any]) -> Tuple[float, str]:
    ts = int(row.get("strict_rows_now") or 0)
    tu = int(row.get("tooling_unlockable_rows") or 0)
    cf = int(row.get("true_conflict_rows") or 0)
    al = int(row.get("alignment_blocked_rows") or 0)
    score = ts * 1000.0 + tu * 100.0 - cf * 50.0 - al * 20.0
    rec = row.get("recommended_action", "MANUAL_REVIEW")
    return score, str(rec)


def rank_unlockable_ayahs(ayah_summaries: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    enriched: List[Dict[str, Any]] = []
    for r in ayah_summaries:
        strict_now = int(r.get("strict_acceptable_rows_now") or 0)
        tooling = int(r.get("tooling_unlockable_rows") or 0)
        core = int(r.get("core_blocked_rows") or 0)
        cf = int(r.get("true_conflict_rows") or 0)
        al = int(r.get("alignment_blocked_rows") or 0)
        total = int(r.get("total_rows") or 0)
        score, rec = unlock_score_and_recommendation(
            {
                "strict_rows_now": strict_now,
                "tooling_unlockable_rows": tooling,
                "true_conflict_rows": cf,
                "alignment_blocked_rows": al,
                "recommended_action": r.get("recommended_action"),
            }
        )
        enriched.append(
            {
                "surah": r["surah"],
                "ayah": r["ayah"],
                "total_rows": total,
                "strict_rows_now": strict_now,
                "tooling_unlockable_rows": tooling,
                "core_blocked_rows": core,
                "true_conflict_rows": cf,
                "alignment_blocked_rows": al,
                "unlock_score": f"{score:.2f}",
                "recommendation": rec,
            }
        )
    enriched.sort(key=lambda x: (-float(x["unlock_score"]), int(x["surah"]), int(x["ayah"])))
    return enriched


DISCOVERY_ROW_FIELDS = (
    "row_index",
    "surah",
    "ayah",
    "word",
    "gold_i3rab",
    "current_system_i3rab",
    "current_match_tier",
    "alignment_status",
    "discovery_bucket",
    "likely_unlockable_without_l17_core",
    "likely_unlockable_without_pipeline_changes",
    "requires_l17_core",
    "requires_manual_review",
    "evidence_summary",
    "blocking_reason",
    "recommended_next_action",
)

DISCOVERY_AYAH_SUMMARY_FIELDS = (
    "surah",
    "ayah",
    "total_rows",
    "strict_acceptable_rows_now",
    "tooling_unlockable_rows",
    "core_blocked_rows",
    "true_conflict_rows",
    "gold_prose_blocked_rows",
    "alignment_blocked_rows",
    "pass_strict_now",
    "likely_pass_strict_after_tooling_only",
    "recommended_action",
)

DISCOVERY_RANKED_UNLOCKABLE_FIELDS = (
    "surah",
    "ayah",
    "total_rows",
    "strict_rows_now",
    "tooling_unlockable_rows",
    "core_blocked_rows",
    "true_conflict_rows",
    "alignment_blocked_rows",
    "unlock_score",
    "recommendation",
)

TRAPPED_STRICT_FIELDS = (
    "surah",
    "ayah",
    "word",
    "row_index",
    "strict_tier",
    "ayah_failure_reason",
    "ayah_strict_row_count",
    "ayah_total_rows",
    "recommended_action",
)


def _write_csv(path: Path, fields: Sequence[str], rows: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fields))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fields})


def write_discovery_rows_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    _write_csv(Path(path), DISCOVERY_ROW_FIELDS, rows)


def write_discovery_ayah_summary_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    _write_csv(Path(path), DISCOVERY_AYAH_SUMMARY_FIELDS, rows)


def write_discovery_ranked_unlockable_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    _write_csv(Path(path), DISCOVERY_RANKED_UNLOCKABLE_FIELDS, rows)


def write_trapped_strict_rows_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    _write_csv(Path(path), TRAPPED_STRICT_FIELDS, rows)


def aggregate_discovery_counts(all_discovery_rows: List[Dict[str, Any]]) -> Dict[str, int]:
    """Roll-up for summary JSON."""
    out = {
        "tooling_unlockable_rows": 0,
        "core_blocked_rows": 0,
        "true_conflict_rows": 0,
        "trapped_strict_rows": 0,
    }
    for r in all_discovery_rows:
        b = r.get("discovery_bucket", "")
        if b == "likely_unlockable_with_tooling_only":
            out["tooling_unlockable_rows"] += 1
        if b == "blocked_by_l17_or_core_analysis":
            out["core_blocked_rows"] += 1
        if b == "blocked_by_true_gold_system_conflict":
            out["true_conflict_rows"] += 1
    return out
