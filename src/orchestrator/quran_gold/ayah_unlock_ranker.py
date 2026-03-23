# -*- coding: utf-8 -*-
"""
Batch 28.9 — ayah-level unlock classification and reporting (diagnostic only).

Does not change comparator acceptance or PASS_STRICT policy.
"""

from __future__ import annotations

import csv
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from orchestrator.quran_gold.ayah_batch_runner import AyahDecision
from orchestrator.quran_gold.comparator import ComparatorTier

STRICT_TIERS = frozenset(
    {
        ComparatorTier.EXACT_TEXT_MATCH.value,
        ComparatorTier.STRICT_STRUCTURAL_MATCH.value,
    }
)

# User-facing ayah unlock labels (Batch 28.9)
AYAH_UNLOCK_PASS_STRICT = "PASS_STRICT"
AYAH_UNLOCK_NEAR_PASS_1 = "NEAR_PASS_1"
AYAH_UNLOCK_NEAR_PASS_2 = "NEAR_PASS_2"
AYAH_UNLOCK_CORE_BLOCKED = "CORE_BLOCKED"
AYAH_UNLOCK_ALIGNMENT_BLOCKED = "ALIGNMENT_BLOCKED"
AYAH_UNLOCK_TRUE_CONFLICT = "TRUE_CONFLICT"
AYAH_UNLOCK_REVIEW_NEEDED = "REVIEW_NEEDED"


def _row_strict_satisfied(truth: Dict[str, Any]) -> bool:
    ab = (truth.get("audit_bucket") or "").strip()
    return ab in ("ALREADY_SATISFIED_ERQA", "ACCEPTED_STRICT_TIER")


def _primary_blocker_kind(truth: Dict[str, Any]) -> str:
    ab = (truth.get("audit_bucket") or "").strip()
    if ab == "ALIGNMENT_FAILED":
        return "alignment_issue"
    if ab == "GOLD_LONG_PROSE_L11_CONFLICT":
        return "true_conflict"
    if ab in (
        "GOLD_LONG_PROSE_L17_UNAVAILABLE",
        "ANALYZER_EMPTY_OR_LOW_SIGNAL",
        "GOLD_PARSED_STRUCTURE_TOO_WEAK",
    ):
        return "requires_core"
    if ab in (
        "L11_EXACT_TEXT_POSSIBLE_BUT_NORMALIZATION_BLOCKED",
        "L11_STRONG_STRUCTURAL_MATCH_POSSIBLE",
        "L17_STRONG_STRUCTURAL_MATCH_POSSIBLE",
    ):
        return "quarantine_only"
    if truth.get("potentially_unlockable_without_l17_core") == "true":
        return "unlockable_now"
    return "other"


def _blocker_rows(truth_rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [t for t in truth_rows if not _row_strict_satisfied(t)]


def classify_ayah_unlock_status(
    decision: AyahDecision,
    truth_rows: Sequence[Dict[str, Any]],
) -> Tuple[str, str]:
    """
    Returns (ayah_unlock_label, would_ayah_pass_if_fixed_short).
    """
    if decision == AyahDecision.PASS_STRICT:
        return AYAH_UNLOCK_PASS_STRICT, "n_a_passed"

    if decision == AyahDecision.FAIL_ALIGNMENT:
        return AYAH_UNLOCK_ALIGNMENT_BLOCKED, "needs_alignment_fix"

    if decision == AyahDecision.FAIL_ANALYSIS:
        return AYAH_UNLOCK_REVIEW_NEEDED, "needs_analysis_pipeline"

    if decision == AyahDecision.REVIEW_NEEDED:
        return AYAH_UNLOCK_REVIEW_NEEDED, "internal_review"

    blockers = _blocker_rows(truth_rows)
    n = len(blockers)
    if n == 0:
        return AYAH_UNLOCK_REVIEW_NEEDED, "no_blocker_rows_inconsistent"

    if n == 1:
        return AYAH_UNLOCK_NEAR_PASS_1, "yes_if_1_row_strict"

    if n == 2:
        return AYAH_UNLOCK_NEAR_PASS_2, "yes_if_2_rows_strict"

    kinds = [_primary_blocker_kind(t) for t in blockers]
    core_n = sum(1 for k in kinds if k == "requires_core")
    cf_n = sum(1 for k in kinds if k == "true_conflict")
    al_n = sum(1 for k in kinds if k == "alignment_issue")

    if al_n > 0 and al_n >= n * 0.5:
        return AYAH_UNLOCK_ALIGNMENT_BLOCKED, "multiple_alignment_skips"

    if core_n >= max(1, (n + 1) // 2) and core_n >= cf_n:
        return AYAH_UNLOCK_CORE_BLOCKED, "dominant_core_limitations"

    if cf_n >= max(1, (n + 1) // 3) and cf_n > core_n:
        return AYAH_UNLOCK_TRUE_CONFLICT, "dominant_gold_l11_conflict"

    return AYAH_UNLOCK_REVIEW_NEEDED, "many_blockers_mixed"


def _count_blocker_kinds(blockers: Sequence[Dict[str, Any]]) -> Dict[str, int]:
    keys = (
        "unlockable_now_count",
        "requires_core_count",
        "true_conflict_count",
        "alignment_issue_count",
        "quarantine_only_count",
    )
    out = {k: 0 for k in keys}
    for t in blockers:
        k = _primary_blocker_kind(t)
        if k == "unlockable_now":
            out["unlockable_now_count"] += 1
        elif k == "requires_core":
            out["requires_core_count"] += 1
        elif k == "true_conflict":
            out["true_conflict_count"] += 1
        elif k == "alignment_issue":
            out["alignment_issue_count"] += 1
        elif k == "quarantine_only":
            out["quarantine_only_count"] += 1
    return out


def _dominant_blocker_type(blockers: Sequence[Dict[str, Any]]) -> str:
    if not blockers:
        return ""
    counts: Dict[str, int] = {}
    for t in blockers:
        k = _primary_blocker_kind(t)
        counts[k] = counts.get(k, 0) + 1
    return max(counts.items(), key=lambda x: (x[1], x[0]))[0]


def build_ayah_blocker_ranking_row(
    surah: int,
    ayah: int,
    decision: AyahDecision,
    truth_rows: Sequence[Dict[str, Any]],
    reason: str,
) -> Dict[str, Any]:
    blockers = _blocker_rows(truth_rows)
    n = len(blockers)
    kinds = _count_blocker_kinds(blockers)
    ayah_status, would_fix = classify_ayah_unlock_status(decision, truth_rows)

    idxs = [str(truth_rows.index(t)) for t in blockers]  # unstable; use word index
    wi_list = [str(int(t.get("ayah_word_index", -1))) for t in blockers]
    words = [t.get("word", "") for t in blockers]
    rs = (
        f"decision={decision.value};blockers={n};{reason[:120]}"
        if reason
        else f"decision={decision.value};blockers={n}"
    )
    return {
        "surah": surah,
        "ayah": ayah,
        "ayah_status": ayah_status,
        "blocker_row_count": str(n),
        "blocker_row_indexes": ";".join(wi_list),
        "blocker_words": ";".join(words),
        "unlockable_now_count": str(kinds["unlockable_now_count"]),
        "requires_core_count": str(kinds["requires_core_count"]),
        "true_conflict_count": str(kinds["true_conflict_count"]),
        "alignment_issue_count": str(kinds["alignment_issue_count"]),
        "quarantine_only_count": str(kinds["quarantine_only_count"]),
        "would_ayah_pass_if_fixed": would_fix,
        "reason_summary": rs,
    }


def build_near_pass_ayah_row(
    surah: int,
    ayah: int,
    decision: AyahDecision,
    truth_rows: Sequence[Dict[str, Any]],
    reason: str,
) -> Dict[str, Any]:
    strict_n = sum(1 for t in truth_rows if _row_strict_satisfied(t))
    blockers = _blocker_rows(truth_rows)
    bn = len(blockers)
    ayah_status, _ = classify_ayah_unlock_status(decision, truth_rows)
    dom = _dominant_blocker_type(blockers)

    wp1 = str(ayah_status == AYAH_UNLOCK_NEAR_PASS_1).lower()
    wp2 = str(ayah_status == AYAH_UNLOCK_NEAR_PASS_2).lower()
    if ayah_status == AYAH_UNLOCK_PASS_STRICT:
        action = "PASS_NOW"
    elif ayah_status == AYAH_UNLOCK_NEAR_PASS_1:
        action = "REVIEW_SINGLE_BLOCKER_THEN_WRITE"
    elif ayah_status == AYAH_UNLOCK_NEAR_PASS_2:
        action = "REVIEW_TWO_BLOCKERS_THEN_WRITE"
    elif ayah_status == AYAH_UNLOCK_CORE_BLOCKED:
        action = "NEEDS_CORE_NEXT"
    elif ayah_status == AYAH_UNLOCK_TRUE_CONFLICT:
        action = "TRUE_CONFLICT_REVIEW"
    elif ayah_status == AYAH_UNLOCK_ALIGNMENT_BLOCKED:
        action = "FIX_ALIGNMENT"
    else:
        action = "MANUAL_REVIEW"

    return {
        "surah": surah,
        "ayah": ayah,
        "ayah_status": ayah_status,
        "strict_rows": str(strict_n),
        "failed_rows": str(bn),
        "blocker_row_count": str(bn),
        "would_pass_with_one_fix": wp1,
        "would_pass_with_two_fixes": wp2,
        "best_next_action": action,
        "dominant_blocker_type": dom,
        "reason_summary": (reason or decision.value)[:300],
    }


def build_unlock_preview_rows(
    surah: int,
    ayah: int,
    decision: AyahDecision,
    truth_rows: Sequence[Dict[str, Any]],
    structured_rows: Sequence[Dict[str, Any]],
    wi_to_gi: Dict[int, int],
) -> List[Dict[str, Any]]:
    """Rows that are strict-eligible but ayah is not PASS_STRICT (trapped), plus partial near-tier."""
    if decision == AyahDecision.PASS_STRICT:
        return []

    ayah_status, _ = classify_ayah_unlock_status(decision, truth_rows)
    truth_by_wi = {int(t.get("ayah_word_index", -1)): t for t in truth_rows}

    out: List[Dict[str, Any]] = []
    for s in structured_rows:
        try:
            wi = int(s.get("ayah_word_index", -1))
        except (TypeError, ValueError):
            wi = -1
        tier = (s.get("comparator_tier") or "").strip()
        eligible = (s.get("strict_acceptance_eligible") or "").lower() == "true"
        trapped = tier in STRICT_TIERS and eligible
        partial = tier == ComparatorTier.PARTIAL_STRUCTURED_MATCH.value
        if not trapped and not partial:
            continue

        tr = truth_by_wi.get(wi, {})
        ab = (tr.get("audit_bucket") or "")[:80]
        pu = tr.get("potentially_unlockable_without_l17_core") == "true"
        req_core = _primary_blocker_kind(tr) == "requires_core" if tr else False

        gri = wi_to_gi.get(wi, "")
        out.append(
            {
                "surah": surah,
                "ayah": ayah,
                "word": s.get("word", ""),
                "row_index": str(gri),
                "match_tier": tier,
                "strict_acceptance_eligible": str(eligible).lower(),
                "row_status": ab,
                "ayah_status": ayah_status,
                "currently_trapped_by_ayah": str(trapped and decision != AyahDecision.PASS_STRICT).lower(),
                "unlockable_now_without_core_change": str(pu).lower(),
                "requires_core_change": str(req_core).lower(),
                "notes": f"Batch 28.9 preview; partial_near={partial}",
            }
        )
    return out


def _near_pass_2_strong(blockers: Sequence[Dict[str, Any]]) -> bool:
    if len(blockers) != 2:
        return False
    kinds = {_primary_blocker_kind(t) for t in blockers}
    return kinds.issubset({"unlockable_now", "quarantine_only"})


def build_best_write_candidate_row(
    surah: int,
    ayah: int,
    decision: AyahDecision,
    truth_rows: Sequence[Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    blockers = _blocker_rows(truth_rows)
    strict_n = sum(1 for t in truth_rows if _row_strict_satisfied(t))
    bn = len(blockers)
    ayah_status, _ = classify_ayah_unlock_status(decision, truth_rows)
    dom = _dominant_blocker_type(blockers)

    if ayah_status == AYAH_UNLOCK_PASS_STRICT:
        safety = "safe_now"
        step = "eligible_for_isolated_write_if_policy_allows"
    elif ayah_status == AYAH_UNLOCK_NEAR_PASS_1:
        safety = "safe_after_manual_review"
        step = "verify_single_blocker_then_bounded_write"
    elif ayah_status == AYAH_UNLOCK_NEAR_PASS_2 and _near_pass_2_strong(blockers):
        safety = "safe_after_manual_review"
        step = "verify_two_tooling_blockers_then_bounded_write"
    elif ayah_status == AYAH_UNLOCK_NEAR_PASS_2:
        safety = "not_safe_yet"
        step = "resolve_core_or_conflict_blockers_first"
    else:
        return None

    return {
        "surah": surah,
        "ayah": ayah,
        "ayah_status": ayah_status,
        "strict_row_count": str(strict_n),
        "failed_row_count": str(bn),
        "blocker_row_count": str(bn),
        "dominant_blocker_type": dom,
        "recommended_write_safety": safety,
        "recommended_next_step": step,
    }


def build_batch_28_9_summary_dict(
    near_pass_rows: Sequence[Dict[str, Any]],
    trapped_strict_rows_total: int,
    trapped_strict_ayahs: int,
    best_write_rows: Sequence[Dict[str, Any]],
) -> Dict[str, Any]:
    def _cnt(label: str) -> int:
        return sum(1 for r in near_pass_rows if (r.get("ayah_status") or "") == label)

    np1 = _cnt(AYAH_UNLOCK_NEAR_PASS_1)
    np2 = _cnt(AYAH_UNLOCK_NEAR_PASS_2)

    def _near_sort_key(r: Dict[str, Any]) -> Tuple[int, int, int]:
        return (
            int(r.get("failed_rows") or 0),
            int(r.get("blocker_row_count") or 0),
            int(r.get("surah") or 0) * 1000 + int(r.get("ayah") or 0),
        )

    near_sel = [
        r
        for r in near_pass_rows
        if (r.get("ayah_status") or "")
        in (AYAH_UNLOCK_NEAR_PASS_1, AYAH_UNLOCK_NEAR_PASS_2)
    ]
    near_sel.sort(key=_near_sort_key)
    top_near = [f'{r.get("surah")}:{r.get("ayah")}' for r in near_sel[:10]]

    core_sel = [r for r in near_pass_rows if (r.get("ayah_status") or "") == AYAH_UNLOCK_CORE_BLOCKED]
    core_sel.sort(key=lambda r: (-int(r.get("failed_rows") or 0), int(r.get("surah") or 0), int(r.get("ayah") or 0)))
    top_core = [f'{r.get("surah")}:{r.get("ayah")}' for r in core_sel[:10]]

    best_list = [f'{r.get("surah")}:{r.get("ayah")}' for r in best_write_rows[:25]]

    return {
        "near_pass_1_count": np1,
        "near_pass_2_count": np2,
        "core_blocked_ayah_count": _cnt(AYAH_UNLOCK_CORE_BLOCKED),
        "alignment_blocked_ayah_count": _cnt(AYAH_UNLOCK_ALIGNMENT_BLOCKED),
        "true_conflict_ayah_count": _cnt(AYAH_UNLOCK_TRUE_CONFLICT),
        "review_needed_ayah_count": _cnt(AYAH_UNLOCK_REVIEW_NEEDED),
        "trapped_strict_rows": trapped_strict_rows_total,
        "trapped_strict_ayahs": trapped_strict_ayahs,
        "unlocked_if_near_pass_1_fixed": np1,
        "unlocked_if_near_pass_2_fixed": np2,
        "top_10_near_pass_ayahs": top_near,
        "top_10_core_blocked_ayahs": top_core,
        "best_write_candidates": best_list,
    }


def write_csv(path: Path, fieldnames: Sequence[str], rows: Sequence[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fieldnames))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fieldnames})


BLOCKER_RANKING_FIELDS = (
    "surah",
    "ayah",
    "ayah_status",
    "blocker_row_count",
    "blocker_row_indexes",
    "blocker_words",
    "unlockable_now_count",
    "requires_core_count",
    "true_conflict_count",
    "alignment_issue_count",
    "quarantine_only_count",
    "would_ayah_pass_if_fixed",
    "reason_summary",
)

NEAR_PASS_AYAH_FIELDS = (
    "surah",
    "ayah",
    "ayah_status",
    "strict_rows",
    "failed_rows",
    "blocker_row_count",
    "would_pass_with_one_fix",
    "would_pass_with_two_fixes",
    "best_next_action",
    "dominant_blocker_type",
    "reason_summary",
)

UNLOCK_PREVIEW_FIELDS = (
    "surah",
    "ayah",
    "word",
    "row_index",
    "match_tier",
    "strict_acceptance_eligible",
    "row_status",
    "ayah_status",
    "currently_trapped_by_ayah",
    "unlockable_now_without_core_change",
    "requires_core_change",
    "notes",
)

BEST_WRITE_FIELDS = (
    "surah",
    "ayah",
    "ayah_status",
    "strict_row_count",
    "failed_row_count",
    "blocker_row_count",
    "dominant_blocker_type",
    "recommended_write_safety",
    "recommended_next_step",
)
