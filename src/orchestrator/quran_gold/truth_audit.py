# -*- coding: utf-8 -*-
"""
Truth-source audit for Quran iʿrāb comparison (Batch 28.5).

Classifies aligned rows by why acceptance failed or succeeded; no ML.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import (
    ComparatorTier,
    MatchDecision,
    normalize_i3rab_for_exact_compare,
    strict_acceptance_eligible,
    structured_strict_gold_vs_l11_prose,
    _l17_authoritative,
    _structured_strict_agreement,
)
from orchestrator.quran_gold.gold_prose_parser import effective_gold_structure_for_compare


def _l17_summary(l17: Optional[Dict[str, Any]]) -> str:
    if not l17:
        return ""
    parts = [
        (l17.get("status") or "").strip(),
        (l17.get("syntactic_role") or "").strip(),
        (l17.get("i3rab_case_or_mood") or "").strip(),
    ]
    return " | ".join(p for p in parts if p)[:400]


def estimate_best_possible_safe_tier(
    gold_i3rab: str,
    l11: str,
    snap: Optional[TokenAnalyzerSnapshot],
) -> Tuple[str, str]:
    """
    Returns (best_tier_label, short_reason).
    Hypothetical only — does not override comparator.
    """
    if snap is None:
        return "mismatch", "no_snapshot"
    l17 = snap.l17
    l17_auth = _l17_authoritative(snap)
    gs = effective_gold_structure_for_compare(gold_i3rab)
    ng = normalize_i3rab_for_exact_compare(gold_i3rab)
    nl = normalize_i3rab_for_exact_compare(l11) if l11 else ""
    if l11 and (ng == nl or _nfc_eq(gold_i3rab, l11)):
        return ComparatorTier.EXACT_TEXT_MATCH.value, "exact_after_norm_or_nfc"
    if l17_auth and l17:
        ok, _ = _structured_strict_agreement(gs, l17)
        if ok:
            return ComparatorTier.STRICT_STRUCTURAL_MATCH.value, "l17_structured_hypothetical"
    if l11:
        ok11, _ = structured_strict_gold_vs_l11_prose(gs, l11)
        if ok11:
            return ComparatorTier.STRICT_STRUCTURAL_MATCH.value, "l11_structured_hypothetical"
    return ComparatorTier.MISMATCH.value, "no_safe_strict_path"


def _nfc_eq(a: str, b: str) -> bool:
    import unicodedata

    return unicodedata.normalize("NFC", (a or "").strip()) == unicodedata.normalize("NFC", (b or "").strip())


def classify_audit_bucket(
    *,
    aligned: bool,
    gold_i3rab: str,
    l11: str,
    snap: Optional[TokenAnalyzerSnapshot],
    dec: MatchDecision,
    already_erqa: bool,
) -> Tuple[str, str, str, bool]:
    """
    Returns (audit_bucket, acceptance_blocker, best_possible_safe_tier, unlockable_without_l17_core).
    """
    if already_erqa:
        return "ALREADY_SATISFIED_ERQA", "", ComparatorTier.EXACT_TEXT_MATCH.value, True

    if not aligned:
        return "ALIGNMENT_FAILED", "alignment", "mismatch", False

    if snap is None:
        return "ANALYZER_EMPTY_OR_LOW_SIGNAL", "no_snapshot", "mismatch", False

    l11_s = l11 or ""
    l17 = snap.l17
    l17_auth = _l17_authoritative(snap)
    gs = effective_gold_structure_for_compare(gold_i3rab)
    best_tier, _ = estimate_best_possible_safe_tier(gold_i3rab, l11_s, snap)

    if strict_acceptance_eligible(dec):
        return "ACCEPTED_STRICT_TIER", "", dec.tier.value, True

    if not l11_s and not l17:
        return "ANALYZER_EMPTY_OR_LOW_SIGNAL", "no_l11_no_l17", best_tier, False

    ok_l11_s, r11 = structured_strict_gold_vs_l11_prose(gs, l11_s) if l11_s else (False, "")
    ng = normalize_i3rab_for_exact_compare(gold_i3rab)
    nl = normalize_i3rab_for_exact_compare(l11_s)
    norm_exact_possible = bool(l11_s) and ng == nl
    unlock_no_l17 = bool(norm_exact_possible or ok_l11_s)

    long_gold = len(gold_i3rab) > 100
    short_l11 = bool(l11_s) and len(l11_s) < len(gold_i3rab) * 0.55

    if gs.syntactic_role_status != "resolved" and gs.parser_confidence < 0.45:
        return "GOLD_PARSED_STRUCTURE_TOO_WEAK", "sparse_parse", best_tier, False

    if norm_exact_possible and dec.tier != ComparatorTier.EXACT_TEXT_MATCH:
        return (
            "L11_EXACT_TEXT_POSSIBLE_BUT_NORMALIZATION_BLOCKED",
            dec.notes,
            ComparatorTier.EXACT_TEXT_MATCH.value,
            True,
        )

    if ok_l11_s and dec.tier not in (
        ComparatorTier.STRICT_STRUCTURAL_MATCH,
        ComparatorTier.EXACT_TEXT_MATCH,
    ):
        return (
            "L11_STRONG_STRUCTURAL_MATCH_POSSIBLE",
            r11 or dec.notes,
            ComparatorTier.STRICT_STRUCTURAL_MATCH.value,
            True,
        )

    if l17_auth and l17:
        ok17, r17 = _structured_strict_agreement(gs, l17)
        if ok17 and dec.tier != ComparatorTier.STRICT_STRUCTURAL_MATCH:
            return "L17_STRONG_STRUCTURAL_MATCH_POSSIBLE", r17, ComparatorTier.STRICT_STRUCTURAL_MATCH.value, False

    if long_gold and short_l11 and not l17_auth:
        if ok_l11_s:
            return "GOLD_LONG_PROSE_L11_SHORT_BUT_COMPATIBLE", dec.notes, best_tier, True
        return "GOLD_LONG_PROSE_L17_UNAVAILABLE", "l17_unresolved", best_tier, unlock_no_l17

    if long_gold and short_l11 and l17_auth and l17:
        ok17, r17 = _structured_strict_agreement(gs, l17)
        if not ok17 and not ok_l11_s:
            return "GOLD_LONG_PROSE_L11_CONFLICT", dec.notes or r17, best_tier, False

    return "ALIGNMENT_OK_BUT_COMPARATOR_REJECTED", dec.notes, best_tier, unlock_no_l17


def build_truth_audit_row_alignment_failed(
    *,
    surah: int,
    ayah: int,
    ayah_word_index: int,
    word: str,
    gold_i3rab: str,
) -> Dict[str, Any]:
    return {
        "surah": surah,
        "ayah": ayah,
        "ayah_word_index": ayah_word_index,
        "word": word,
        "gold_i3rab": gold_i3rab,
        "l11_i3rab": "",
        "l17_i3rab_blob_or_summary": "",
        "comparator_tier_current": ComparatorTier.MISMATCH.value,
        "audit_bucket": "ALIGNMENT_FAILED",
        "acceptance_blocker": "alignment",
        "best_possible_safe_tier": "mismatch",
        "potentially_unlockable_without_l17_core": "false",
    }


def build_truth_audit_row(
    *,
    surah: int,
    ayah: int,
    ayah_word_index: int,
    word: str,
    gold_i3rab: str,
    snap: Optional[TokenAnalyzerSnapshot],
    dec: MatchDecision,
    aligned: bool,
    already_erqa: bool,
) -> Dict[str, Any]:
    l11 = (snap.l11_i3rab_text or "") if snap else ""
    l17 = snap.l17 if snap else None
    bucket, blocker, best_tier, unlock_nc = classify_audit_bucket(
        aligned=aligned,
        gold_i3rab=gold_i3rab,
        l11=l11,
        snap=snap,
        dec=dec,
        already_erqa=already_erqa,
    )
    return {
        "surah": surah,
        "ayah": ayah,
        "ayah_word_index": ayah_word_index,
        "word": word,
        "gold_i3rab": gold_i3rab,
        "l11_i3rab": l11,
        "l17_i3rab_blob_or_summary": _l17_summary(l17),
        "comparator_tier_current": dec.tier.value,
        "audit_bucket": bucket,
        "acceptance_blocker": blocker,
        "best_possible_safe_tier": best_tier,
        "potentially_unlockable_without_l17_core": str(unlock_nc).lower(),
    }


TRUTH_AUDIT_FIELDS = (
    "surah",
    "ayah",
    "ayah_word_index",
    "word",
    "gold_i3rab",
    "l11_i3rab",
    "l17_i3rab_blob_or_summary",
    "comparator_tier_current",
    "audit_bucket",
    "acceptance_blocker",
    "best_possible_safe_tier",
    "potentially_unlockable_without_l17_core",
)

UNLOCKABLE_AYAH_FIELDS = (
    "surah",
    "ayah",
    "total_rows",
    "aligned_rows",
    "accepted_rows_current",
    "rows_unlockable_via_l11_only",
    "rows_unlockable_via_gold_parser_only",
    "rows_unlockable_via_comparator_logic_only",
    "rows_blocked_by_missing_l17",
    "rows_blocked_by_real_conflict",
    "ayah_status_current",
    "ayah_status_if_batch_28_5_succeeds",
    "concise_unlock_strategy",
)

REAL_ACCEPT_PREVIEW_FIELDS = (
    "surah",
    "ayah",
    "word",
    "gold_i3rab",
    "system_i3rab_candidate",
    "candidate_acceptance_tier",
    "acceptance_reason",
    "source_authority_used",
    "confidence",
    "safe_to_accept_now",
)


def aggregate_batch_28_5_counters(truth_rows: List[Dict[str, Any]]) -> Dict[str, int]:
    """Roll-up counts for batch summary JSON (real corpus rows)."""
    done = {"ALREADY_SATISFIED_ERQA", "ACCEPTED_STRICT_TIER"}
    unlock_now = 0
    blocked_l17 = 0
    blocked_parser = 0
    blocked_conflict = 0
    for r in truth_rows:
        b = r.get("audit_bucket", "")
        pu = r.get("potentially_unlockable_without_l17_core") == "true"
        if b in done:
            continue
        if b == "GOLD_PARSED_STRUCTURE_TOO_WEAK":
            blocked_parser += 1
        elif b == "GOLD_LONG_PROSE_L11_CONFLICT":
            blocked_conflict += 1
        elif b == "GOLD_LONG_PROSE_L17_UNAVAILABLE" and not pu:
            blocked_l17 += 1
        if pu and b not in done:
            unlock_now += 1
    cand_accept = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") == "ACCEPTED_STRICT_TIER"
        or r.get("comparator_tier_current") in ("exact_text_match", "strict_structural_match")
    )
    return {
        "rows_unlockable_now": unlock_now,
        "rows_blocked_by_l17_core": blocked_l17,
        "rows_blocked_by_gold_parser_limits": blocked_parser,
        "rows_blocked_by_true_conflict": blocked_conflict,
        "candidate_real_accept_rows": cand_accept,
    }


def summarize_ayah_unlockability(
    truth_rows: List[Dict[str, Any]],
    ayah_status: str,
) -> Dict[str, Any]:
    """Aggregate row-level truth audits for one ayah."""
    total = len(truth_rows)
    aligned = sum(1 for r in truth_rows if r.get("audit_bucket") != "ALIGNMENT_FAILED")
    accepted = sum(1 for r in truth_rows if r.get("audit_bucket") == "ACCEPTED_STRICT_TIER")
    l11_only = sum(
        1
        for r in truth_rows
        if r.get("potentially_unlockable_without_l17_core") == "true"
        and "L11" in (r.get("best_possible_safe_tier") or "")
    )
    # heuristic counts
    gp_only = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") == "GOLD_PARSED_STRUCTURE_TOO_WEAK"
    )
    comp_only = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") == "L11_EXACT_TEXT_POSSIBLE_BUT_NORMALIZATION_BLOCKED"
    )
    miss_l17 = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") == "GOLD_LONG_PROSE_L17_UNAVAILABLE"
    )
    conflict = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") in ("GOLD_LONG_PROSE_L11_CONFLICT", "GOLD_LONG_PROSE_L11_SHORT_BUT_COMPATIBLE")
        and r.get("potentially_unlockable_without_l17_core") == "false"
    )
    unlockable_now = sum(
        1
        for r in truth_rows
        if r.get("potentially_unlockable_without_l17_core") == "true"
        and r.get("audit_bucket") not in ("ACCEPTED_STRICT_TIER", "ALREADY_SATISFIED_ERQA")
    )
    strict_ok = ayah_status == "PASS_STRICT"
    # Hypothetical: if every non-satisfied row were tooling-unlocked, could we pass?
    pending_non_erqa = sum(
        1
        for r in truth_rows
        if r.get("audit_bucket") not in ("ALREADY_SATISFIED_ERQA", "ACCEPTED_STRICT_TIER")
    )
    future = "PASS_STRICT" if strict_ok else (
        "PASS_STRICT" if pending_non_erqa > 0 and unlockable_now >= pending_non_erqa else ayah_status
    )
    strategy = ""
    if unlockable_now > 0:
        strategy = "tooling_unlock_rows_without_l17"
    elif miss_l17 > 0:
        strategy = "needs_l17_resolution_or_l11_agreement"
    elif conflict > 0:
        strategy = "review_conflicts"
    return {
        "total_rows": total,
        "aligned_rows": aligned,
        "accepted_rows_current": accepted,
        "rows_unlockable_via_l11_only": l11_only,
        "rows_unlockable_via_gold_parser_only": gp_only,
        "rows_unlockable_via_comparator_logic_only": comp_only,
        "rows_blocked_by_missing_l17": miss_l17,
        "rows_blocked_by_real_conflict": conflict,
        "ayah_status_current": ayah_status,
        "ayah_status_if_batch_28_5_succeeds": future,
        "concise_unlock_strategy": strategy,
    }


def write_truth_audit_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    import csv
    from pathlib import Path

    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with open(p, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(TRUTH_AUDIT_FIELDS))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in TRUTH_AUDIT_FIELDS})


def write_unlockable_ayahs_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    import csv
    from pathlib import Path

    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with open(p, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(UNLOCKABLE_AYAH_FIELDS))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in UNLOCKABLE_AYAH_FIELDS})


def write_real_accept_preview_csv(path: Any, rows: List[Dict[str, Any]]) -> None:
    import csv
    from pathlib import Path

    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with open(p, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(REAL_ACCEPT_PREVIEW_FIELDS))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in REAL_ACCEPT_PREVIEW_FIELDS})
