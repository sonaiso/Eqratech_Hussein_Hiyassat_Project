# -*- coding: utf-8 -*-
"""
Ayah-bounded evaluation for Quran iʿrāb comparison (Batch 28.3).

One ayah → one decision: PASS_STRICT, FAIL_*, or REVIEW_NEEDED.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from orchestrator import run_pipeline
from orchestrator.quran_gold.alignment import AlignmentOutcome, align_gold_words_to_pipeline_tokens
from orchestrator.quran_gold.analyzer_extract import extract_snapshots, get_token_surfaces
from orchestrator.quran_gold.accepted_row_serializer import build_accepted_erqa_row, erqa_row_to_field_dict
from orchestrator.quran_gold.comparator import compare_token_conservative, strict_acceptance_eligible
from orchestrator.quran_gold.gold_prose_parser import parse_gold_i3rab_prose
from orchestrator.quran_gold.i3rab_compare_pipeline import row_key
from orchestrator.quran_gold.truth_audit import (
    build_truth_audit_row,
    build_truth_audit_row_alignment_failed,
)


class AyahDecision(str, Enum):
    PASS_STRICT = "PASS_STRICT"
    FAIL_ALIGNMENT = "FAIL_ALIGNMENT"
    FAIL_COMPARATOR = "FAIL_COMPARATOR"
    FAIL_ANALYSIS = "FAIL_ANALYSIS"
    REVIEW_NEEDED = "REVIEW_NEEDED"


@dataclass
class AyahBatchResult:
    decision: AyahDecision
    surah: int
    ayah: int
    rows_total: int
    rows_skipped_alignment: int
    rows_strict_accepted: int
    rows_rejected_comparator: int
    rows_already_in_erqa: int
    new_erqa_payloads: List[Dict[str, Any]] = field(default_factory=list)
    wrong_payloads: List[Dict[str, Any]] = field(default_factory=list)
    alignment_debug_rows: List[Dict[str, Any]] = field(default_factory=list)
    structured_debug_rows: List[Dict[str, Any]] = field(default_factory=list)
    truth_audit_rows: List[Dict[str, Any]] = field(default_factory=list)
    preview_candidate_rows: List[Dict[str, Any]] = field(default_factory=list)
    reason: str = ""


def _alignment_debug_stub(
    gi: int,
    row: Any,
    ayah_text: str,
    rr: Optional[Any],
    comparator_label: str,
) -> Dict[str, Any]:
    from orchestrator.quran_gold.alignment import normalize_arabic_surface

    surf = ""
    tnorm = ""
    reason_out = ""
    st = ""
    if rr is not None:
        surf = rr.ayah_token_surface or ""
        tnorm = rr.ayah_token_normalized or ""
        seg = getattr(rr, "segmentation_reason", "") or ""
        reason_out = (seg or rr.reason or "").strip()
        st = rr.outcome.value
    return {
        "row_index": gi,
        "surah": row.surah,
        "ayah": row.ayah,
        "gold_word": row.word,
        "gold_word_normalized": normalize_arabic_surface(row.word),
        "ayah_text": ayah_text,
        "ayah_token_index": "" if rr is None or rr.token_index is None else str(rr.token_index),
        "ayah_token_surface": surf,
        "ayah_token_normalized": tnorm,
        "alignment_status": st,
        "alignment_reason": reason_out,
        "occurrence_rank_gold": str(getattr(rr, "occurrence_rank_gold", 0) if rr else 0),
        "occurrence_rank_ayah": str(getattr(rr, "occurrence_rank_ayah", 0) if rr else 0),
        "comparator_decision": comparator_label,
    }


def evaluate_ayah(
    surah: int,
    ayah: int,
    indexed: Sequence[Tuple[int, Any]],
    erqa_keys: Set[Tuple[int, int, int]],
    ayah_text: str,
    *,
    repair_pass: int = 0,
    require_strict_comparator: bool = True,
) -> AyahBatchResult:
    """
    Evaluate one ayah. Rows already present in ``erqa_keys`` count as satisfied for strict policy.
    New ERQA payloads are produced only for rows not yet in erqa that pass strict acceptance.
    """
    cands = [(gi, r) for gi, r in indexed if r.surah == surah and r.ayah == ayah]
    cands.sort(key=lambda t: t[1].index_in_ayah)
    row_global_indices = [gi for gi, _ in cands]
    full_rows = [r for _, r in cands]
    rows_total = len(full_rows)
    already_erqa = sum(1 for r in full_rows if row_key(r) in erqa_keys)

    if not ayah_text.strip():
        return AyahBatchResult(
            decision=AyahDecision.FAIL_ANALYSIS,
            surah=surah,
            ayah=ayah,
            rows_total=rows_total,
            rows_skipped_alignment=rows_total,
            rows_strict_accepted=0,
            rows_rejected_comparator=0,
            rows_already_in_erqa=already_erqa,
            reason="missing_ayah_text",
            structured_debug_rows=[],
            truth_audit_rows=[],
            preview_candidate_rows=[],
        )

    pipeline = run_pipeline(
        ayah_text,
        source={"entrypoint": "ayah_batch_runner", "surah": surah, "ayah": ayah},
    )
    token_surfaces = get_token_surfaces(pipeline)
    snapshots = extract_snapshots(pipeline)
    if not token_surfaces or not snapshots:
        return AyahBatchResult(
            decision=AyahDecision.FAIL_ANALYSIS,
            surah=surah,
            ayah=ayah,
            rows_total=rows_total,
            rows_skipped_alignment=rows_total,
            rows_strict_accepted=0,
            rows_rejected_comparator=0,
            rows_already_in_erqa=already_erqa,
            reason="empty_pipeline_tokens_or_snapshots",
            structured_debug_rows=[],
            truth_audit_rows=[],
            preview_candidate_rows=[],
        )

    gold_words = [r.word for r in full_rows]
    rich_align = align_gold_words_to_pipeline_tokens(
        gold_words, token_surfaces, repair_pass=repair_pass
    )

    skipped_align = 0
    ad_rows: List[Dict[str, Any]] = []
    new_erqa: List[Dict[str, Any]] = []
    wrong: List[Dict[str, Any]] = []
    structured_debug_rows: List[Dict[str, Any]] = []
    truth_audit_rows: List[Dict[str, Any]] = []
    preview_candidate_rows: List[Dict[str, Any]] = []

    # Per-row: skip pipeline compare if already in cumulative erqa
    for i, r in enumerate(full_rows):
        gi = row_global_indices[i]
        if row_key(r) in erqa_keys:
            ad_rows.append(
                {
                    **_alignment_debug_stub(gi, r, ayah_text, None, "already_in_erqa"),
                }
            )
            truth_audit_rows.append(
                {
                    "surah": surah,
                    "ayah": ayah,
                    "ayah_word_index": r.index_in_ayah,
                    "word": r.word,
                    "gold_i3rab": r.i3rab,
                    "l11_i3rab": "",
                    "l17_i3rab_blob_or_summary": "",
                    "comparator_tier_current": "already_in_erqa",
                    "audit_bucket": "ALREADY_SATISFIED_ERQA",
                    "acceptance_blocker": "",
                    "best_possible_safe_tier": "exact_text_match",
                    "potentially_unlockable_without_l17_core": "true",
                }
            )
            continue

        pos = r.index_in_ayah
        if pos < 0 or pos >= len(rich_align):
            skipped_align += 1
            ad_rows.append(
                _alignment_debug_stub(
                    gi,
                    r,
                    ayah_text,
                    None,
                    "skipped_alignment",
                )
            )
            truth_audit_rows.append(
                build_truth_audit_row_alignment_failed(
                    surah=surah,
                    ayah=ayah,
                    ayah_word_index=r.index_in_ayah,
                    word=r.word,
                    gold_i3rab=r.i3rab,
                )
            )
            continue
        rr = rich_align[pos]
        ok_al = rr.outcome in (
            AlignmentOutcome.ALIGNED_UNIQUE,
            AlignmentOutcome.ALIGNED_BY_OCCURRENCE,
        )
        if not ok_al:
            skipped_align += 1
            ad_rows.append(
                _alignment_debug_stub(
                    gi,
                    r,
                    ayah_text,
                    rr,
                    "skipped_alignment",
                )
            )
            truth_audit_rows.append(
                build_truth_audit_row_alignment_failed(
                    surah=surah,
                    ayah=ayah,
                    ayah_word_index=r.index_in_ayah,
                    word=r.word,
                    gold_i3rab=r.i3rab,
                )
            )
            continue

        tok_i = rr.token_index
        assert tok_i is not None
        snap = snapshots[tok_i] if tok_i < len(snapshots) else None
        dec = compare_token_conservative(r.i3rab, snap, repair_pass=repair_pass)
        tier_label = dec.tier.value
        tr = dec.trace or {}
        gs_lim = parse_gold_i3rab_prose(r.i3rab)
        structured_debug_rows.append(
            {
                "surah": surah,
                "ayah": ayah,
                "word": r.word,
                "gold_i3rab_raw": r.i3rab,
                "gold_family": tr.get("gold_family", ""),
                "gold_role": tr.get("gold_role", ""),
                "gold_case_bucket": tr.get("gold_case_bucket", ""),
                "gold_marker": tr.get("gold_marker", ""),
                "l17_family": tr.get("l17_family_guess", ""),
                "l17_role": tr.get("l17_role_blob", ""),
                "l17_case_bucket": tr.get("l17_case_bucket", ""),
                "l17_marker": tr.get("l17_marker", ""),
                "comparator_tier": dec.tier.value,
                "strict_acceptance_eligible": str(strict_acceptance_eligible(dec)).lower(),
                "reason": dec.notes,
                "parser_confidence": tr.get("parser_confidence") or str(gs_lim.parser_confidence),
                "parser_limitations": ",".join(gs_lim.limitations),
                "ayah_word_index": r.index_in_ayah,
            }
        )
        truth_audit_rows.append(
            build_truth_audit_row(
                surah=surah,
                ayah=ayah,
                ayah_word_index=r.index_in_ayah,
                word=r.word,
                gold_i3rab=r.i3rab,
                snap=snap,
                dec=dec,
                aligned=True,
                already_erqa=False,
            )
        )
        if strict_acceptance_eligible(dec):
            accepted_full = erqa_row_to_field_dict(
                build_accepted_erqa_row(
                    surah=r.surah,
                    ayah=r.ayah,
                    word=r.word,
                    gold_i3rab=r.i3rab,
                    ayah_word_index=r.index_in_ayah,
                    dec=dec,
                    snap=snap,
                )
            )
            preview_candidate_rows.append(
                {
                    "surah": surah,
                    "ayah": ayah,
                    "word": r.word,
                    "gold_i3rab": r.i3rab,
                    "system_i3rab_candidate": accepted_full["system_i3rab"],
                    "candidate_acceptance_tier": dec.tier.value,
                    "acceptance_reason": dec.notes,
                    "source_authority_used": dec.analyzer_source,
                    "confidence": f"{dec.confidence:.4f}",
                    "safe_to_accept_now": "",
                }
            )
            ad_rows.append(_alignment_debug_stub(gi, r, ayah_text, rr, tier_label))
            new_erqa.append(accepted_full)
        else:
            ad_rows.append(_alignment_debug_stub(gi, r, ayah_text, rr, tier_label))
            wrong.append(
                {
                    "surah": r.surah,
                    "ayah": r.ayah,
                    "word": r.word,
                    "gold_i3rab": r.i3rab,
                    "system_i3rab": dec.system_i3rab_display,
                    "mismatch_reason": dec.notes,
                    "alignment_status": rr.outcome.value,
                    "analyzer_source": dec.analyzer_source,
                    "notes": dec.tier.value,
                    "ayah_word_index": r.index_in_ayah,
                }
            )

    pending_need = [r for r in full_rows if row_key(r) not in erqa_keys]
    pending_need_n = len(pending_need)
    pending_aligned_strict = len(new_erqa)
    rejected = len(wrong)

    if skipped_align > 0:
        return AyahBatchResult(
            decision=AyahDecision.FAIL_ALIGNMENT,
            surah=surah,
            ayah=ayah,
            rows_total=rows_total,
            rows_skipped_alignment=skipped_align,
            rows_strict_accepted=pending_aligned_strict,
            rows_rejected_comparator=rejected,
            rows_already_in_erqa=already_erqa,
            new_erqa_payloads=new_erqa,
            wrong_payloads=wrong,
            alignment_debug_rows=ad_rows,
            reason="one_or_more_alignment_skips",
            structured_debug_rows=structured_debug_rows,
            truth_audit_rows=truth_audit_rows,
            preview_candidate_rows=preview_candidate_rows,
        )

    # All pending rows aligned; check strict coverage for pending
    if rejected > 0:
        return AyahBatchResult(
            decision=AyahDecision.FAIL_COMPARATOR,
            surah=surah,
            ayah=ayah,
            rows_total=rows_total,
            rows_skipped_alignment=0,
            rows_strict_accepted=pending_aligned_strict,
            rows_rejected_comparator=rejected,
            rows_already_in_erqa=already_erqa,
            new_erqa_payloads=new_erqa,
            wrong_payloads=wrong,
            alignment_debug_rows=ad_rows,
            reason="comparator_rejected_one_or_more_rows",
            structured_debug_rows=structured_debug_rows,
            truth_audit_rows=truth_audit_rows,
            preview_candidate_rows=preview_candidate_rows,
        )

    if pending_need_n != pending_aligned_strict:
        return AyahBatchResult(
            decision=AyahDecision.REVIEW_NEEDED,
            surah=surah,
            ayah=ayah,
            rows_total=rows_total,
            rows_skipped_alignment=0,
            rows_strict_accepted=pending_aligned_strict,
            rows_rejected_comparator=rejected,
            rows_already_in_erqa=already_erqa,
            new_erqa_payloads=new_erqa,
            wrong_payloads=wrong,
            alignment_debug_rows=ad_rows,
            reason="row_count_mismatch_internal",
            structured_debug_rows=structured_debug_rows,
            truth_audit_rows=truth_audit_rows,
            preview_candidate_rows=preview_candidate_rows,
        )

    return AyahBatchResult(
        decision=AyahDecision.PASS_STRICT,
        surah=surah,
        ayah=ayah,
        rows_total=rows_total,
        rows_skipped_alignment=0,
        rows_strict_accepted=pending_aligned_strict,
        rows_rejected_comparator=0,
        rows_already_in_erqa=already_erqa,
        new_erqa_payloads=new_erqa,
        wrong_payloads=[],
        alignment_debug_rows=ad_rows,
        reason="all_pending_rows_strict_or_erqa",
        structured_debug_rows=structured_debug_rows,
        truth_audit_rows=truth_audit_rows,
        preview_candidate_rows=preview_candidate_rows,
    )
