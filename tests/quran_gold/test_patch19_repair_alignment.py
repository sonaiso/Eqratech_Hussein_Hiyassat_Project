# -*- coding: utf-8 -*-
"""Patch 19: repair-pass selection must not overwrite better alignment (infrastructure)."""

from __future__ import annotations

from orchestrator.quran_gold.ayah_batch_runner import (
    AyahBatchResult,
    AyahDecision,
    choose_best_ayah_batch_result_after_repairs,
)


def _mk(
    decision: AyahDecision,
    *,
    skips: int,
    surah: int = 2,
    ayah: int = 264,
    rows_total: int = 10,
) -> AyahBatchResult:
    return AyahBatchResult(
        decision=decision,
        surah=surah,
        ayah=ayah,
        rows_total=rows_total,
        rows_skipped_alignment=skips,
        rows_strict_accepted=0,
        rows_rejected_comparator=0,
        rows_already_in_erqa=0,
        reason="test",
    )


def test_choose_best_prefers_first_pass_strict() -> None:
    worse = _mk(AyahDecision.FAIL_ALIGNMENT, skips=3)
    ok = _mk(AyahDecision.PASS_STRICT, skips=0)
    assert choose_best_ayah_batch_result_after_repairs([worse, ok]) is ok


def test_choose_best_prefers_earliest_min_skips_when_no_pass_strict() -> None:
    good = _mk(AyahDecision.FAIL_COMPARATOR, skips=0)
    bad = _mk(AyahDecision.FAIL_ALIGNMENT, skips=1)
    assert choose_best_ayah_batch_result_after_repairs([good, bad]) is good


def test_choose_best_single_result() -> None:
    only = _mk(AyahDecision.FAIL_ANALYSIS, skips=5)
    assert choose_best_ayah_batch_result_after_repairs([only]) is only
