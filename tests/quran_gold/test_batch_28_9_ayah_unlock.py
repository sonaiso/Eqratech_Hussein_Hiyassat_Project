# -*- coding: utf-8 -*-
"""Batch 28.9 — ayah unlock ranker (diagnostic only)."""

from orchestrator.quran_gold.ayah_batch_runner import AyahDecision
from orchestrator.quran_gold import ayah_unlock_ranker as u
from orchestrator.quran_gold.ayah_unlock_ranker import (
    AYAH_UNLOCK_ALIGNMENT_BLOCKED,
    AYAH_UNLOCK_CORE_BLOCKED,
    AYAH_UNLOCK_NEAR_PASS_1,
    AYAH_UNLOCK_NEAR_PASS_2,
    AYAH_UNLOCK_PASS_STRICT,
    AYAH_UNLOCK_TRUE_CONFLICT,
)


def _strict_ok():
    return {"audit_bucket": "ACCEPTED_STRICT_TIER", "ayah_word_index": 0, "word": "a"}


def _block_conflict(wi: int):
    return {
        "audit_bucket": "GOLD_LONG_PROSE_L11_CONFLICT",
        "ayah_word_index": wi,
        "word": f"w{wi}",
        "potentially_unlockable_without_l17_core": "false",
    }


def _block_core(wi: int):
    return {
        "audit_bucket": "GOLD_LONG_PROSE_L17_UNAVAILABLE",
        "ayah_word_index": wi,
        "word": f"c{wi}",
        "potentially_unlockable_without_l17_core": "false",
    }


def test_near_pass_one_blocker():
    rows = [_strict_ok(), _block_conflict(1)]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.FAIL_COMPARATOR, rows)
    assert st == AYAH_UNLOCK_NEAR_PASS_1


def test_near_pass_two_blockers():
    rows = [_strict_ok(), _block_conflict(1), _block_conflict(2)]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.FAIL_COMPARATOR, rows)
    assert st == AYAH_UNLOCK_NEAR_PASS_2


def test_alignment_blocked():
    rows = [{"audit_bucket": "ALIGNMENT_FAILED", "ayah_word_index": 0, "word": "x"}]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.FAIL_ALIGNMENT, rows)
    assert st == AYAH_UNLOCK_ALIGNMENT_BLOCKED


def test_core_blocked_dominant():
    rows = [
        _block_core(0),
        _block_core(1),
        _block_core(2),
        _block_conflict(3),
    ]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.FAIL_COMPARATOR, rows)
    assert st == AYAH_UNLOCK_CORE_BLOCKED


def test_true_conflict_dominant():
    rows = [_block_conflict(i) for i in range(4)]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.FAIL_COMPARATOR, rows)
    assert st == AYAH_UNLOCK_TRUE_CONFLICT


def test_pass_strict():
    rows = [_strict_ok(), _strict_ok()]
    st, _ = u.classify_ayah_unlock_status(AyahDecision.PASS_STRICT, rows)
    assert st == AYAH_UNLOCK_PASS_STRICT


def test_unlock_preview_trapped_strict(tmp_path):
    from orchestrator.quran_gold.comparator import ComparatorTier

    structured = [
        {
            "ayah_word_index": 0,
            "word": "x",
            "comparator_tier": ComparatorTier.STRICT_STRUCTURAL_MATCH.value,
            "strict_acceptance_eligible": "true",
        }
    ]
    truth = [
        {
            "audit_bucket": "ACCEPTED_STRICT_TIER",
            "ayah_word_index": 0,
            "word": "x",
            "potentially_unlockable_without_l17_core": "true",
        }
    ]
    rows = u.build_unlock_preview_rows(1, 1, AyahDecision.FAIL_COMPARATOR, truth, structured, {0: 5})
    assert len(rows) >= 1
    assert rows[0].get("currently_trapped_by_ayah") == "true"


def test_write_csv_generates_files(tmp_path):
    p = tmp_path / "t.csv"
    u.write_csv(
        p,
        u.BLOCKER_RANKING_FIELDS,
        [
            {
                "surah": 1,
                "ayah": 1,
                "ayah_status": "NEAR_PASS_1",
                "blocker_row_count": "1",
                "blocker_row_indexes": "0",
                "blocker_words": "a",
                "unlockable_now_count": "0",
                "requires_core_count": "0",
                "true_conflict_count": "1",
                "alignment_issue_count": "0",
                "quarantine_only_count": "0",
                "would_ayah_pass_if_fixed": "yes_if_1_row_strict",
                "reason_summary": "test",
            }
        ],
    )
    assert p.is_file()
    txt = p.read_text(encoding="utf-8-sig")
    assert "NEAR_PASS_1" in txt
