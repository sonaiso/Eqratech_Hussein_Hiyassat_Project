# -*- coding: utf-8 -*-
import csv
from pathlib import Path

from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision, normalize_i3rab_for_exact_compare
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows
from orchestrator.quran_gold.truth_audit import (
    aggregate_batch_28_5_counters,
    build_truth_audit_row,
    write_truth_audit_csv,
)


def test_normalize_strips_decorative_quotes():
    a = '"" الْحَمْدُ ""'
    b = "الْحَمْدُ"
    assert normalize_i3rab_for_exact_compare(a) == normalize_i3rab_for_exact_compare(b)


def test_real_corpus_52_1_pass_strict():
    root = Path(__file__).resolve().parents[2]
    gold = str(root / "data" / "quran_i3rab.csv")
    indexed = list(enumerate(_read_gold_rows(gold)))
    from orchestrator.quran_gold.ayah_loader import get_ayah_text, default_quran_text_path

    at = get_ayah_text(52, 1, text_path=default_quran_text_path())
    assert at
    res = evaluate_ayah(52, 1, indexed, set(), at)
    assert res.decision == AyahDecision.PASS_STRICT
    assert len(res.new_erqa_payloads) == 1


def test_truth_audit_aggregate():
    rows = [
        {
            "audit_bucket": "GOLD_LONG_PROSE_L17_UNAVAILABLE",
            "potentially_unlockable_without_l17_core": "false",
            "comparator_tier_current": "mismatch",
        },
        {
            "audit_bucket": "ACCEPTED_STRICT_TIER",
            "comparator_tier_current": "strict_structural_match",
        },
    ]
    c = aggregate_batch_28_5_counters(rows)
    assert c["rows_blocked_by_l17_core"] >= 1
    assert c["candidate_real_accept_rows"] >= 1


def test_truth_audit_csv_roundtrip(tmp_path):
    from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot

    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17=None,
        l11_i3rab_text="اسْمٌ مَجْرُورٌ",
        primary_label="L11_only",
    )
    dec = MatchDecision(
        tier=ComparatorTier.MISMATCH,
        confidence=0.0,
        analyzer_source="L11",
        system_i3rab_display="x",
        notes="no_match",
    )
    row = build_truth_audit_row(
        surah=1,
        ayah=1,
        ayah_word_index=0,
        word="w",
        gold_i3rab="test",
        snap=snap,
        dec=dec,
        aligned=True,
        already_erqa=False,
    )
    p = tmp_path / "t.csv"
    write_truth_audit_csv(p, [row])
    with open(p, encoding="utf-8-sig") as f:
        r = csv.DictReader(f)
        assert next(r)["audit_bucket"]
