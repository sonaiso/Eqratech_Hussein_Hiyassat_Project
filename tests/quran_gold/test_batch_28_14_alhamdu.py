# -*- coding: utf-8 -*-
"""Batch 28.14 — Fatiha 1:2 الْحَمْدُ as مبتدأ via Stage15 PRED head (L17 B28_14)."""

from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows
from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
from orchestrator.quran_gold.comparator import compare_token_conservative, strict_acceptance_eligible
from orchestrator.quran_gold.analyzer_extract import extract_snapshots, get_token_surfaces
from orchestrator.quran_gold.alignment import align_gold_words_to_pipeline_tokens
from orchestrator import run_pipeline


def _indexed():
    return list(enumerate(_read_gold_rows("data/quran_i3rab.csv")))


def test_alhamdu_token_strict_acceptance():
    indexed = _indexed()
    ayah_text = reconstruct_ayah_text_from_indexed(indexed, 1, 2)
    pl = run_pipeline(ayah_text, source={"entrypoint": "test_b28_14", "surah": 1, "ayah": 2})
    snaps = extract_snapshots(pl)
    tsurf = get_token_surfaces(pl)
    rows = sorted([(gi, r) for gi, r in indexed if r.surah == 1 and r.ayah == 2], key=lambda x: x[1].index_in_ayah)
    gold_words = [r.word for _, r in rows]
    rich = align_gold_words_to_pipeline_tokens(gold_words, tsurf, repair_pass=0)
    # First word of 1:2 is الْحَمْدُ (diacritics may sit between root letters; use index).
    hamdu = next((i for i, (_, r) in enumerate(rows) if r.index_in_ayah == 0), None)
    assert hamdu is not None
    rr = rich[hamdu]
    assert rr.token_index is not None
    snap = snaps[rr.token_index]
    assert snap.l17 is not None
    assert "مبتدأ" in (snap.l17.get("syntactic_role") or "")
    assert (snap.l17.get("status") or "") == "resolved"
    dec = compare_token_conservative(rows[hamdu][1].i3rab, snap, repair_pass=0)
    assert dec.tier.value == "strict_structural_match"
    assert strict_acceptance_eligible(dec)


def test_ayah_1_2_pass_strict_dry_run():
    indexed = _indexed()
    ayah_text = reconstruct_ayah_text_from_indexed(indexed, 1, 2)
    res = evaluate_ayah(1, 2, indexed, set(), ayah_text, repair_pass=0)
    assert res.decision == AyahDecision.PASS_STRICT
    assert res.rows_rejected_comparator == 0
    assert len(res.new_erqa_payloads) == 4


def test_1_1_still_pass_strict():
    indexed = _indexed()
    ayah_text = reconstruct_ayah_text_from_indexed(indexed, 1, 1)
    res = evaluate_ayah(1, 1, indexed, set(), ayah_text, repair_pass=0)
    assert res.decision == AyahDecision.PASS_STRICT


def test_1_3_still_pass_strict():
    indexed = _indexed()
    ayah_text = reconstruct_ayah_text_from_indexed(indexed, 1, 3)
    res = evaluate_ayah(1, 3, indexed, set(), ayah_text, repair_pass=0)
    assert res.decision == AyahDecision.PASS_STRICT


def test_strict_acceptance_eligible_unchanged():
    from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision, strict_acceptance_eligible

    d = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="x",
        notes="",
        trace=None,
    )
    assert strict_acceptance_eligible(d) is True
