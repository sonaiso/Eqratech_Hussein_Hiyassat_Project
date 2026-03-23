# -*- coding: utf-8 -*-
"""Batch 28.12 — accepted erqa row serialization is decision-faithful."""

from orchestrator.quran_gold.accepted_row_serializer import (
    _letters_only,
    build_accepted_erqa_row,
    canonical_system_i3rab_for_acceptance,
    raw_prose_contradicts_accepted_structure,
    render_structured_i3rab_ar,
    validate_accepted_row_invariants,
)
from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision, _structured_trace
from orchestrator.quran_gold.gold_prose_parser import effective_gold_structure_for_compare


def test_render_mudaf_ilayh_template():
    s = render_structured_i3rab_ar(
        syntactic_role="مضاف إليه",
        i3rab_case_or_mood="مجرور",
        marker="الكسرة",
        governing_factor="المضاف",
    )
    assert "مُضَافٌ" in s or "مضاف" in s
    assert "خبر" not in s


def test_strict_l17_row_not_khabar_in_system_column():
    gold = "اسْمُ الْجَلَالَةِ مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l17 = {
        "syntactic_role": "مضاف إليه",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
        "governing_factor": "المضاف",
        "confidence": 0.9,
        "status": "resolved",
    }
    gs = effective_gold_structure_for_compare(gold)
    tr = _structured_trace(gs, l17, {"structured_gate": "strict", "reason": "structured_ok"})
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="خَبَرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ",
        notes="strict_structured_gold_vs_l17",
        trace=tr,
    )
    snap = TokenAnalyzerSnapshot(
        token_id="1",
        surface="اللَّهِ",
        l17=l17,
        l11_i3rab_text=dec.system_i3rab_display,
        primary_label="L17_resolved",
    )
    row = build_accepted_erqa_row(
        surah=1,
        ayah=1,
        word="اللَّهِ",
        gold_i3rab=gold,
        ayah_word_index=1,
        dec=dec,
        snap=snap,
    )
    assert "خبر" not in (row["system_i3rab"] or "")
    assert "مرفوع" not in (row["system_i3rab"] or "")
    assert "مضاف" in (row["system_i3rab"] or "") or "مُضَاف" in (row["system_i3rab"] or "")
    assert "خبر" in _letters_only(row["raw_system_i3rab_before_hardening"] or "")
    assert row["accepted_case_bucket"] == "genitive"
    assert row["accepted_structured_signature"] == "mudaf_ilaih"
    assert validate_accepted_row_invariants(row) == []


def test_exact_text_unchanged():
    dec = MatchDecision(
        tier=ComparatorTier.EXACT_TEXT_MATCH,
        confidence=0.95,
        analyzer_source="L11",
        system_i3rab_display="حَرْفُ جَرٍّ مَبْنِيٌّ",
        notes="exact_l11_vs_gold",
        trace=None,
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="بِسْمِ",
        l17=None,
        l11_i3rab_text=dec.system_i3rab_display,
        primary_label="L11_only",
    )
    can, basis, src = canonical_system_i3rab_for_acceptance(dec, snap, "gold prose")
    assert can == dec.system_i3rab_display
    assert src == "L11_exact_text"


def test_contradiction_detection_khabar_vs_mudaf():
    gold = "اسْمُ الْجَلَالَةِ مُضَافٌ إِلَيْهِ مَجْرُورٌ"
    raw = "خَبَرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ"
    assert raw_prose_contradicts_accepted_structure(raw, gold_i3rab=gold, l17=None) is True


def test_canonical_prefers_l17_when_raw_contradicts():
    gold = "اسْمُ الْجَلَالَةِ مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l17 = {
        "syntactic_role": "مضاف إليه",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
        "governing_factor": "المضاف",
        "confidence": 0.9,
        "status": "resolved",
    }
    gs = effective_gold_structure_for_compare(gold)
    tr = _structured_trace(gs, l17, {})
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="خَبَرٌ مَرْفُوعٌ",
        notes="strict_structured_gold_vs_l17",
        trace=tr,
    )
    snap = TokenAnalyzerSnapshot("1", "اللَّهِ", l17, "خَبَرٌ مَرْفُوعٌ", "L17_resolved")
    can, _, _ = canonical_system_i3rab_for_acceptance(dec, snap, gold)
    assert "خبر" not in can
