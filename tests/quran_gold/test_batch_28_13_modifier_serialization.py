# -*- coding: utf-8 -*-
"""Batch 28.13 — modifier-aware accepted row serialization (naʿt specificity, metadata consistency)."""

from orchestrator.quran_gold.accepted_row_serializer import (
    _letters_only,
    build_accepted_erqa_row,
    canonical_system_i3rab_for_acceptance,
    canonicalize_accepted_metadata,
    normalize_accepted_structured_metadata,
    render_gold_structured_display,
)
from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision, _structured_trace
from orchestrator.quran_gold.gold_prose_parser import effective_gold_structure_for_compare, parse_gold_i3rab_prose
from orchestrator.quran_gold.gold_structured import GoldStructuredI3rab


def test_naat_genitive_renders_as_naat_not_generic_ism():
    gs = parse_gold_i3rab_prose("نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.")
    assert gs.syntactic_role == "naat"
    line = render_gold_structured_display(gs, "نَعْتٌ مَجْرُورٌ …")
    assert "نَعْت" in line or "نعت" in _letters_only(line)
    assert "اسْمٌ" not in line.split("،")[0]  # not leading with generic اسم


def test_naat_second_and_third_from_gold():
    gs = parse_gold_i3rab_prose("نَعْتٌ ثَانٍ مَجْرُورٌ …")
    assert gs.syntactic_role == "naat"
    s2 = render_gold_structured_display(gs, "نَعْتٌ ثَانٍ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ")
    assert "ثَانٍ" in s2 or "ثان" in _letters_only(s2)

    gs3 = parse_gold_i3rab_prose("نَعْتٌ ثَالِثٌ مَجْرُورٌ …")
    s3 = render_gold_structured_display(gs3, "نَعْتٌ ثَالِثٌ مَجْرُورٌ …")
    assert "ثَالِث" in s3 or "ثالث" in _letters_only(s3)


def test_l11_structured_prefers_gold_naat_display():
    gold = "نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l11 = "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    gs = effective_gold_structure_for_compare(gold)
    l17_stub = {"syntactic_role": "", "governing_factor": "", "i3rab_case_or_mood": "", "marker": ""}
    tr = _structured_trace(gs, l17_stub, {"structured_gate": "l11_struct", "reason": "l11_structured_ok"})
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.85,
        analyzer_source="L11_structured",
        system_i3rab_display=l11,
        notes="strict_structured_gold_vs_l11_prose",
        trace=tr,
    )
    snap = TokenAnalyzerSnapshot("t", "الرَّحْمَنِ", None, l11, "L11")
    can, _, src = canonical_system_i3rab_for_acceptance(dec, snap, gold)
    assert src == "L11_structured_parse"
    assert "نَعْت" in can or "نعت" in _letters_only(can)
    assert _letters_only(can).count("اسم") == 0 or "نعت" in _letters_only(can)


def test_mudaf_ilayh_still_renders_mudaf():
    gold = "مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    gs = effective_gold_structure_for_compare(gold)
    s = render_gold_structured_display(gs, gold)
    assert "مُضَاف" in s or "مضاف" in _letters_only(s)


def test_signature_conflict_naat_vs_mudaf_normalized():
    l17 = {
        "syntactic_role": "مضاف إليه",
        "governing_factor": "المضاف",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
    }
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17_structured",
        system_i3rab_display="",
        notes="",
        trace=None,
    )
    can = canonicalize_accepted_metadata(
        canonical_role="naat",
        system_i3rab="نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.",
        gold_i3rab="نَعْتٌ مَجْرُورٌ …",
        l17=l17,
        trace=None,
        dec=dec,
    )
    assert can["accepted_structured_signature"] == "naat"
    assert "mudaf_ilaih" not in can["accepted_structured_signature"]


def test_generic_ism_majrur_when_no_finer_role():
    gs = parse_gold_i3rab_prose("اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.")
    assert gs.syntactic_role == "ism_majrur"
    line = render_gold_structured_display(gs, "اسْمٌ مَجْرُورٌ …")
    assert "اسْمٌ" in line or "اسم" in _letters_only(line)


def test_normalize_metadata_makes_role_and_display_consistent():
    gold = "نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l11 = "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    gs = effective_gold_structure_for_compare(gold)
    l17_stub = {"syntactic_role": "", "governing_factor": "", "i3rab_case_or_mood": "", "marker": ""}
    tr = _structured_trace(gs, l17_stub, {})
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.85,
        analyzer_source="L11_structured",
        system_i3rab_display=l11,
        notes="strict_structured_gold_vs_l11_prose",
        trace=tr,
    )
    snap = TokenAnalyzerSnapshot("t", "w", None, l11, "L11")
    can, basis, src = canonical_system_i3rab_for_acceptance(dec, snap, gold)
    role, disp, _, _ = normalize_accepted_structured_metadata(
        trace=tr,
        l17=None,
        gold_i3rab=gold,
        dec=dec,
        canonical_display=can,
        decision_basis=basis,
        accepted_analysis_source=src,
    )
    assert role == "naat"
    canon = canonicalize_accepted_metadata(
        canonical_role=role,
        system_i3rab=disp,
        gold_i3rab=gold,
        l17=None,
        trace=tr,
        dec=dec,
    )
    assert canon["accepted_structured_signature"] == "naat"
    assert "نعت" in _letters_only(disp) or "نَعْت" in disp


def test_build_row_1_3_style_accepted_fields():
    # Gold CSV 1:3 — الرَّحِيمِ is third naʿt (ثالث), not ثانٍ.
    gold = "نَعْتٌ ثَالِثٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l11 = "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    gs = effective_gold_structure_for_compare(gold)
    l17_stub = {"syntactic_role": "", "governing_factor": "", "i3rab_case_or_mood": "", "marker": ""}
    tr = _structured_trace(gs, l17_stub, {})
    dec = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.85,
        analyzer_source="L11_structured",
        system_i3rab_display=l11,
        notes="strict_structured_gold_vs_l11_prose",
        trace=tr,
    )
    snap = TokenAnalyzerSnapshot("t", "الرَّحِيمِ", None, l11, "L11")
    row = build_accepted_erqa_row(
        surah=1,
        ayah=3,
        word="الرَّحِيمِ",
        gold_i3rab=gold,
        ayah_word_index=1,
        dec=dec,
        snap=snap,
    )
    assert row["accepted_role"] == "naat"
    assert "mudaf_ilaih" not in row["accepted_structured_signature"]
    assert "ثَالِث" in row["system_i3rab"] or "ثالث" in _letters_only(row["system_i3rab"])


def test_gold_structured_stub_for_is_majrur_only():
    gs = GoldStructuredI3rab(
        raw_text="x",
        gram_family="noun",
        gram_family_status="candidate",
        syntactic_role="ism_majrur",
        syntactic_role_status="resolved",
        case_bucket="genitive",
        case_status="resolved",
        marker="kasra",
        marker_status="resolved",
        parser_confidence=0.8,
        limitations=(),
    )
    line = render_gold_structured_display(gs, "اسْمٌ مَجْرُورٌ …")
    assert line  # stock template
