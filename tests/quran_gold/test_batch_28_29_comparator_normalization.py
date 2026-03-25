# -*- coding: utf-8 -*-
"""Batch 28.29 — comparator: particle مبني case bridge + gold_parser_limit partial tier."""

from __future__ import annotations

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def test_b28_29_strict_particle_harf_jar_gold_nominative_vs_l17_built():
    """Pattern A: gold particle + محل رفع (nominative) vs L17 حرف جر + مبني — normalization bridge, not case_bucket_mismatch."""
    gold = (
        "حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ، وَشِبْهُ الْجُمْلَةِ فِي مَحَلِّ رَفْعٍ مَرْفُوعٌ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="بِ",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "حرف جر",
            "i3rab_case_or_mood": "مبني على الفتح",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_execution_patch1_harf_jar_gold_genitive_from_majrur_mention_vs_l17_built():
    """Gold cell mentions مجرور (parser → genitive) alongside حرف جر مبني; L17 حرف جر + مبني → strict, not case_bucket_mismatch."""
    gold = "حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ، وَمَا مَجْرُورٌ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="بِمَا",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "حرف جر",
            "i3rab_case_or_mood": "مبني على الكسر",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_b28_29_strict_particle_harf_jar_gold_accusative_vs_l17_built():
    """Pattern A (accusative gold): same مبني bridge for particle|particle."""
    gold = "حَرْفُ جَرٍّ مَبْنِيٌّ، وَشِبْهُ الْجُمْلَةِ فِي مَحَلِّ نَصْبٍ مَنْصُوبٌ."
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="بِ",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "حرف جر",
            "i3rab_case_or_mood": "مبني",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes


def test_b28_29_partial_gold_parser_limit_sparse_gold_high_l17():
    """Pattern B: gold prose leaves no resolved role (low parser confidence); L17 resolved — partial gold_parser_limit, not strict."""
    gold = "ذِكْرٌ عَامٌّ بِلَا تَفْصِيلٍ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="ذِكْرًا",
        l17={
            "status": "resolved",
            "confidence": 0.8,
            "syntactic_role": "مبتدأ",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "الضمة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.PARTIAL_STRUCTURED_MATCH, d.notes
    assert d.notes == "gold_parser_limit"
    assert not strict_acceptance_eligible(d)
    assert d.trace and d.trace.get("structured_gate") == "gold_parser_limit"


def test_b28_29_sparse_gold_never_strict_even_with_strong_l17():
    """Negative: empty/absent gold role must not be promoted to strict_structural_match."""
    gold = "ذِكْرٌ عَامٌّ بِلَا تَفْصِيلٍ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.99,
            "syntactic_role": "مبتدأ",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier != ComparatorTier.STRICT_STRUCTURAL_MATCH


def test_b28_29_gold_parser_limit_requires_l17_confidence_floor():
    """Negative: gold_parser_limit path requires L17 confidence >= 0.75."""
    gold = "ذِكْرٌ عَامٌّ بِلَا تَفْصِيلٍ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.5,
            "syntactic_role": "مبتدأ",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.MISMATCH
    assert d.notes == "no_match"


def test_b28_28_regression_fael_verb_fial_mabni_still_strict():
    """Regression: Batch 28.28 fael + verb + finite فعل + مبني remains strict."""
    gold = (
        'فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الضَّمِّ لِاتِّصَالِهِ بِوَاوِ الْجَمَاعَةِ جَوَابُ الشَّرْطِ، وَ" وَاوُ الْجَمَاعَةِ " '
        "ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ رَفْعٍ فَاعِلٌ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="4",
        surface="قَالُوا",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "فعل",
            "i3rab_case_or_mood": "مبني على الضم لاتصاله بواو الجماعة",
            "marker": "السكون",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_b28_28_regression_mafool_vs_fial_still_mismatch():
    """Regression: role mismatch (مفعول به vs فعل) still not strict."""
    gold = "مَفْعُولٌ بِهٖ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "فعل",
            "i3rab_case_or_mood": "مبني",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.MISMATCH
    assert not strict_acceptance_eligible(d)
