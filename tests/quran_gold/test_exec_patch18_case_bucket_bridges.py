# -*- coding: utf-8 -*-
"""Patch 18 — narrow comparator bridges for `case_bucket_mismatch` (Batch 18 execution)."""

from __future__ import annotations

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def test_patch18_mudaf_ilaih_gold_nominative_vs_l17_genitive_strict():
    """**2:17** الَّذِي-style: gold nominative bucket + L17 مضاف إليه + genitive (سُكُون/كسرة display)."""
    gold = (
        "اسْمٌ مَوْصُولٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ جَرٍّ مُضَافٌ إِلَيْهِ، "
        "وَشِبْهُ الْجُمْلَةِ فِي مَحَلِّ رَفْعٍ خَبَرُ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="2",
        surface="الَّذِي",
        l17={
            "status": "resolved",
            "confidence": 0.85,
            "syntactic_role": "مضاف إليه",
            "i3rab_case_or_mood": "مجرور",
            "marker": "الكسرة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_patch18_fael_jussive_gold_vs_mudari_marfuu_l17_strict():
    """**2:33** أَقُلْ-style: gold **مجزوم** vs L17 **فعل مضارع** **مرفوع** (display-only case bucket)."""
    gold = (
        'فِعْلٌ مُضَارِعٌ مَجْزُومٌ وَعَلَامَةُ جَزْمِهِ السُّكُونُ الظَّاهِرُ، وَالْفَاعِلُ ضَمِيرٌ مُسْتَتِرٌ تَقْدِيرُهُ "" أَنَا "".'
    )
    snap = TokenAnalyzerSnapshot(
        token_id="9",
        surface="أَقُلْ",
        l17={
            "status": "resolved",
            "confidence": 0.95,
            "syntactic_role": "فعل مضارع",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "الضمة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_patch18_darf_accusative_gold_vs_l17_built_strict():
    """**2:17** حَوْلَهُ-style: gold **منصوب** vs L17 **ظرف مكان** + مبني-style bucket."""
    gold = (
        "ظَرْفُ مَكَانٍ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ، وَ"
        '"" هَاءُ الْغَائِبِ "" ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى الضَّمِّ فِي مَحَلِّ جَرٍّ مُضَافٌ إِلَيْهِ'
    )
    snap = TokenAnalyzerSnapshot(
        token_id="8",
        surface="حَوْلَهُ",
        l17={
            "status": "resolved",
            "confidence": 0.85,
            "syntactic_role": "ظرف مكان",
            "i3rab_case_or_mood": "مبني",
            "marker": "الفتحة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)
