# -*- coding: utf-8 -*-
"""Batch 28.28 — comparator bridge: gold fael on verb tokens vs L17 «فعل» + مبني case bucket."""

from __future__ import annotations

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def test_b28_28_strict_when_gold_fael_verb_and_l17_fial_mabni():
    """Quranic gold pattern (e.g. قَالُوا row): gold role fael + verb family; L17 labels finite verb «فعل»."""
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


def test_b28_28_fael_bridge_does_not_accept_mafool_gold_with_fial_label():
    """Genuine role mismatch: gold مفعول به vs L17 فعل — still not strict."""
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


def test_exec_patch4_strict_gold_fael_verb_vs_l17_fael_np():
    """Patch 4: gold **fael** + **verb** row; L17 «فاعل» (noun family) — same slot, different display."""
    gold = (
        'فِعْلٌ مُضَارِعٌ مَجْزُومٌ وَعَلَامَةُ جَزْمِهِ حَذْفُ النُّونِ لِأَنَّهُ مِنَ الْأَفْعَالِ الْخَمْسَةِ، وَ"" وَاوُ الْجَمَاعَةِ "" '
        "ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ رَفْعٍ فَاعِلٌ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="تَجْعَلُوا",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "فاعل",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "الضمة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes


def test_exec_patch4_strict_gold_naib_fael_verb_vs_l17_naib_np():
    gold = (
        'فِعْلٌ مُضَارِعٌ مَجْزُومٌ وَعَلَامَةُ جَزْمِهِ حَذْفُ النُّونِ لِأَنَّهُ مِنَ الْأَفْعَالِ الْخَمْسَةِ، وَ"" وَاوُ الْجَمَاعَةِ "" '
        "ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ رَفْعٍ فَاعِلٌ، وَالْجُمْلَةُ فِي مَحَلِّ رَفْعٍ نَائِبُ فَاعِلٍ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="تُفْسِدُوا",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "نائب فاعل",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "الضمة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes


def test_exec_patch4_reject_mafool_bih_gold_with_l17_fael_np():
    """فَزَادَهُمُ-style: gold **مفعول به** must not strict-match L17 **فاعل**."""
    gold = (
        '"" هَاءُ الْغَائِبِ "" ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ الْمُقَدَّرِ لِالْتِقَاءِ السَّاكِنَيْنِ فِي مَحَلِّ نَصْبٍ مَفْعُولٌ بِهِ.'
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="فَزَادَهُمُ",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "فاعل",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "الضمة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.MISMATCH


def test_exec_patch4_reject_ism_in_l17_on_kana_row():
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="كُنْتُمْ",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "اسم إن",
            "i3rab_case_or_mood": "منصوب",
            "marker": "الفتحة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    gold = (
        'فِعْلٌ مَاضٍ نَاسِخٌ مَبْنِيٌّ عَلَى السُّكُونِ لِاتِّصَالِهِ بِتَاءِ الْفَاعِلِ فِي مَحَلِّ جَزْمٍ فِعْلُ الشَّرْطِ، وَ"" تَاءُ الْفَاعِلِ "" '
        "ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ رَفْعٍ اسْمُ كَانَ."
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.MISMATCH


def test_exec_patch5_strict_sila_mawsul_verb_vs_l17_finite_fial():
    """Patch 5: gold **sila_mawsul** + **verb**; L17 finite **فعل** (صلة) — role code bridge."""
    gold = (
        'فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى السُّكُونِ لِاتِّصَالِهِ بِتَاءِ الْفَاعِلِ، وَ"" تَاءُ الْفَاعِلِ "" '
        "ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى الْفَتْحِ فِي مَحَلِّ رَفْعٍ فَاعِلٌ، وَالْجُمْلَةُ صِلَةُ الْمَوْصُولِ لَا مَحَلَّ لَهَا مِنَ الْإِعْرَابِ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="أَنْعَمْتَ",
        l17={
            "status": "resolved",
            "confidence": 0.92,
            "syntactic_role": "فعل",
            "i3rab_case_or_mood": "مبني على السكون لاتصاله بتاء الفاعل",
            "marker": "الفتح",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
