# -*- coding: utf-8 -*-
"""Execution Patch 2 — harf_jar fused lam/bāʾ/ilá/min-mā cluster vs L17 noun/verb (allowlisted surfaces)."""

from __future__ import annotations

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def test_patch2_wamima_mafool_vs_gold_harf_jar_strict():
    """2:3 وَمِمَّا — gold whole-token **harf_jar**; L17 **مفعول به** (fused cluster)."""
    gold = (
        '" الْوَاوُ " حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ، وَ( مِنْ ) : حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ، '
        'وَ( مَا ) : اسْمٌ مَوْصُولٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ جَرٍّ بِالْحَرْفِ، وَشِبْهُ الْجُمْلَةِ مُتَعَلِّقٌ بِـ( يُنْفِقُونَ ) :.'
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="وَمِمَّا",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "مفعول به",
            "i3rab_case_or_mood": "منصوب",
            "marker": "الفتحة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)


def test_patch2_walahum_finite_misparse_strict():
    """2:7 وَلَهُمْ — gold **harf_jar**; L17 mislabels cluster as finite **فعل** + مبني."""
    gold = (
        '" الْوَاوُ " حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ، وَ" اللَّامُ " حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ، '
        'و" هَاءُ الْغَائِبِ " ضَمِيرٌ مُتَّصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ فِي مَحَلِّ جَرٍّ بِالْحَرْفِ.'
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="وَلَهُمْ",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "فعل مضارع",
            "i3rab_case_or_mood": "مبني على الفتح لاتصاله بواو الجماعة",
            "marker": "الفتح",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes


def test_patch2_jannat_harf_jar_spurious_stays_mismatch():
    """2:25 جَنَّاتٍ — gold **harf_jar** from **اسم أنّ** prose; must not bridge to strict."""
    gold = (
        "اسْمُ ( أَنَّ ) : مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْكَسْرَةُ الظَّاهِرَةُ لِأَنَّهُ جَمْعُ مُؤَنَّثٍ سَالِمٌ، "
        "وَالْمَصْدَرُ الْمُؤَوَّلُ مِنْ أَنَّ وَمَعْمُولَيْهَا مَجْرُورٌ بِحَرْفِ جَرٍّ مَحْذُوفٍ وَالتَّقْدِيرُ: بِأَنَّ لَهُمْ جَنَّاتٍ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="جَنَّاتٍ",
        l17={
            "status": "resolved",
            "confidence": 0.85,
            "syntactic_role": "فعل",
            "i3rab_case_or_mood": "مبني على الفتح",
            "marker": "الفتح",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.MISMATCH
    assert not strict_acceptance_eligible(d)
