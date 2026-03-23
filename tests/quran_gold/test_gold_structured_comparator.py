# -*- coding: utf-8 -*-
from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import (
    ComparatorTier,
    compare_token_conservative,
    strict_acceptance_eligible,
)


def test_structured_strict_mafool_bih():
    gold = "مَفْعُولٌ بِهٖ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.92,
            "syntactic_role": "مفعول به",
            "i3rab_case_or_mood": "منصوب",
            "marker": "الفتحة",
        },
        l11_i3rab_text="different prose entirely",
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH
    assert strict_acceptance_eligible(d)
    assert d.trace and "mafool_bih" in (d.trace.get("l17_codes") or "")


def test_family_conflict_mismatch():
    gold = "فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "مبتدأ",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert not strict_acceptance_eligible(d)
