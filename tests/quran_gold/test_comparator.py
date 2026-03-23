# -*- coding: utf-8 -*-
from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import MatchLevel, compare_token_conservative, erqa_eligible


def test_exact_l11_match():
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17=None,
        l11_i3rab_text="goldline",
        primary_label="L11_only",
    )
    d = compare_token_conservative("goldline", snap)
    assert d.level == MatchLevel.EXACT_TEXT
    assert erqa_eligible(d)


def test_structured_l17():
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "مفعول به",
            "i3rab_case_or_mood": "منصوب",
            "marker": "—",
        },
        l11_i3rab_text=None,
        primary_label="L17_resolved",
    )
    gold = "مَفْعُولٌ بِهٖ مَنْصُوبٌ"
    d = compare_token_conservative(gold, snap)
    assert erqa_eligible(d) or d.level == MatchLevel.STRUCTURED_ROLE


