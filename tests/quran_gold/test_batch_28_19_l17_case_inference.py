# -*- coding: utf-8 -*-
"""Batch 28.19: _infer_case_bucket_from_l17 — مبني particles vs false «جر» genitive; fused لِل… genitive."""

from __future__ import annotations

from orchestrator.quran_gold.comparator import _infer_case_bucket_from_l17


def test_mabni_harf_jar_maps_to_built_not_false_genitive():
    """«حرف جر» must not trigger genitive via substring «جر» alone (was case_bucket_mismatch vs gold مبني)."""
    l17 = {
        "status": "resolved",
        "confidence": 0.9,
        "syntactic_role": "حرف جر",
        "i3rab_case_or_mood": "مبني",
        "marker": "—",
    }
    assert _infer_case_bucket_from_l17(l17) == "built"


def test_b28_10_fused_lil_maps_to_genitive():
    """Batch 28.10 لِل… — gold expects genitive اسم analysis, not «built»."""
    l17 = {
        "status": "resolved",
        "confidence": 0.9,
        "syntactic_role": "حرف جر",
        "i3rab_case_or_mood": "مبني",
        "marker": "—",
        "gold_rule_refs": ["B28_10_LAM_AL_FUSED"],
        "reasoning_steps": ["Batch 28.10: fused لام+الْ+اسم (لل…) as single-surface حرف جر"],
    }
    assert _infer_case_bucket_from_l17(l17) == "genitive"


def test_majrur_still_genitive():
    l17 = {
        "status": "resolved",
        "syntactic_role": "اسم مجرور",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
    }
    assert _infer_case_bucket_from_l17(l17) == "genitive"


def test_patch18_ism_majrur_genitive_despite_mabni_in_reasoning_steps():
    """Patch 18: fused PP cells — «مبني» in evidence must not beat primary **اسم مجرور** (was **built** → mismatch)."""
    l17 = {
        "status": "resolved",
        "confidence": 0.85,
        "syntactic_role": "اسم مجرور",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
        "reasoning_steps": [
            'الْوَاوُ "" حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ',
            "Stage15:JAR_MAJROR",
        ],
    }
    assert _infer_case_bucket_from_l17(l17) == "genitive"
