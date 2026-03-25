# -*- coding: utf-8 -*-
"""Master Execution Patch 7 — gold **particle**/**fael** (fused حرف + imperative) vs L17 finite «فعل»."""

from __future__ import annotations

import csv

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def _gold_2_24_fattaqoo() -> str:
    with open("data/quran_i3rab.csv", newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            if r["surah"] == "2" and r["ayah"] == "24" and r["word"].startswith("فَاتَّقُوا"):
                return r["i3rab"]
    raise RuntimeError("missing gold row")


def test_patch7_particle_fael_vs_l17_finite_verb_strict_and_built_case():
    gold = _gold_2_24_fattaqoo()
    snap = TokenAnalyzerSnapshot(
        token_id="5",
        surface="فَاتَّقُوا",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "syntactic_role": "فعل أمر",
            "i3rab_case_or_mood": "مبني على حذف النون",
            "marker": "السكون",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)
