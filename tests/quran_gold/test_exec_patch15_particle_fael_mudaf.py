# -*- coding: utf-8 -*-
"""Master Execution Patch 15 — gold **particle**/**fael** (و+imperative+fused واو الجماعة) vs L17 **مضاف**."""

from __future__ import annotations

import csv

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def _gold_2_43_waatoo() -> str:
    with open("data/quran_i3rab.csv", newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            if r["surah"] == "2" and r["ayah"] == "43" and r["word"].startswith("وَآتُوا"):
                return r["i3rab"]
    raise RuntimeError("missing gold row")


def test_patch15_particle_fael_vs_l17_mudaf_strict():
    gold = _gold_2_43_waatoo()
    snap = TokenAnalyzerSnapshot(
        token_id="2",
        surface="وَآتُوا",
        l17={
            "status": "resolved",
            "confidence": 0.82,
            "syntactic_role": "مضاف",
            "i3rab_case_or_mood": "مجرور",
            "marker": "الكسرة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)
