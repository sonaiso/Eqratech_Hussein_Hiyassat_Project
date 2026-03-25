# -*- coding: utf-8 -*-
"""Master Execution Patch 13 — gold **particle**/**darf** vs L17 **noun**/**ظرف زمان** (comparator family bridge)."""

from __future__ import annotations

import csv

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def _gold_2_11_waitha() -> str:
    with open("data/quran_i3rab.csv", newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            if r["surah"] == "2" and r["ayah"] == "11" and r["word"].startswith("وَإِذَا"):
                return r["i3rab"]
    raise RuntimeError("missing gold row")


def test_patch13_particle_darf_vs_l17_noun_zarf_strict():
    gold = _gold_2_11_waitha()
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="وَإِذَا",
        l17={
            "status": "resolved",
            "confidence": 0.78,
            "syntactic_role": "ظرف زمان",
            "i3rab_case_or_mood": "منصوب",
            "marker": "الفتحة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH, d.notes
    assert strict_acceptance_eligible(d)
