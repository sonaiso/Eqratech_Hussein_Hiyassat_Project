# -*- coding: utf-8 -*-
"""Master Execution Patch 9 — empty gold syntactic_role + bounded parser confidence → partial gold_parser_limit."""

from __future__ import annotations

import csv

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def _gold_1_7_wala() -> str:
    with open("data/quran_i3rab.csv", newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            if r["surah"] == "1" and r["ayah"] == "7" and r["word"].startswith("وَلَا"):
                return r["i3rab"]
    raise RuntimeError("missing gold row")


def test_patch9_family_conflict_particle_empty_gold_role_becomes_gold_parser_limit_partial():
    """1:7 وَلَا — gold particle (no resolved iʿrāb role in cell) vs L17 verb; classify as tooling limit, not hard mismatch."""
    gold = _gold_1_7_wala()
    snap = TokenAnalyzerSnapshot(
        token_id="7",
        surface="وَلَا",
        l17={
            "status": "resolved",
            "confidence": 0.9,
            "syntactic_role": "فعل مضارع",
            "i3rab_case_or_mood": "مجزوم",
            "marker": "السكون",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.PARTIAL_STRUCTURED_MATCH, d.notes
    assert d.notes == "gold_parser_limit"
    assert not strict_acceptance_eligible(d)
    assert d.trace and d.trace.get("structured_gate") == "gold_parser_limit"
