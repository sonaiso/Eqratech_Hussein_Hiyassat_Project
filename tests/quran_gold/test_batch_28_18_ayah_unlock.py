# -*- coding: utf-8 -*-
"""Batch 28.18: strict-pass unlock for 1:5 (وَإِيَّاكَ) and 2:1 (حُرُوف مُقَطَّعَة)."""

from __future__ import annotations

from pathlib import Path

import pytest

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative
from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed
from orchestrator.quran_gold.gold_prose_parser import parse_gold_i3rab_prose
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def test_gold_prose_muqatta_huruf_alif_lam_mim():
    s = "حُرُوفٌ مُقَطَّعَةٌ لِلدَّلَالَةِ عَلَى إِعْجَازِ الْقُرْآنِ."
    g = parse_gold_i3rab_prose(s)
    assert g.gram_family == "particle"
    assert g.syntactic_role == "muqatta_huruf"
    assert g.case_bucket == "built"
    assert g.parser_confidence >= 0.9


def test_gold_prose_harf_mabni_matches_l11_alm():
    g = parse_gold_i3rab_prose("حَرْفٌ مَبْنِيٌّ")
    assert g.syntactic_role == "harf_mabni"
    assert g.gram_family == "particle"
    assert g.case_bucket == "built"


def test_comparator_waw_iyya_particle_gold_vs_motawaf_l17():
    """1:5 — gold lemma begins with واو عطف (particle family) + مفعول به; L17 «معطوف» (Batch 28.17)."""
    gold = (
        '" الْوَاوُ " حَرْفُ عَطْفٍ مَبْنِيٌّ عَلَى الْفَتْحِ، وَ( إِيَّاكَ ) : ضَمِيرٌ مُنْفَصِلٌ مَبْنِيٌّ عَلَى السُّكُونِ '
        "فِي مَحَلِّ نَصْبٍ مَفْعُولٌ بِهِ مُقَدَّمٌ لِلِاخْتِصَاصِ."
    )
    snap = TokenAnalyzerSnapshot(
        token_id="2",
        surface="وَإِيَّاكَ",
        l17={
            "status": "resolved",
            "confidence": 0.88,
            "grammatical_family": "NOUN",
            "syntactic_role": "معطوف",
            "i3rab_case_or_mood": "منصوب",
            "marker": "الفتحة",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    assert d.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH
    assert d.notes == "strict_structured_gold_vs_l17"


@pytest.mark.parametrize(
    "surah,ayah,expected_rows",
    [
        (1, 5, 4),
        (2, 1, 1),
    ],
)
def test_evaluate_ayah_pass_strict_gold_csv(surah: int, ayah: int, expected_rows: int):
    gold_path = Path(__file__).resolve().parents[2] / "data" / "quran_i3rab.csv"
    rows = _read_gold_rows(str(gold_path))
    indexed = list(enumerate(rows))
    ayah_text = reconstruct_ayah_text_from_indexed(indexed, surah, ayah)
    res = evaluate_ayah(surah, ayah, indexed, set(), ayah_text or "", repair_pass=0)
    assert res.decision == AyahDecision.PASS_STRICT
    assert res.rows_total == expected_rows
    assert res.rows_strict_accepted == expected_rows
