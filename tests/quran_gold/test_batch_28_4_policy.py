# -*- coding: utf-8 -*-
import csv
from pathlib import Path

from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
from orchestrator.quran_gold.ayah_loader import get_ayah_text
from orchestrator.quran_gold.comparator import ComparatorTier, strict_acceptance_eligible
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def test_tier_partial_not_erqa():
    from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
    from orchestrator.quran_gold.comparator import compare_token_conservative

    gold = "مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ"
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.85,
            "syntactic_role": "نعت",
            "i3rab_case_or_mood": "مرفوع",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    d = compare_token_conservative(gold, snap)
    if d.tier == ComparatorTier.PARTIAL_STRUCTURED_MATCH:
        assert not strict_acceptance_eligible(d)


def test_structured_debug_csv_shape(tmp_path: Path):
    from orchestrator.quran_gold.batch_quarantine import (
        STRUCTURED_DEBUG_FIELDS,
        write_structured_debug_csv,
    )

    p = tmp_path / "sd.csv"
    rows = [
        {
            "surah": 1,
            "ayah": 1,
            "word": "w",
            "gold_i3rab_raw": "x",
            "gold_family": "",
            "gold_role": "mafool_bih",
            "gold_case_bucket": "accusative",
            "gold_marker": "",
            "l17_family": "noun",
            "l17_role": "مفعول به",
            "l17_case_bucket": "accusative",
            "l17_marker": "",
            "comparator_tier": "strict_structural_match",
            "strict_acceptance_eligible": "true",
            "reason": "ok",
            "parser_confidence": "0.8",
            "parser_limitations": "",
            "ayah_word_index": 0,
        }
    ]
    write_structured_debug_csv(p, rows)
    with open(p, encoding="utf-8-sig") as f:
        r = csv.DictReader(f)
        row = next(iter(r))
        assert set(row.keys()) == set(STRUCTURED_DEBUG_FIELDS)


def test_fixture_l11_exact_ayah_pass_strict():
    root = Path(__file__).resolve().parents[2]
    gold_path = root / "tests" / "fixtures" / "quran_i3rab_batch284_l11_exact_smoke.csv"
    rows = _read_gold_rows(str(gold_path))
    indexed = list(enumerate(rows))
    ayah_text = get_ayah_text(1, 1, text_path=str(root / "data" / "quran-uthmani.txt"))
    assert ayah_text
    res = evaluate_ayah(1, 1, indexed, set(), ayah_text, require_strict_comparator=True)
    assert res.decision == AyahDecision.PASS_STRICT
    assert res.rows_strict_accepted == 1
