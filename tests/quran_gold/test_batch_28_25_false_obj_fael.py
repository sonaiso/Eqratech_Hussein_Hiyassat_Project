# -*- coding: utf-8 -*-
"""Batch 28.25 — Stage 15: exclude finite-verb surfaces from post-verbal nominal argument scan (false OBJ vs gold fael)."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_gold_rows
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def _links_for_ayah(surah: int, ayah: int):
    indexed = _read_gold_rows("data/quran_i3rab.csv")
    rows_ayah = [r for r in indexed if r.surah == surah and r.ayah == ayah]
    rows_ayah.sort(key=lambda r: r.index_in_ayah)
    text = reconstruct_ayah_text_from_gold_rows(rows_ayah)
    r = run_pipeline(text)
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    return dsb.get("dependency_links") or [], rows_ayah


def test_b28_25_qala_not_obj_of_prior_verb_2_33():
    """
    Positive: قَالَ (finite past) must not fill a nominal ``second argument'' slot → OBJ to a prior verb.
    Gold marks this token as fael in the CSV; mis-linking was Pass_E2_strong_verb_local_obj.
    """
    links, _ = _links_for_ayah(2, 33)
    assert not any(
        l.get("head_id") == "5"
        and l.get("dependent_id") == "7"
        and l.get("relation") == "OBJ"
        for l in links
    )


def test_b28_25_regression_28_23_accusative_object_still_obj():
    """28.23: lone accusative object after verb — still OBJ (finite-surface heuristic must not fire)."""
    r = run_pipeline("ضَرَبَ عَمْرًا")
    links = ((r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}).get("dependency_links") or []
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "OBJ"
        for l in links
    )


def test_b28_25_regression_28_23_marfuu_subject_still_subj():
    """28.23: definite marfūʿ subject — still SUBJ."""
    r = run_pipeline("ظَهَرَ الْحَقُّ")
    links = ((r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}).get("dependency_links") or []
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "SUBJ"
        for l in links
    )


def test_b28_24_locality_map_still_builds_after_28_25():
    """28.24: clause locality map still available (integration smoke)."""
    from orchestrator.clause_locality import build_clause_locality_token_map

    r = run_pipeline("إِنَّ اللَّهَ غَفُورٌ رَحِيمٌ")
    m = build_clause_locality_token_map(r["layer_outputs"])
    assert isinstance(m, dict) and len(m) >= 1
