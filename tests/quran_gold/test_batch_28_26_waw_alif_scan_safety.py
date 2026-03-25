# -*- coding: utf-8 -*-
"""Batch 28.26 — terminal و+ا plural/imperative verb shape excluded from post-verbal nominal scans (extends 28.25)."""

from __future__ import annotations

from orchestrator.dependency_syntax.builder import (
    _has_plural_imperative_verb_terminal_waw_alif_shape,
)
from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_gold_rows
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def test_b28_26_waw_alif_shape_detects_plural_verb_surface():
    assert _has_plural_imperative_verb_terminal_waw_alif_shape("خَلَوْا") is True
    assert _has_plural_imperative_verb_terminal_waw_alif_shape("كَفَرُوا") is True


def test_b28_26_waw_alif_does_not_match_accusative_or_marfuu_noun():
    """28.23 negatives — must stay noun-like for attachment rules."""
    assert _has_plural_imperative_verb_terminal_waw_alif_shape("عَمْرًا") is False
    assert _has_plural_imperative_verb_terminal_waw_alif_shape("الْحَقُّ") is False


def test_b28_26_quranic_2_14_khalaw_no_false_obj_on_fael_token():
    """2:14 — gold marks خَلَوْا as fael; Stage15 must not attach OBJ to that token (E2 pollution)."""
    indexed = _read_gold_rows("data/quran_i3rab.csv")
    rows_ayah = [r for r in indexed if r.surah == 2 and r.ayah == 14]
    rows_ayah.sort(key=lambda r: r.index_in_ayah)
    text = reconstruct_ayah_text_from_gold_rows(rows_ayah)
    r = run_pipeline(text)
    links = ((r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}).get("dependency_links") or []
    assert not any(
        l.get("dependent_id") == "7" and l.get("relation") == "OBJ" for l in links
    )


def test_b28_25_regression_accusative_object_unchanged():
    r = run_pipeline("ضَرَبَ عَمْرًا")
    links = ((r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}).get("dependency_links") or []
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "OBJ"
        for l in links
    )
