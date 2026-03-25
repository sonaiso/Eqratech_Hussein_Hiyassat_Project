# -*- coding: utf-8 -*-
"""Master execution Patches 10–12 — L17 B40/B41/B42 (nominal خبر, ظرف surfaces, fused PP majrur)."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def _l17_by_surface(text: str) -> dict[str, tuple[str, str]]:
    r = run_pipeline(text)
    lo = r.get("layer_outputs") or {}
    tr = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}
    out: dict[str, tuple[str, str]] = {}
    for t in tr.get("token_reasoning") or []:
        s = (t.get("surface") or "").strip()
        out[s] = ((t.get("syntactic_role") or "").strip(), (t.get("status") or "").strip())
    return out


def test_patch10_b40_pointer_la_rayb_huda_khabar():
    """2:2 opening — ذَلِكَ الْكِتَابُ لَا رَيْبَ فِيهِ هُدًى → هُدًى خبر."""
    rows = _read_gold_rows("data/quran_i3rab.csv")
    indexed = list(enumerate(rows))
    text = reconstruct_ayah_text_from_indexed(indexed, 2, 2)
    m = _l17_by_surface(text)
    assert m["هُدًى"][0] == "خبر"
    assert m["هُدًى"][1] == "resolved"


def test_patch11_b41_waith_and_qabl():
    """B41: وَإِذْ → ظرف زمان; مِنْ قَبْلُ cluster — قَبْلُ ظرف (not stray فاعل)."""
    rows = _read_gold_rows("data/quran_i3rab.csv")
    indexed = list(enumerate(rows))
    text = reconstruct_ayah_text_from_indexed(indexed, 2, 30)
    m = _l17_by_surface(text)
    assert m["وَإِذْ"][0] == "ظرف زمان"

    text25 = reconstruct_ayah_text_from_indexed(indexed, 2, 25)
    m25 = _l17_by_surface(text25)
    assert m25["قَبْلُ"][0] == "ظرف زمان"


def test_patch12_b42_lil_muttaqin():
    """2:2 trailing للمتقين — اسم مجرور when fused PP surface."""
    rows = _read_gold_rows("data/quran_i3rab.csv")
    indexed = list(enumerate(rows))
    text = reconstruct_ayah_text_from_indexed(indexed, 2, 2)
    m = _l17_by_surface(text)
    assert m["لِلْمُتَّقِينَ"][0] == "اسم مجرور"
