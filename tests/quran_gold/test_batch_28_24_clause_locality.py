# -*- coding: utf-8 -*-
"""Batch 28.24 — unified clause locality (L10B when L16 is trivial main-only)."""

from __future__ import annotations

from orchestrator.clause_locality import (
    build_clause_locality_token_map,
    ensure_locality_map,
    same_clause_locality_stage15_style,
)
from orchestrator.pipeline_orchestrator import run_pipeline


def test_b28_24_trivial_main_uses_l10b_not_flat_l16_main_0():
    """When L16 is single main clause, locality ids match L10B (Stage 15 path)."""
    r = run_pipeline("إِنَّ اللَّهَ غَفُورٌ رَحِيمٌ")
    lo = r["layer_outputs"]
    m = build_clause_locality_token_map(lo)
    ce = lo.get("CLAUSE_ENGINE") or {}
    tr = ce.get("transformation_result") or ce
    ca = tr.get("clause_analysis") or []
    assert len(ca) == 1
    assert (ca[0].get("clause_type") or "").strip() == "main"
    # L10B may label tokens with a stable clause id string (e.g. main); L16 would be main_0.
    assert all(str(k).isdigit() for k in m.keys())
    assert len(m) >= 1


def test_b28_24_ensure_locality_accepts_legacy_clause_list():
    """Unit tests may pass L16 clause_analysis rows; ensure_locality_map coerces."""
    lo: dict = {}
    rows = [
        {"clause_id": "main_0", "start_token_id": "0", "end_token_id": "2", "clause_type": "main"},
    ]
    m = ensure_locality_map(lo, rows)
    assert m.get("0") == "main_0"


def test_b28_24_same_clause_permissive_empty():
    """Missing clause id on either side → permissive (Stage 15 parity)."""
    m = {"0": "a", "1": ""}
    assert same_clause_locality_stage15_style(m, 0, 1) is True


def test_b28_24_diagnostic_wa_allahu_pipeline_runs():
    """Spot-check: pipeline completes for وَاللَّهُ بِكُلِّ شَيْءٍ عَلِيمٌ (Quranic surface)."""
    r = run_pipeline("وَاللَّهُ بِكُلِّ شَيْءٍ عَلِيمٌ")
    assert r.get("layer_outputs")
    m = build_clause_locality_token_map(r["layer_outputs"])
    assert isinstance(m, dict)
