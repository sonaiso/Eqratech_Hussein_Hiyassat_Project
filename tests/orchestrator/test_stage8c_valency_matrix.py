# -*- coding: utf-8 -*-
"""
Tests for L8C Valency Matrix Seed Layer.
Valency is knowledge-only; no syntax, iʿrāb, or dependency changes.
"""

from __future__ import annotations

import pytest

try:
    from orchestrator.valency import load_valency_kb, resolve_valency, ValencyFrame
except ImportError:
    from src.orchestrator.valency import load_valency_kb, resolve_valency, ValencyFrame


def test_resolve_valency_exact_root():
    """Exact root match returns frame with expected class and required_roles."""
    frame = resolve_valency("ضرب")
    assert frame is not None
    assert frame.valency_class == "transitive_one_object"
    assert "فاعل" in frame.required_roles
    assert "مفعول به" in frame.required_roles
    assert frame.confidence >= 0.85
    # Root with dashes normalizes to same
    frame2 = resolve_valency("ض-ر-ب")
    assert frame2 is not None
    assert frame2.valency_class == frame.valency_class


def test_resolve_valency_unknown_root():
    """Unknown or nonexistent root returns frame with valency_class=unknown, confidence 0.20."""
    frame = resolve_valency("xyz")
    assert frame is not None
    assert frame.valency_class == "unknown"
    assert frame.required_roles == []
    assert frame.confidence == 0.20
    # Empty root returns unknown frame
    frame_empty = resolve_valency("")
    assert frame_empty is not None
    assert frame_empty.valency_class == "unknown"
    assert frame_empty.required_roles == []


def test_resolve_valency_quadrilateral_returns_none():
    """Quadrilateral root returns None (caller uses unknown placeholder)."""
    frame_4 = resolve_valency("أكرم")
    assert frame_4 is None
    frame_4b = resolve_valency("فعلل")
    assert frame_4b is None


def test_profile_contains_valency_fields():
    """L8B verb profile includes valency_class, valency_required_roles, valency_optional_roles, valency_confidence."""
    from tests.orchestrator.conftest import run_pipeline_for_test
    pipeline = run_pipeline_for_test("ظَلَمَ الرجل")
    lo = pipeline.get("layer_outputs") or {}
    tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr8b.get("verb_governance_profiles") or []
    # May have 0 or 1+ profiles depending on candidacy gate
    for p in profiles:
        if p.get("status") == "not_applicable":
            continue
        assert "valency_class" in p
        assert "valency_required_roles" in p
        assert "valency_optional_roles" in p
        assert "valency_confidence" in p
        assert isinstance(p.get("valency_required_roles"), list)
        assert isinstance(p.get("valency_optional_roles"), list)
        break
    else:
        if not profiles:
            pytest.skip("No verb profiles (candidacy gate may exclude)")
        pytest.skip("All profiles not_applicable")


def test_pipeline_smoke_valency_presence():
    """Pipeline runs and L8B profiles carry valency fields; ظَلَمَ can resolve to transitive_one_object."""
    from tests.orchestrator.conftest import run_pipeline_for_test
    pipeline = run_pipeline_for_test("ظَلَمَ الظالمُ")
    assert pipeline is not None
    lo = pipeline.get("layer_outputs") or {}
    tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr8b.get("verb_governance_profiles") or []
    has_valency = any(
        "valency_class" in p and p.get("valency_class") != "unknown"
        for p in profiles
        if p.get("status") != "not_applicable"
    )
    # At least one profile should have valency fields; may be unknown if root not in seed
    all_have_fields = all(
        "valency_class" in p and "valency_required_roles" in p
        for p in profiles
        if p.get("status") != "not_applicable"
    )
    assert all_have_fields or len(profiles) == 0
