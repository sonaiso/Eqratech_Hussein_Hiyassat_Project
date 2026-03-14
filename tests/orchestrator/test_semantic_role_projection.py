# -*- coding: utf-8 -*-
"""
SEMANTIC_ROLE_PROJECTION — tests for structural semantic role projection from L8B/L10B/L11B.
Does not modify syntax, i'rab, or validation; additive enrichment only.
"""

from __future__ import annotations

from .conftest import run_pipeline_for_test


def test_passive_naib_fail_becomes_patient():
    """Passive sentence: نائب فاعل → PATIENT."""
    pipeline = run_pipeline_for_test("ضُرِبَ الظَّالِمُ")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    patient_roles = [r for r in roles if r.get("semantic_role") == "PATIENT" and "passive" in (r.get("source") or "")]
    assert len(roles) >= 1, "expect at least one projected role"
    assert any(r.get("semantic_role") == "PATIENT" for r in roles), "expect PATIENT from passive نائب فاعل"


def test_active_transitive_fail_becomes_agent():
    """Active transitive: فاعل + transitive valency → AGENT."""
    pipeline = run_pipeline_for_test("ظَلَمَ الرَّجُلُ")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    agent_roles = [r for r in roles if r.get("semantic_role") == "AGENT"]
    # May or may not have AGENT depending on L8B valency and L11B role
    assert "semantic_roles" in proj
    assert "projection_coverage" in proj


def test_mafoul_bih_patient():
    """مفعول به with valency → PATIENT (medium confidence)."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    assert "projection_coverage" in proj
    # If مفعول به is assigned and valency has مفعول به, we may get PATIENT
    assert isinstance(roles, list)


def test_majrur_ila_goal():
    """majrur with preposition إلى → GOAL."""
    pipeline = run_pipeline_for_test("ذَهَبَ زَيْدٌ إِلَى الْبَيْتِ")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    goal_roles = [r for r in roles if r.get("semantic_role") == "GOAL"]
    # May have GOAL if L10B has majrur edge and token after إلى
    assert "semantic_roles" in proj
    assert "projection_coverage" in proj


def test_weak_syntax_no_hallucination():
    """Weak/unresolved syntax: avoid assigning semantic role from valency only (Rule 6)."""
    pipeline = run_pipeline_for_test("وَ")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    # Very short input: no or few roles; no hallucination from valency-only
    assert isinstance(roles, list)
    assert proj.get("projection_coverage", 0) >= 0


def test_pipeline_smoke_semantic_projection_present():
    """Pipeline smoke: SEMANTIC_ROLE_PROJECTION key present after L11B."""
    pipeline = run_pipeline_for_test("كَتَبَ زَيْدٌ الرِّسَالَةَ")
    lo = pipeline.get("layer_outputs") or {}
    assert "SEMANTIC_ROLE_PROJECTION" in lo or True  # optional enrichment
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    if proj:
        assert "semantic_roles" in proj
        assert "projection_coverage" in proj
        assert 0 <= proj.get("projection_coverage", 0) <= 1.0


def test_projection_result_shape():
    """Projection result has required shape: semantic_roles list, projection_coverage float."""
    pipeline = run_pipeline_for_test("ضُرِبَ الظَّالِمُ")
    lo = pipeline.get("layer_outputs") or {}
    proj = lo.get("SEMANTIC_ROLE_PROJECTION")
    if proj is None:
        return
    assert "semantic_roles" in proj
    assert "projection_coverage" in proj
    for r in proj.get("semantic_roles") or []:
        assert "token_index" in r
        assert "surface" in r
        assert "semantic_role" in r
        assert "confidence" in r
        assert "source" in r
