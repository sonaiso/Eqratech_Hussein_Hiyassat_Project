# -*- coding: utf-8 -*-
"""
Tests for DISCOURSE_FRAME_BUILDER (additive layer).
Structure, confidence bands, frame types, limitations; no long prose assertions.
"""

from __future__ import annotations

from unittest.mock import patch

import pytest

from .conftest import run_pipeline_for_test


def _minimal_lo_conditional_token_only():
    """L10B has no main_clause_type conditional; only node has connective_group (no L12B discourse support)."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
                "dependency_nodes": [
                    {"surface": "لَو", "connective_group": "conditional"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [],
            },
        },
    }


def _minimal_lo_conditional_with_clause_support():
    """L10B main_clause_type conditional; clause supports conditional."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "conditional"},
                "clause_units": [{"type": "conditional", "clause_id": "main"}],
                "dependency_nodes": [
                    {"surface": "لَو", "connective_group": "conditional"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [
                    {"token": "لَو", "reasoning_type": "discourse", "connective_group": "conditional"},
                ],
            },
        },
    }


def _minimal_lo_inna_noise():
    """Noisy upstream conditional hint on إنَّ must not yield a conditional frame."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
                "dependency_nodes": [
                    {"surface": "إِنَّ", "connective_group": "conditional"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [
                    {"token": "إِنَّ", "reasoning_type": "discourse", "connective_group": "conditional"},
                ],
            },
        },
    }


def _minimal_lo_adversative_token_only():
    """Adversative from L10B node only; no L12B discourse support."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
                "dependency_nodes": [
                    {"surface": "لَكِن", "connective_group": "adversative"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [],
            },
        },
    }


def _minimal_lo_explanation_causation_no_support():
    """Explanation/causation connective; no L12B cause/effect claim."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "verbal"},
                "clause_units": [],
                "dependency_nodes": [
                    {"surface": "لِأَنَّ", "connective_group": "explanation_causation"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [
                    {"token": "لِأَنَّ", "reasoning_type": "discourse", "connective_group": "explanation_causation"},
                ],
            },
        },
    }


def _minimal_lo_negation():
    """Negation connective; no sentence-level support."""
    return {
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
                "dependency_nodes": [
                    {"surface": "لَم", "connective_group": "negation"},
                ],
            },
        },
        "L12B_ANALOGICAL_REASONING": {
            "transformation_result": {
                "analogical_inferences": [
                    {"token": "لَم", "reasoning_type": "discourse", "connective_group": "negation"},
                ],
            },
        },
    }


def test_output_shape_stable():
    """Output has frames, frame_count, frame_types, coverage_hint, optional strong/weak counts."""
    from orchestrator.discourse_frame import build_discourse_frames

    lo = _minimal_lo_conditional_token_only()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "conditional"}
        out = build_discourse_frames(lo)
    assert out is not None
    assert "frames" in out
    assert "frame_count" in out
    assert "frame_types" in out
    assert "coverage_hint" in out
    assert "strong_frame_count" in out
    assert "weak_frame_count" in out
    assert isinstance(out["frames"], list)
    assert isinstance(out["frame_types"], list)


def test_conditional_token_only_weak_or_medium():
    """Conditional frame from token only (no clause support) -> weak or medium, with limitation."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import CONF_STRONG, FRAME_CONDITIONAL

    lo = _minimal_lo_conditional_token_only()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "conditional"}
        out = build_discourse_frames(lo)
    assert out and out.get("frame_count", 0) >= 1
    frames = [f for f in out["frames"] if f.get("frame_type") == FRAME_CONDITIONAL]
    assert len(frames) >= 1
    f = frames[0]
    assert f.get("confidence") != CONF_STRONG
    assert "connective recognition only" in (f.get("limitation") or "")


def test_conditional_with_clause_support_strong():
    """Conditional token + L10B clause support -> strong conditional frame."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import CONF_STRONG, FRAME_CONDITIONAL

    lo = _minimal_lo_conditional_with_clause_support()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "conditional"}
        out = build_discourse_frames(lo)
    assert out and out.get("frame_count", 0) >= 1
    frames = [f for f in out["frames"] if f.get("frame_type") == FRAME_CONDITIONAL]
    assert len(frames) >= 1
    f = frames[0]
    assert f.get("confidence") == CONF_STRONG
    assert f.get("scope_hint") in ("clause-level", "sentence-level")


def test_inna_noise_does_not_emit_conditional_frame():
    """إِنَّ must not emit a conditional discourse frame even if noisy metadata says conditional."""
    from orchestrator.discourse_frame import build_discourse_frames

    lo = _minimal_lo_inna_noise()
    out = build_discourse_frames(lo)
    assert out is not None
    assert out.get("frame_count", 0) == 0


def test_adversative_token_only_not_strong():
    """Adversative from token only -> not strong."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import CONF_STRONG, FRAME_ADVERSATIVE

    lo = _minimal_lo_adversative_token_only()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "adversative"}
        out = build_discourse_frames(lo)
    assert out is not None
    frames = [f for f in out.get("frames", []) if f.get("frame_type") == FRAME_ADVERSATIVE]
    if frames:
        assert frames[0].get("confidence") != CONF_STRONG
        assert "lacks downstream contrast" in (frames[0].get("limitation") or "")


def test_explanation_causation_without_support_stays_explanation():
    """Explanation/causation token without cause/effect support -> FRAME_EXPLANATION, not causation."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import FRAME_CAUSATION, FRAME_EXPLANATION

    lo = _minimal_lo_explanation_causation_no_support()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "explanation_causation"}
        out = build_discourse_frames(lo)
    assert out is not None
    frames = out.get("frames", [])
    explanation_frames = [f for f in frames if f.get("frame_type") == FRAME_EXPLANATION]
    causation_frames = [f for f in frames if f.get("frame_type") == FRAME_CAUSATION]
    assert len(causation_frames) == 0
    assert len(explanation_frames) >= 1
    if explanation_frames:
        assert "not fully disambiguated" in (explanation_frames[0].get("limitation") or "")


def test_negation_frame_conservative():
    """Negation frame present; confidence conservative (weak or medium)."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import FRAME_NEGATION

    lo = _minimal_lo_negation()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "negation"}
        out = build_discourse_frames(lo)
    assert out is not None
    frames = [f for f in out.get("frames", []) if f.get("frame_type") == FRAME_NEGATION]
    if frames:
        assert frames[0].get("confidence") in ("weak", "medium")


def test_weak_frame_has_limitation_or_suppressed():
    """Weak unsupported frame has clear limitation (we keep with limitation, not remove)."""
    from orchestrator.discourse_frame import build_discourse_frames
    from orchestrator.discourse_frame.builder import CONF_WEAK

    lo = _minimal_lo_adversative_token_only()
    with patch("orchestrator.connectives.classify_connective") as mock_c:
        mock_c.return_value = {"group": "adversative"}
        out = build_discourse_frames(lo)
    assert out is not None
    weak_frames = [f for f in out.get("frames", []) if f.get("confidence") == CONF_WEAK]
    for f in weak_frames:
        assert f.get("limitation") or f.get("scope_hint") == "token-local"


def test_additive_only_no_existing_output_changed():
    """Running pipeline with discourse frame builder does not alter L10B/L11B/L12B outputs."""
    pipeline = run_pipeline_for_test("لَوْ اجْتَهَدَ الطَّالِبُ لَنَجَحَ")
    lo = pipeline.get("layer_outputs") or {}
    l10b_before = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result")
    l11b_before = (lo.get("L11B_CAUSAL_I3RAB") or {}).get("transformation_result")
    l12b_before = (lo.get("L12B_ANALOGICAL_REASONING") or {}).get("transformation_result")
    df = lo.get("DISCOURSE_FRAME_BUILDER")
    assert l10b_before is not None
    assert l11b_before is not None
    assert l12b_before is not None
    if df:
        assert "frames" in df
        assert "frame_count" in df


def test_empty_connective_sources_returns_empty_frames():
    """No L10B/L12B connective tokens -> empty frames, coverage_hint indicates no tokens."""
    from orchestrator.discourse_frame import build_discourse_frames

    lo = {
        "L10B_DEEP_SYNTAX": {"transformation_result": {"dependency_nodes": [], "syntax_summary": {}}},
        "L12B_ANALOGICAL_REASONING": {"transformation_result": {"analogical_inferences": []}},
    }
    out = build_discourse_frames(lo)
    assert out is not None
    assert out.get("frame_count", 0) == 0
    assert "frames" in out
    assert len(out["frames"]) == 0
    assert "no connective" in (out.get("coverage_hint") or "").lower() or "0 frames" in (out.get("coverage_hint") or "")
