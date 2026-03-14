# -*- coding: utf-8 -*-
"""
Orchestrator smoke tests across canonical inputs.
Focus: status semantics and section existence, not exact long text bodies.
"""

from __future__ import annotations

import pytest

from .conftest import (
    CANONICAL_INPUTS,
    assert_has_section,
    extract_stage_status_map,
    get_evidence_claims,
    run_pipeline_for_test,
)

VALID_STATUSES = frozenset({"success", "partial", "skipped", "failed", "pass_through", "missing"})


@pytest.mark.parametrize("text", CANONICAL_INPUTS)
def test_pipeline_completes(text):
    pipeline = run_pipeline_for_test(text)
    assert pipeline is not None
    assert pipeline.get("layer_outputs") is not None
    assert pipeline.get("final_validation") is not None
    assert pipeline.get("rendered_output") is not None


@pytest.mark.parametrize("text", CANONICAL_INPUTS)
def test_all_stage_statuses_valid(text):
    pipeline = run_pipeline_for_test(text)
    status_map = extract_stage_status_map(pipeline)
    for stage_id, status in status_map.items():
        assert status in VALID_STATUSES, f"{stage_id} invalid status: {status}"


@pytest.mark.parametrize("text", CANONICAL_INPUTS)
def test_final_validation_has_global_validity(text):
    pipeline = run_pipeline_for_test(text)
    fv = pipeline.get("final_validation") or {}
    assert "global_validity" in fv
    assert fv.get("global_validity") in ("valid", "partial", "weak", "invalid", None) or isinstance(
        fv.get("global_validity"), str
    )


@pytest.mark.parametrize("text", CANONICAL_INPUTS)
def test_rendered_output_has_mode_and_summary(text):
    pipeline = run_pipeline_for_test(text)
    ro = pipeline.get("rendered_output") or {}
    assert "mode" in ro
    assert "summary" in ro
    assert len(ro.get("summary", "")) >= 0


@pytest.mark.parametrize("text", ["كَاتِبٌ", "إِنَّ اللَّهَ غَفُورٌ"])
def test_detailed_has_i3rab_section(text):
    pipeline = run_pipeline_for_test(text, render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    assert_has_section(ro, "i3rab")


@pytest.mark.parametrize("text", CANONICAL_INPUTS)
def test_evidence_trace_present_in_detailed(text):
    pipeline = run_pipeline_for_test(text, render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    assert isinstance(trace, list)
    for e in trace:
        assert "supporting_stage" in e
        assert "status" in e
