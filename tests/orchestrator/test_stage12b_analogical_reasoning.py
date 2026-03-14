# -*- coding: utf-8 -*-
"""
Orchestrator L12B Analogical Reasoning tests.
Stage id in order; layer_output shape; explainability trace; presentation section.
No assertions on specific Arabic strings.
"""

from __future__ import annotations

import pytest

from .conftest import (
    REQUIRED_STAGE_IDS,
    assert_has_section,
    get_evidence_claims,
    run_pipeline_for_test,
)


def test_stage_id_exists_in_stage_order():
    assert "L12B_ANALOGICAL_REASONING" in REQUIRED_STAGE_IDS
    from orchestrator.types import STAGE_ORDER
    assert "L12B_ANALOGICAL_REASONING" in STAGE_ORDER
    idx_l12 = STAGE_ORDER.index("L12_SEMANTIC_RHETORICAL")
    idx_l12b = STAGE_ORDER.index("L12B_ANALOGICAL_REASONING")
    idx_l13 = STAGE_ORDER.index("L13_VALIDATION")
    assert idx_l12 < idx_l12b < idx_l13


def test_layer_output_contains_analogical_summary():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    lo = pipeline.get("layer_outputs") or {}
    L12B = lo.get("L12B_ANALOGICAL_REASONING") or {}
    assert L12B.get("layer_id") == "L12B_ANALOGICAL_REASONING"
    tr = L12B.get("transformation_result") or {}
    summary = tr.get("analogical_summary")
    assert summary is not None
    assert "total_inferences" in summary
    assert "strong_count" in summary
    assert "weak_count" in summary
    assert isinstance(summary["total_inferences"], (int, float))
    assert isinstance(summary["strong_count"], (int, float))
    assert isinstance(summary["weak_count"], (int, float))


def test_ambiguity_resolutions_shape_valid():
    pipeline = run_pipeline_for_test("إِنَّ اللَّهَ غَفُورٌ")
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L12B_ANALOGICAL_REASONING") or {}).get("transformation_result") or {}
    resolutions = tr.get("ambiguity_resolutions") or []
    assert isinstance(resolutions, list)
    for r in resolutions:
        assert isinstance(r, dict)
        assert "token" in r or "preferred_role" in r or "reason" in r


def test_analogical_inferences_is_list():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L12B_ANALOGICAL_REASONING") or {}).get("transformation_result") or {}
    inferences = tr.get("analogical_inferences") or []
    assert isinstance(inferences, list)


def test_explainability_trace_includes_l12b():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    stages = [e.get("supporting_stage") for e in trace]
    assert "L12B_ANALOGICAL_REASONING" in stages


def test_presentation_detailed_includes_analogical_section():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    assert_has_section(ro, "analogical_reasoning")


def test_l12b_status_valid():
    pipeline = run_pipeline_for_test("وَ")
    lo = pipeline.get("layer_outputs") or {}
    L12B = lo.get("L12B_ANALOGICAL_REASONING") or {}
    status = L12B.get("status")
    assert status in ("success", "partial", "skipped", "failed")


def test_compact_mode_analogical_line():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="compact")
    ro = pipeline.get("rendered_output") or {}
    summary = ro.get("summary") or ""
    assert "Analogical inference used:" in summary
    assert "yes" in summary or "no" in summary
