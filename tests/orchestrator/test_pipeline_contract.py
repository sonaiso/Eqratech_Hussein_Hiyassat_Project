# -*- coding: utf-8 -*-
"""
Orchestrator pipeline contract tests.
Stage 9: top-level keys, stage IDs, layer_outputs shape, final_validation, rendered_output.
"""

from __future__ import annotations

import pytest

from .conftest import (
    CANONICAL_INPUTS,
    REQUIRED_STAGE_IDS,
    run_pipeline_for_test,
)


def test_pipeline_version_exists():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    assert "pipeline_version" in pipeline


def test_request_id_exists():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    assert "request_id" in pipeline


def test_original_text_matches_input():
    for text in CANONICAL_INPUTS:
        pipeline = run_pipeline_for_test(text)
        assert pipeline.get("original_text") == text


def test_stage_order_length_matches_required():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    order = pipeline.get("stage_order")
    assert order is not None
    assert len(order) == len(REQUIRED_STAGE_IDS)


def test_layer_outputs_contains_all_required_stage_keys():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    lo = pipeline.get("layer_outputs") or {}
    for stage_id in REQUIRED_STAGE_IDS:
        assert stage_id in lo, f"Missing layer_outputs key: {stage_id}"


def test_each_layer_output_has_required_fields():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    lo = pipeline.get("layer_outputs") or {}
    valid_statuses = ("success", "partial", "skipped", "failed", "pass_through", "missing")
    additive_raw = ("CLAUSE_ENGINE",)  # raw dict with status; DEPENDENCY_SYNTAX_BUILDER not in STAGE_ORDER
    for stage_id in REQUIRED_STAGE_IDS:
        layer = lo.get(stage_id) or {}
        if stage_id in additive_raw:
            assert stage_id in lo, f"{stage_id} missing from layer_outputs"
            continue
        assert "status" in layer, f"{stage_id} missing status"
        assert layer.get("status") in valid_statuses, f"{stage_id} invalid status: {layer.get('status')}"


def test_final_validation_populated():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    fv = pipeline.get("final_validation")
    assert fv is not None
    assert "global_validity" in fv
    assert "issues" in fv


def test_rendered_output_populated():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    ro = pipeline.get("rendered_output")
    assert ro is not None
    assert ro.get("mode") is not None
    assert ro.get("summary") is not None
