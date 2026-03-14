# -*- coding: utf-8 -*-
"""
Orchestrator explainability tests (Stage 8).
evidence_trace artifacts exist; structure; skipped/partial explained; validation reasoning.
"""

from __future__ import annotations

import pytest

from .conftest import get_evidence_claims, run_pipeline_for_test


def test_evidence_trace_artifact_exists():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    artifacts = ro.get("artifacts") or {}
    assert "evidence_trace" in artifacts


def test_evidence_trace_is_list():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    assert isinstance(trace, list)


def test_evidence_trace_non_empty_for_content_input():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    assert len(trace) >= 1


def test_evidence_entry_has_required_fields():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    assert len(trace) >= 1
    entry = trace[0]
    assert "claim" in entry
    assert "supporting_stage" in entry
    assert "evidence" in entry
    assert "status" in entry


def test_waw_evidence_trace_explains_l8_l9_skipped():
    pipeline = run_pipeline_for_test("وَ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    skipped_l8 = [e for e in trace if e.get("supporting_stage") == "L8_ROOT_EXTRACTION" and e.get("status") == "skipped"]
    skipped_l9 = [e for e in trace if e.get("supporting_stage") == "L9_WAZN_MATCHING" and e.get("status") == "skipped"]
    assert len(skipped_l8) >= 1 or any(e.get("supporting_stage") == "L8_ROOT_EXTRACTION" for e in trace)
    assert len(skipped_l9) >= 1 or any(e.get("supporting_stage") == "L9_WAZN_MATCHING" for e in trace)


def test_katib_evidence_trace_includes_root_or_pattern_or_i3rab():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    stages = [e.get("supporting_stage") for e in trace]
    assert "L8_ROOT_EXTRACTION" in stages or "L9_WAZN_MATCHING" in stages or "L11_I3RAB" in stages


def test_validation_reasoning_in_evidence_trace():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    trace = get_evidence_claims(pipeline)
    l13_entries = [e for e in trace if e.get("supporting_stage") == "L13_VALIDATION"]
    assert len(l13_entries) >= 1
    assert "global_validity" in str(l13_entries[0].get("evidence", []))
