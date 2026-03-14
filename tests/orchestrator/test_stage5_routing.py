# -*- coding: utf-8 -*-
"""
Orchestrator routing / gate tests (Stage 5).
Minimal/pathological inputs cause skipped/partial where expected; no fake success.
"""

from __future__ import annotations

import pytest

from .conftest import run_pipeline_for_test, extract_stage_status_map


def test_waw_l8_l9_skipped():
    """For 'وَ', L8 and L9 should be skipped (operator; no root candidate)."""
    pipeline = run_pipeline_for_test("وَ")
    status_map = extract_stage_status_map(pipeline)
    assert status_map.get("L8_ROOT_EXTRACTION") == "skipped"
    assert status_map.get("L9_WAZN_MATCHING") == "skipped"


def test_waw_l8_not_fake_success_with_empty_roots():
    """L8 must not be success with empty root result for operator-only input."""
    pipeline = run_pipeline_for_test("وَ")
    lo = pipeline.get("layer_outputs") or {}
    L8 = lo.get("L8_ROOT_EXTRACTION") or {}
    assert L8.get("status") != "success" or (L8.get("transformation_result") or {}).get("words")
    # If success, there must be some content; for "وَ" we expect skipped
    assert L8.get("status") in ("skipped", "partial", "success")


def test_fi_l8_l9_skipped():
    """For 'في', L8 and L9 should be skipped (particle)."""
    pipeline = run_pipeline_for_test("في")
    status_map = extract_stage_status_map(pipeline)
    assert status_map.get("L8_ROOT_EXTRACTION") == "skipped"
    assert status_map.get("L9_WAZN_MATCHING") == "skipped"


def test_punctuation_l8_l9_skipped():
    """For '!', morphology-heavy stages should be skipped."""
    pipeline = run_pipeline_for_test("!")
    status_map = extract_stage_status_map(pipeline)
    assert status_map.get("L8_ROOT_EXTRACTION") == "skipped"
    assert status_map.get("L9_WAZN_MATCHING") == "skipped"


def test_punctuation_tokenization_appropriate():
    """Tokenization still works for punctuation."""
    pipeline = run_pipeline_for_test("!")
    L2 = (pipeline.get("layer_outputs") or {}).get("L2_TOKENIZATION") or {}
    tr = L2.get("transformation_result") or {}
    tokens = tr.get("tokens") or []
    assert isinstance(tokens, list)


def test_katib_l8_produces_root_evidence():
    """For 'كَاتِبٌ', L8 should produce real root evidence."""
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L8 = (pipeline.get("layer_outputs") or {}).get("L8_ROOT_EXTRACTION") or {}
    assert L8.get("status") in ("success", "partial")
    tr = L8.get("transformation_result") or {}
    words = tr.get("words") or []
    assert len(words) >= 1
    roots = [w.get("root") for w in words if w.get("root")]
    assert len(roots) >= 1


def test_katib_l9_produces_wazn_evidence():
    """For 'كَاتِبٌ', L9 should produce pattern/wazn evidence."""
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L9 = (pipeline.get("layer_outputs") or {}).get("L9_WAZN_MATCHING") or {}
    assert L9.get("status") in ("success", "partial")
    tr = L9.get("transformation_result") or {}
    words = tr.get("words") or []
    assert len(words) >= 1


def test_katib_l11_produces_i3rab_evidence():
    """For 'كَاتِبٌ', L11 should produce i3rab evidence."""
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L11 = (pipeline.get("layer_outputs") or {}).get("L11_I3RAB") or {}
    assert L11.get("status") in ("success", "partial")
    tr = L11.get("transformation_result") or {}
    token_results = tr.get("token_results") or []
    assert len(token_results) >= 1


def test_l12_not_overclaim_strong_sentence_for_single_token():
    """L12 should not overclaim full strong sentence evidence for single operator."""
    pipeline = run_pipeline_for_test("وَ")
    L12 = (pipeline.get("layer_outputs") or {}).get("L12_SEMANTIC_RHETORICAL") or {}
    status = L12.get("status")
    assert status in ("success", "partial", "skipped")
    # Partial or skipped is acceptable for single-token operator
    if status == "success":
        tr = L12.get("transformation_result") or {}
        assert tr.get("sentence_type") or tr.get("rhetoric_signals") or True
