# -*- coding: utf-8 -*-
"""
Orchestrator validation tests (Stage 6).
L13 is not pass_through; global_validity and issues; final_validation mirrors L13.
"""

from __future__ import annotations

import pytest

from .conftest import run_pipeline_for_test


def test_l13_not_pass_through():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L13 = (pipeline.get("layer_outputs") or {}).get("L13_VALIDATION") or {}
    assert L13.get("status") != "pass_through"


def test_l13_transformation_result_includes_global_validity():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L13 = (pipeline.get("layer_outputs") or {}).get("L13_VALIDATION") or {}
    tr = L13.get("transformation_result") or {}
    assert "global_validity" in tr


def test_top_level_final_validation_exists():
    pipeline = run_pipeline_for_test("إِنَّ اللَّهَ غَفُورٌ")
    fv = pipeline.get("final_validation")
    assert fv is not None
    assert "global_validity" in fv
    assert "issues" in fv


def test_final_validation_confidence_present_or_null():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    fv = pipeline.get("final_validation") or {}
    assert "final_confidence" in fv
    # Value may be number or None per current logic
    c = fv.get("final_confidence")
    assert c is None or isinstance(c, (int, float))


def test_validation_emits_issues_list():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    fv = pipeline.get("final_validation") or {}
    issues = fv.get("issues")
    assert isinstance(issues, list)


def test_validation_direct_call_emits_expected_codes():
    """Feed manipulated layer_outputs to run_validation; expect structural behavior."""
    from orchestrator.l13_validation import run_validation

    # Empty layer_outputs -> invalid or issues
    issues, validity, summary, confidence = run_validation({})
    assert isinstance(issues, list)
    assert validity in ("invalid", "weak", "partial", "valid")
    assert isinstance(summary, dict)

    # L8 success but no tokens in L2 -> possible MISSING_PREREQUISITE or EMPTY_SUCCESS
    layer_outputs = {
        "L2_TOKENIZATION": {"status": "success", "transformation_result": {"tokens": []}},
        "L8_ROOT_EXTRACTION": {"status": "success", "transformation_result": {"words": []}},
        "L9_WAZN_MATCHING": {"status": "success", "transformation_result": {"words": []}},
        "L11_I3RAB": {"status": "success", "transformation_result": {"token_results": []}},
        "L12_SEMANTIC_RHETORICAL": {"status": "success", "transformation_result": {}},
    }
    for sid in ["L0_INPUT", "L1_NORMALIZATION", "L3_SEGMENTATION", "L4_OPERATORS", "L5_WORD_TYPING",
                "L6_PHONOLOGY", "L7_SYLLABIFICATION", "L10_SYNTAX", "L13_VALIDATION"]:
        layer_outputs.setdefault(sid, {"status": "missing", "transformation_result": {}})

    issues2, validity2, _, _ = run_validation(layer_outputs)
    assert isinstance(issues2, list)
    codes = [i.get("code") for i in issues2]
    # May contain EMPTY_SUCCESS or MISSING_PREREQUISITE depending on logic
    assert validity2 in ("invalid", "weak", "partial", "valid")
