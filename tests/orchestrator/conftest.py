# -*- coding: utf-8 -*-
"""
Orchestrator integration test helpers and fixtures.
Stage 9: shared utilities for contract, routing, validation, presentation, explainability.
"""

from __future__ import annotations

from typing import Any, Dict, List

import pytest


# Canonical test inputs (stable)
CANONICAL_INPUTS = [
    "وَ",
    "في",
    "!",
    "يَا رَبِّ",
    "كَاتِبٌ",
    "إِنَّ اللَّهَ غَفُورٌ",
]

REQUIRED_STAGE_IDS = [
    "L0_INPUT",
    "L1_NORMALIZATION",
    "L2_TOKENIZATION",
    "L3_SEGMENTATION",
    "L4_OPERATORS",
    "L5_WORD_TYPING",
    "L6_PHONOLOGY",
    "L7_SYLLABIFICATION",
    "L8_ROOT_EXTRACTION",
    "L8B_VERB_BAB_GOVERNANCE",
    "L9_WAZN_MATCHING",
    "L10_SYNTAX",
    "L10B_DEEP_SYNTAX",
    "L11_I3RAB",
    "L11B_CAUSAL_I3RAB",
    "L12_SEMANTIC_RHETORICAL",
    "L12B_ANALOGICAL_REASONING",
    "L13_COGNITIVE_FUSION",
    "L13_VALIDATION",
    "L14_PRESENTATION",
]


def run_pipeline_for_test(text: str, render_mode: str = "detailed") -> Dict[str, Any]:
    """Run pipeline on text; default detailed for full sections."""
    from orchestrator import run
    return run(text, render_mode=render_mode)


def extract_stage_status_map(pipeline: Dict[str, Any]) -> Dict[str, str]:
    """Return dict of stage_id -> status from layer_outputs."""
    lo = pipeline.get("layer_outputs") or {}
    return {sid: (lo.get(sid) or {}).get("status", "missing") for sid in REQUIRED_STAGE_IDS}


def assert_has_section(rendered_output: Dict[str, Any], section_id: str) -> None:
    """Assert that rendered_output has a section with the given id."""
    sections = rendered_output.get("sections") or []
    ids_found = [s.get("id") for s in sections if s.get("id")]
    assert section_id in ids_found, f"Section id '{section_id}' not in {ids_found}"


def get_evidence_claims(pipeline: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Return evidence_trace list from rendered_output.artifacts."""
    ro = pipeline.get("rendered_output") or {}
    artifacts = ro.get("artifacts") or {}
    return artifacts.get("evidence_trace") or []


@pytest.fixture(scope="module")
def pipeline_katib():
    """One content-word pipeline for reuse."""
    return run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")


@pytest.fixture(scope="module")
def pipeline_waw():
    """Operator-only pipeline."""
    return run_pipeline_for_test("وَ", render_mode="detailed")
