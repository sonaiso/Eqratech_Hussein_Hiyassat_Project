# -*- coding: utf-8 -*-
"""
End-to-end orchestrator tests.
Locks in the full pipeline contract: L0–L14, final_validation, rendered_output.
"""

import pytest
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from orchestrator import run as run_pipeline


@pytest.mark.parametrize("text,expected_validity", [
    ("إِنَّ اللَّهَ غَفُورٌ", "valid"),
    ("كَاتِبٌ", "valid"),
    ("يَا رَبِّ", "valid"),
    ("وَ", "valid"),
    ("!", "valid"),
])
def test_pipeline_runs_and_validates(text, expected_validity):
    pipeline = run_pipeline(text)
    fv = pipeline["final_validation"]
    assert fv["global_validity"] == expected_validity
    assert fv["final_confidence"] >= 0.0
    assert pipeline["rendered_output"]["mode"] is not None
    # L14 must not be pass_through
    assert pipeline["layer_outputs"]["L14_PRESENTATION"]["status"] != "pass_through"


@pytest.mark.parametrize("text", [
    "إِنَّ اللَّهَ غَفُورٌ",
    "كَاتِبٌ",
    "يَا رَبِّ",
    "وَ",
    "في",
    "!",
])
def test_all_15_layers_present(text):
    """Every stage ID must appear in layer_outputs."""
    from orchestrator.types import STAGE_ORDER
    pipeline = run_pipeline(text)
    outputs = pipeline.get("layer_outputs", {})
    for stage_id in STAGE_ORDER:
        assert stage_id in outputs, f"Missing stage: {stage_id} for input: {text}"


@pytest.mark.parametrize("text", [
    "إِنَّ اللَّهَ غَفُورٌ",
    "كَاتِبٌ",
    "يَا رَبِّ",
])
def test_rendered_output_has_required_keys(text):
    """rendered_output must have mode, summary, sections."""
    pipeline = run_pipeline(text)
    ro = pipeline.get("rendered_output", {})
    assert "mode" in ro
    assert "summary" in ro
    assert "sections" in ro


@pytest.mark.parametrize("text", [
    "إِنَّ اللَّهَ غَفُورٌ",
    "كَاتِبٌ",
])
def test_i3rab_section_present_in_detailed(text):
    """In detailed mode, an I3rab section must be present."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run(text, render_mode="detailed")
    ro = pipeline.get("rendered_output", {})
    sections = ro.get("sections", [])
    section_ids = [s.get("id") for s in sections]
    assert "i3rab" in section_ids, f"I3rab section missing for: {text}"


@pytest.mark.parametrize("text,should_skip", [
    ("وَ", ["L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING"]),
    ("في", ["L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING"]),
])
def test_gate_skips_particles(text, should_skip):
    """Particles must not get success on root/wazn layers."""
    pipeline = run_pipeline(text)
    outputs = pipeline.get("layer_outputs", {})
    for layer_id in should_skip:
        status = outputs.get(layer_id, {}).get("status")
        assert status == "skipped", (
            f"{layer_id} should be skipped for particle '{text}', got: {status}"
        )


def test_no_false_success_on_punctuation():
    """Punctuation must not produce root or wazn success."""
    pipeline = run_pipeline("!")
    outputs = pipeline.get("layer_outputs", {})
    assert outputs["L8_ROOT_EXTRACTION"]["status"] == "skipped"
    assert outputs["L9_WAZN_MATCHING"]["status"] == "skipped"


def test_final_validation_always_present():
    """final_validation must always be populated."""
    for text in ["وَ", "كَاتِبٌ", "إِنَّ اللَّهَ غَفُورٌ"]:
        pipeline = run_pipeline(text)
        fv = pipeline.get("final_validation", {})
        assert "global_validity" in fv
        assert "final_confidence" in fv
        assert "issues" in fv
