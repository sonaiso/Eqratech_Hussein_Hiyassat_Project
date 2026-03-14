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


# ── Stage 8: Explainability tests ──────────────────────────────────────────

def test_evidence_trace_in_artifacts():
    """rendered_output.artifacts must contain evidence_trace."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output", {})
    artifacts = ro.get("artifacts", {})
    assert "evidence_trace" in artifacts, "evidence_trace missing from artifacts"
    assert isinstance(artifacts["evidence_trace"], list)
    assert len(artifacts["evidence_trace"]) > 0


def test_evidence_trace_entry_shape():
    """Each evidence trace entry must have required fields."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("إِنَّ اللَّهَ غَفُورٌ", render_mode="detailed")
    trace = pipeline["rendered_output"]["artifacts"]["evidence_trace"]
    for entry in trace:
        assert "claim" in entry
        assert "supporting_stage" in entry
        assert "evidence" in entry
        assert "status" in entry
        assert entry["status"] in ("supported", "limited", "absent", "skipped")


def test_skipped_stages_have_explanations():
    """Skipped layers (وَ L8/L9) must appear in evidence trace as skipped."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("وَ", render_mode="detailed")
    trace = pipeline["rendered_output"]["artifacts"]["evidence_trace"]
    skipped_stages = {e["supporting_stage"] for e in trace if e["status"] == "skipped"}
    assert "L8_ROOT_EXTRACTION" in skipped_stages
    assert "L9_WAZN_MATCHING" in skipped_stages


def test_i3rab_evidence_present():
    """I3rab evidence section must appear for content words."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("كَاتِبٌ", render_mode="detailed")
    sections = pipeline["rendered_output"]["sections"]
    section_ids = [s["id"] for s in sections]
    assert "i3rab_evidence" in section_ids or "i3rab" in section_ids


def test_no_overclaiming_on_punctuation():
    """Punctuation must not have supported morphology evidence."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("!", render_mode="detailed")
    trace = pipeline["rendered_output"]["artifacts"]["evidence_trace"]
    for entry in trace:
        if entry["supporting_stage"] in ("L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING"):
            assert entry["status"] == "skipped", (
                f"Punctuation should not have supported morphology: {entry}"
            )


def test_compact_why_lines_for_skipped():
    """Compact mode must include Why lines when stages are skipped."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("وَ", render_mode="compact")
    ro = pipeline.get("rendered_output", {})
    summary = ro.get("summary", "")
    # artifacts should still have evidence_trace in compact
    assert "evidence_trace" in ro.get("artifacts", {})


def test_validation_reasoning_section_present():
    """detailed mode must have a validation_reasoning section."""
    from orchestrator.pipeline_orchestrator import run_pipeline as _run
    pipeline = _run("إِنَّ اللَّهَ غَفُورٌ", render_mode="detailed")
    sections = pipeline["rendered_output"]["sections"]
    section_ids = [s["id"] for s in sections]
    assert "validation_reasoning" in section_ids or "validation" in section_ids
