# -*- coding: utf-8 -*-
"""
Orchestrator presentation tests (Stage 7).
L14 renders compact/detailed/debug; rendered_output shape; I3rab explicit section.
"""

from __future__ import annotations

import pytest

from .conftest import assert_has_section, run_pipeline_for_test


def test_l14_status_not_pass_through():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    L14 = (pipeline.get("layer_outputs") or {}).get("L14_PRESENTATION") or {}
    assert L14.get("status") != "pass_through"
    assert L14.get("status") in ("success", "partial")


def test_rendered_output_exists():
    pipeline = run_pipeline_for_test("كَاتِبٌ")
    assert pipeline.get("rendered_output") is not None


def test_rendered_output_mode_matches_requested():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    assert ro.get("mode") == "detailed"


@pytest.mark.parametrize("mode", ["compact", "detailed", "debug"])
def test_all_modes_render(mode):
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode=mode)
    ro = pipeline.get("rendered_output") or {}
    assert ro.get("mode") == mode
    assert ro.get("summary") is not None
    assert len(ro.get("summary", "")) > 0


def test_detailed_mode_includes_sections():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    sections = ro.get("sections") or []
    assert len(sections) >= 5


def test_detailed_mode_includes_i3rab_section():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    assert_has_section(ro, "i3rab")


def test_detailed_mode_includes_discourse_frames_section():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    assert_has_section(ro, "discourse_frames")


def test_debug_mode_includes_stage_info():
    pipeline = run_pipeline_for_test("كَاتِبٌ", render_mode="debug")
    ro = pipeline.get("rendered_output") or {}
    summary = ro.get("summary") or ""
    content = ""
    for s in ro.get("sections") or []:
        content += s.get("content") or ""
    assert "validity" in summary.lower() or "Validity" in summary or "stage" in content.lower()


def test_rendered_output_summary_non_empty():
    pipeline = run_pipeline_for_test("إِنَّ اللَّهَ غَفُورٌ")
    ro = pipeline.get("rendered_output") or {}
    assert len(ro.get("summary", "")) > 0
