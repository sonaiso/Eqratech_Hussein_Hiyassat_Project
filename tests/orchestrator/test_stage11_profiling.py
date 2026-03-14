# -*- coding: utf-8 -*-
"""
Orchestrator profiling tests (Stage 11).
Shape and consistency only; no exact timing assertions.
"""

from __future__ import annotations

from .conftest import REQUIRED_STAGE_IDS


def test_profiling_key_exists_when_enabled():
    from orchestrator import run
    p = run("كَاتِبٌ", render_mode="detailed", profile=True)
    assert "profiling" in p


def test_profiling_total_time_ms_present_and_non_negative():
    from orchestrator import run
    p = run("كَاتِبٌ", profile=True)
    pf = p.get("profiling")
    assert pf is not None
    total = pf.get("total_time_ms")
    assert total is not None
    assert isinstance(total, (int, float))
    assert total >= 0


def test_profiling_per_stage_contains_all_stage_ids():
    from orchestrator import run
    p = run("إِنَّ اللَّهَ غَفُورٌ", profile=True)
    pf = p.get("profiling")
    assert pf is not None
    per_stage = pf.get("per_stage") or {}
    for sid in REQUIRED_STAGE_IDS:
        assert sid in per_stage, f"Missing per_stage entry: {sid}"


def test_profiling_slowest_stage_id_is_valid():
    from orchestrator import run
    p = run("كَاتِبٌ", profile=True)
    pf = p.get("profiling")
    assert pf is not None
    slowest = pf.get("slowest_stage_id")
    assert slowest is None or slowest in REQUIRED_STAGE_IDS


def test_profiling_stage_count_is_20():
    from orchestrator import run
    p = run("وَ", profile=True)
    pf = p.get("profiling")
    assert pf is not None
    assert pf.get("stage_count") == 20


def test_rendered_output_can_include_performance_section():
    from orchestrator import run
    p = run("كَاتِبٌ", render_mode="detailed", profile=True)
    ro = p.get("rendered_output") or {}
    sections = ro.get("sections") or []
    ids = [s.get("id") for s in sections]
    assert "performance_summary" in ids


def test_debug_mode_includes_profiling_when_enabled():
    from orchestrator import run
    p = run("كَاتِبٌ", render_mode="debug", profile=True)
    ro = p.get("rendered_output") or {}
    section_ids = [s.get("id") for s in ro.get("sections") or []]
    # When profile=True, augment_rendered_output_with_profiling adds performance_summary section
    assert "performance_summary" in section_ids
