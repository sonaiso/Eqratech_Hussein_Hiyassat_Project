# -*- coding: utf-8 -*-
"""
Post-Stage-13 Fusion Audit tests.
Audit key exists; fusion_consistency; issue shape; presentation; fallback when fusion missing.
"""

from __future__ import annotations

from orchestrator import run


def test_post_stage13_audit_key_exists():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    assert "post_stage13_audit" in pipeline
    pa = pipeline["post_stage13_audit"]
    assert isinstance(pa, dict)


def test_fusion_consistency_is_high_medium_or_low():
    pipeline = run("إِنَّ اللَّهَ غَفُورٌ", render_mode="detailed")
    pa = pipeline.get("post_stage13_audit") or {}
    consistency = pa.get("fusion_consistency")
    assert consistency in ("high", "medium", "low")


def test_issue_objects_have_required_fields():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    pa = pipeline.get("post_stage13_audit") or {}
    issues = pa.get("issues") or []
    for i in issues:
        assert "code" in i
        assert "message" in i
        assert "severity" in i
        assert i.get("severity") in ("info", "warning", "error")


def test_detailed_rendering_includes_post_fusion_audit():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    sections = ro.get("sections") or []
    ids = [s.get("id") for s in sections]
    assert "post_stage13_fusion_audit" in ids


def test_compact_includes_fusion_audit_line():
    pipeline = run("يَا رَبِّ", render_mode="compact")
    ro = pipeline.get("rendered_output") or {}
    summary = ro.get("summary") or ""
    assert "Fusion audit:" in summary
    assert "high" in summary or "medium" in summary or "low" in summary


def test_debug_includes_post_fusion_audit_info():
    pipeline = run("كَاتِبٌ", render_mode="debug")
    ro = pipeline.get("rendered_output") or {}
    content = ""
    for s in ro.get("sections") or []:
        content += s.get("content") or ""
    assert "Post-Stage-13 Fusion Audit" in content or "fusion_consistency" in content


def test_low_readiness_or_missing_fusion_triggers_valid_fallback():
    # When audit runs after fusion, if fusion is missing we store fallback in orchestrator only when audit crashes.
    # When fusion is present but empty token_states, audit returns low consistency with MISSING_FUSION_STATE.
    pipeline = run("!", render_mode="detailed")
    pa = pipeline.get("post_stage13_audit") or {}
    assert "fusion_consistency" in pa
    assert pa.get("fusion_consistency") in ("high", "medium", "low")
    assert "issues" in pa
    assert "source_alignment" in pa
