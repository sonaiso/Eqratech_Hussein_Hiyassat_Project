# -*- coding: utf-8 -*-
"""
Pre-Stage-13 Readiness Audit tests.
Audit key exists; readiness_score in range; required sources; readiness_band; conservative mode when roots missing.
"""

from __future__ import annotations

from orchestrator import run


REQUIRED_AUDIT_SOURCES = [
    "ROOT_EXTRACTION",
    "PATTERN_MATCH",
    "OPERATOR_DETECTION",
    "WORD_TYPING",
    "MORPHO_FEATURES",
    "SYNTAX",
    "I3RAB",
    "SEMANTIC_RHETORICAL",
    "ANALOGICAL_REASONING",
]


def test_audit_key_exists():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    assert "pre_stage13_audit" in pipeline
    audit = pipeline["pre_stage13_audit"]
    assert isinstance(audit, dict)


def test_readiness_score_in_range():
    pipeline = run("إِنَّ اللَّهَ غَفُورٌ", render_mode="detailed")
    audit = pipeline.get("pre_stage13_audit") or {}
    score = audit.get("readiness_score")
    assert score is not None
    assert isinstance(score, (int, float))
    assert 0 <= score <= 1


def test_all_required_sources_present():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    audit = pipeline.get("pre_stage13_audit") or {}
    sources = audit.get("sources") or []
    source_ids = [s.get("source") for s in sources if s.get("source")]
    for sid in REQUIRED_AUDIT_SOURCES:
        assert sid in source_ids, f"Missing audit source: {sid}"


def test_readiness_band_valid():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    audit = pipeline.get("pre_stage13_audit") or {}
    band = audit.get("readiness_band")
    assert band in ("HIGH", "MEDIUM", "LOW")


def test_conservative_mode_triggered_when_readiness_low():
    # When readiness_band is LOW, conservative_fusion_mode must be True.
    # Use "!" (no Arabic tokens) to get no tokens + no roots -> LOW -> conservative.
    pipeline = run("!", render_mode="detailed")
    audit = pipeline.get("pre_stage13_audit") or {}
    meta = pipeline.get("meta") or {}
    band = audit.get("readiness_band")
    assert band == "LOW", "Expected LOW for punctuation-only input"
    assert meta.get("conservative_fusion_mode") is True


def test_meta_fusion_readiness_set():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    meta = pipeline.get("meta") or {}
    assert "fusion_readiness" in meta
    assert meta["fusion_readiness"] in ("HIGH", "MEDIUM", "LOW")


def test_per_source_has_required_fields():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    audit = pipeline.get("pre_stage13_audit") or {}
    sources = audit.get("sources") or []
    for s in sources:
        assert "source" in s
        assert "availability" in s
        assert "structural_depth" in s
        assert "decision_reliability" in s
        assert "known_limitations" in s
        assert "fusion_weight" in s
        assert s["structural_depth"] in (0, 1, 2, 3)
        assert 0 <= s.get("fusion_weight", -1) <= 1
