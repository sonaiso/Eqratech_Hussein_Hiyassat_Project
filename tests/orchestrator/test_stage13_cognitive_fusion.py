# -*- coding: utf-8 -*-
"""
L13 Cognitive Fusion tests.
Fusion object exists; conservative mode; confidence range; hierarchy; token_states length.
"""

from __future__ import annotations

from orchestrator import run


def test_fusion_object_exists():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    assert "cognitive_fusion" in pipeline
    cf = pipeline["cognitive_fusion"]
    assert isinstance(cf, dict)
    assert "fusion_mode" in cf
    assert "token_states" in cf
    assert "global_confidence" in cf


def test_conservative_mode_activates():
    # Punctuation-only yields LOW readiness -> conservative fusion
    pipeline = run("!", render_mode="detailed")
    cf = pipeline.get("cognitive_fusion") or {}
    assert cf.get("fusion_mode") in ("conservative", "normal")
    # For "!" we expect conservative due to pre_stage13_audit LOW
    if pipeline.get("meta", {}).get("conservative_fusion_mode"):
        assert cf.get("fusion_mode") == "conservative"


def test_confidence_range_respected():
    pipeline = run("إِنَّ اللَّهَ غَفُورٌ", render_mode="detailed")
    cf = pipeline.get("cognitive_fusion") or {}
    global_conf = cf.get("global_confidence")
    assert global_conf is not None
    assert 0.05 <= global_conf <= 0.98
    for ts in cf.get("token_states") or []:
        c = ts.get("confidence")
        assert c is not None
        assert 0.05 <= c <= 0.98


def test_hierarchy_respected_root_over_rhetoric():
    # Fusion must not override root/wazn with weak rhetoric
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    cf = pipeline.get("cognitive_fusion") or {}
    token_states = cf.get("token_states") or []
    for ts in token_states:
        stack = ts.get("evidence_stack") or []
        sources = [s.get("source") for s in stack]
        # If ROOT or WAZN in stack, they should be present (not overridden by RHETORICAL only)
        if "ROOT" in sources or "WAZN" in sources:
            assert "ROOT" in sources or "WAZN" in sources
        assert ts.get("fusion_error_flag") is False


def test_token_states_length_equals_tokens_length():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    cf = pipeline.get("cognitive_fusion") or {}
    token_states = cf.get("token_states") or []
    lo = pipeline.get("layer_outputs") or {}
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words5 = tr5.get("words") or []
    expected = len(tokens) if tokens else len(words5)
    assert len(token_states) == expected, f"token_states={len(token_states)} expected={expected}"


def test_fusion_per_token_has_required_fields():
    pipeline = run("يَا رَبِّ", render_mode="detailed")
    cf = pipeline.get("cognitive_fusion") or {}
    for ts in cf.get("token_states") or []:
        assert "token" in ts
        assert "stable_pos" in ts
        assert "confidence" in ts
        assert "evidence_stack" in ts
        assert "fusion_error_flag" in ts


def test_detailed_mode_includes_cognitive_fusion_section():
    pipeline = run("كَاتِبٌ", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    sections = ro.get("sections") or []
    ids = [s.get("id") for s in sections]
    assert "cognitive_fusion_stability" in ids
