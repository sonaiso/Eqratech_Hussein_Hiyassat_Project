# -*- coding: utf-8 -*-
"""Batch 28.23 — Stage 15: lone post-verbal accusative noun → OBJ (not SUBJ)."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


def test_b28_23_single_accusative_after_verb_is_object_not_subject():
    r = run_pipeline("ضَرَبَ عَمْرًا")
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    assert any(
        l.get("head_id") == "0"
        and l.get("dependent_id") == "1"
        and l.get("relation") == "OBJ"
        for l in links
    )
    assert not any(
        l.get("head_id") == "0"
        and l.get("dependent_id") == "1"
        and l.get("relation") == "SUBJ"
        for l in links
    )
    assert any(
        "Pass_B28_23" in (l.get("rule") or "") for l in links
    )
    tr = (r.get("layer_outputs") or {}).get("L17_RULE_BASED_I3RAB") or {}
    rows = (tr.get("transformation_result") or {}).get("token_reasoning") or []
    o = next(x for x in rows if (x.get("surface") or "").strip() == "عَمْرًا")
    assert "مفعول" in (o.get("syntactic_role") or "")


def test_b28_23_marfuu_subject_two_token_clause_unchanged():
    """Marfūʿ definite subject after verb — still SUBJ (no accusative tanwīn / object cue)."""
    r = run_pipeline("ظَهَرَ الْحَقُّ")
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    assert any(
        l.get("head_id") == "0"
        and l.get("dependent_id") == "1"
        and l.get("relation") == "SUBJ"
        for l in links
    )
