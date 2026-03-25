# -*- coding: utf-8 -*-
"""Master Execution Patch 16 — Stage 15: false SUBJ «فاعل» on gold مفعول به (double accusative; imperative+object)."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


def test_patch16_double_accusative_jaal_no_false_subj_appos():
    r = run_pipeline("جَعَلَ الْأَرْضَ فِرَاشًا")
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "OBJ"
        for l in links
    )
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "2" and l.get("relation") == "OBJ"
        for l in links
    )
    assert not any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "SUBJ"
        for l in links
    )
    assert not any(l.get("relation") == "APPOS" for l in links)


def test_patch16_imperative_first_object_still_obj():
    r = run_pipeline("اتَّقُوا النَّارَ")
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    assert any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "OBJ"
        for l in links
    )
    assert not any(
        l.get("head_id") == "0" and l.get("dependent_id") == "1" and l.get("relation") == "SUBJ"
        for l in links
    )
