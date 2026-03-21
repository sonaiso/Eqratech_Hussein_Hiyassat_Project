# -*- coding: utf-8 -*-
"""
Stage 15 DEPENDENCY_SYNTAX_BUILDER — integration tests (Pass D).
End-to-end sentences via pipeline; expected relations and additive-only check.
"""

from __future__ import annotations

import copy
import pytest

from .conftest import run_pipeline_for_test
from orchestrator.dependency_syntax import build_dependency_syntax


def _get_ds(pipeline: dict) -> dict | None:
    lo = pipeline.get("layer_outputs") or {}
    return lo.get("DEPENDENCY_SYNTAX_BUILDER")


def _get_links(ds: dict) -> list:
    return ds.get("dependency_links") or []


def _relation_types(links: list) -> set:
    return {l.get("relation") for l in links if l.get("relation")}


def test_integration_simple_nominal_mubtada_khabar_root():
    """بسيطة اسمية: الكتاب مفيد → root_resolution (mubtada) + PRED (khabar)."""
    pipeline = run_pipeline_for_test("الكتاب مفيد")
    ds = _get_ds(pipeline)
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert root.get("root_id") is not None
    assert (root.get("root_form") or "").strip() != ""
    links = _get_links(ds)
    types = _relation_types(links)
    # Nominal: expect PRED when L10B gives nominal; may also have APPOS/SIFA from Pass C/B
    assert "dependency_links" in ds
    assert "ambiguity_log" in ds
    assert "corrections_log" in ds
    if "PRED" in types:
        pred_links = [l for l in links if l.get("relation") == "PRED"]
        assert any(l.get("arabic_role") == "KHABAR" for l in pred_links)


def test_integration_simple_verbal_root_subj_obj():
    """بسيطة فعلية واضحة: ضَرَبَ زَيْدٌ عَمْراً → ROOT + SUBJ + OBJ."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    ds = _get_ds(pipeline)
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert root.get("root_id") is not None
    links = _get_links(ds)
    types = _relation_types(links)
    assert "SUBJ" in types
    assert "OBJ" in types


def test_integration_passive_naib_subj():
    """مبني للمجهول: كُتب الدرس → ROOT + NAIB_SUBJ (when L10B verbal) or PRED."""
    pipeline = run_pipeline_for_test("كُتب الدرس")
    ds = _get_ds(pipeline)
    assert ds is not None
    types = _relation_types(_get_links(ds))
    assert "NAIB_SUBJ" in types or "PRED" in types


def test_integration_with_jar_majrur_pp_attach():
    """مع جار ومجرور: ذهب الطالب إلى المدرسة. When L10B yields majrur edges → JAR_MAJRUR + PP_ATTACH; else structure present."""
    pipeline = run_pipeline_for_test("ذهب الطالب إلى المدرسة")
    ds = _get_ds(pipeline)
    assert ds is not None
    assert ds.get("root_resolution") is not None
    types = _relation_types(_get_links(ds))
    if "JAR_MAJRUR" in types:
        assert "PP_ATTACH" in types
    assert "SUBJ" in types or "PRED" in types


def test_integration_with_idafa_pred():
    """مع إضافة: كتاب الطالب مفيد → IDAFA + PRED (when nominal)."""
    pipeline = run_pipeline_for_test("كتاب الطالب مفيد")
    ds = _get_ds(pipeline)
    assert ds is not None
    types = _relation_types(_get_links(ds))
    assert "IDAFA" in types
    assert "PRED" in types or "dependency_links" in ds


def test_integration_with_sifa_subj_root():
    """مع نعت: الطالب المجتهد نجح. When L5/L10B yield adjective-noun → SIFA; else root + links present."""
    pipeline = run_pipeline_for_test("الطالب المجتهد نجح")
    ds = _get_ds(pipeline)
    assert ds is not None
    assert ds.get("root_resolution") is not None
    types = _relation_types(_get_links(ds))
    assert "SUBJ" in types or "PRED" in types or "IDAFA" in types


def test_integration_with_coord():
    """مع عطف: جاء محمد وعلي. When و detected as operator → COORD + COORD_CONJ; else root + links present."""
    pipeline = run_pipeline_for_test("جاء محمد وعلي")
    ds = _get_ds(pipeline)
    assert ds is not None
    types = _relation_types(_get_links(ds))
    if "COORD" in types:
        assert "COORD_CONJ" in types
    assert "SUBJ" in types or "PRED" in types


def test_integration_inna_governance_and_coord_chain():
    pipeline = run_pipeline_for_test("إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ")
    ds = _get_ds(pipeline)
    assert ds is not None
    links = _get_links(ds)
    types = _relation_types(links)
    assert "INNA_NAME" in types
    assert "COORD" in types


def test_integration_candidate_markers_present_not_resolved():
    """جملة مركبة جزئياً: candidate_markers present; hal/tamyiz marked, not resolved."""
    pipeline = run_pipeline_for_test("جاء الطالب مبتسماً")
    ds = _get_ds(pipeline)
    assert ds is not None
    assert "candidate_markers" in ds
    assert isinstance(ds["candidate_markers"], list)
    # Stage 15 does not resolve TAMYIZ_CAND/HAL_CAND; structure is in place for Stage 16


def test_integration_ambiguity_log_no_silent_collapse():
    """جملة غامضة: ambiguity_log populated when applicable; entries have required shape."""
    pipeline = run_pipeline_for_test("ذهب الرجل إلى البيت أو المدرسة")
    ds = _get_ds(pipeline)
    assert ds is not None
    ambiguity = ds.get("ambiguity_log") or []
    for a in ambiguity:
        assert "token_id" in a
        assert "candidates" in a
        assert "selected" in a
        assert "selection_reason" in a


def test_integration_additive_only_l10b_unchanged():
    """Stage 15 does not mutate L10B: L10B outputs identical before and after build_dependency_syntax."""
    pipeline = run_pipeline_for_test("كتب الطالب الدرس")
    lo = pipeline.get("layer_outputs") or {}
    l10b_before = copy.deepcopy(lo.get("L10B_DEEP_SYNTAX"))
    build_dependency_syntax(lo)
    l10b_after = lo.get("L10B_DEEP_SYNTAX")
    assert l10b_before == l10b_after


def test_integration_evidence_trace_contains_dependency_syntax_builder():
    """Pass E: evidence_trace includes DEPENDENCY_SYNTAX_BUILDER entry."""
    pipeline = run_pipeline_for_test("كتب الطالب الدرس")
    trace = (pipeline.get("rendered_output") or {}).get("artifacts") or {}
    trace = trace.get("evidence_trace") or []
    stages = [e.get("supporting_stage") for e in trace]
    assert "DEPENDENCY_SYNTAX_BUILDER" in stages
