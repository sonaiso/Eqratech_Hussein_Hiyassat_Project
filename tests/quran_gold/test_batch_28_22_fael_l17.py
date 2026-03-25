# -*- coding: utf-8 -*-
"""Batch 28.22 — narrow L17 فاعل fallback when Stage15 omits SUBJ (unresolved NOUN only)."""

from __future__ import annotations

import copy

from orchestrator.l17_rule_based_i3rab import (
    _apply_b28_20_harf_jar_from_l4,
    _apply_b28_21_mafool_bih_fallback,
    _apply_b28_22_fael_fallback,
    _get_tokens,
    _l12_features_by_token_id,
)
from orchestrator.pipeline_orchestrator import run_pipeline


def _tr(lo: dict) -> dict:
    return (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}


def test_b28_22_positive_missing_subj_marfuu():
    """Active finite verb + marfūʿ noun, no Stage15 links → فاعل."""
    r = run_pipeline("ظَهَرَ الْحَقُّ")
    lo = copy.deepcopy(r["layer_outputs"])
    tr = _tr(lo)["token_reasoning"]
    lo.setdefault("DEPENDENCY_SYNTAX_BUILDER", {})["dependency_links"] = []
    for e in tr:
        if str(e.get("token_id")) == "1":
            e["status"] = "unresolved"
            e["syntactic_role"] = "غير محسوم"
            e["grammatical_family"] = "NOUN"
            e["gold_rule_refs"] = []
    tokens = _get_tokens(lo)
    ce = lo.get("CLAUSE_ENGINE") or {}
    clause_analysis = ce.get("clause_analysis") or ce.get("clauses") or []
    l12_by_id = _l12_features_by_token_id(lo)
    _apply_b28_22_fael_fallback(
        tr,
        lo,
        tokens,
        lo["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or [],
        clause_analysis,
        l12_by_id,
    )
    subj = next(x for x in tr if str(x.get("token_id")) == "1")
    assert subj.get("status") == "resolved"
    assert subj.get("syntactic_role") == "فاعل"
    assert "B28_22_FAEL_FALLBACK" in (subj.get("gold_rule_refs") or [])


def test_b28_22_skips_after_harf_jar():
    """Negative: noun after resolved حرف جر — not promoted to فاعل."""
    r = run_pipeline("فِي الْبَيْتِ")
    lo = copy.deepcopy(r["layer_outputs"])
    tr = _tr(lo)["token_reasoning"]
    tokens = _get_tokens(lo)
    ce = lo.get("CLAUSE_ENGINE") or {}
    clause_analysis = ce.get("clause_analysis") or ce.get("clauses") or []
    l12_by_id = _l12_features_by_token_id(lo)
    for e in tr:
        if str(e.get("token_id")) == "1":
            e["status"] = "unresolved"
            e["syntactic_role"] = "غير محسوم"
            e["grammatical_family"] = "NOUN"
            e["gold_rule_refs"] = []
    _apply_b28_22_fael_fallback(
        tr,
        lo,
        tokens,
        lo.get("DEPENDENCY_SYNTAX_BUILDER", {}).get("dependency_links") or [],
        clause_analysis,
        l12_by_id,
    )
    t1 = next(x for x in tr if str(x.get("token_id")) == "1")
    assert "B28_22_FAEL_FALLBACK" not in (t1.get("gold_rule_refs") or [])


def test_b28_22_skips_passive_verb():
    """Passive governor — B2.2 head check fails; no B28_22."""
    r = run_pipeline("قُتِلَ زَيْدٌ")
    lo = copy.deepcopy(r["layer_outputs"])
    tr = _tr(lo)["token_reasoning"]
    lo.setdefault("DEPENDENCY_SYNTAX_BUILDER", {})["dependency_links"] = []
    for e in tr:
        if str(e.get("token_id")) == "1":
            e["status"] = "unresolved"
            e["syntactic_role"] = "غير محسوم"
            e["grammatical_family"] = "NOUN"
            e["gold_rule_refs"] = []
    tokens = _get_tokens(lo)
    ce = lo.get("CLAUSE_ENGINE") or {}
    clause_analysis = ce.get("clause_analysis") or ce.get("clauses") or []
    l12_by_id = _l12_features_by_token_id(lo)
    _apply_b28_22_fael_fallback(
        tr,
        lo,
        tokens,
        lo["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or [],
        clause_analysis,
        l12_by_id,
    )
    t1 = next(x for x in tr if str(x.get("token_id")) == "1")
    assert "B28_22_FAEL_FALLBACK" not in (t1.get("gold_rule_refs") or [])


def test_b28_20_regression_harf_jar():
    """Regression 28.20."""
    tr = [
        {
            "token_id": "0",
            "grammatical_family": "PARTICLE",
            "syntactic_role": "أداة",
            "status": "candidate",
            "reasoning_steps": [],
            "evidence_sources": [],
            "limitations": [],
        }
    ]
    lo = {
        "L4_OPERATORS": {
            "transformation_result": {
                "words": [
                    {
                        "word": "حَاشَا",
                        "kind": "operator",
                        "operator": {
                            "effect_signature": "GEN",
                            "group": {"arabic": "الجر فقط الدلالية"},
                            "note": "حاشا: حرف جر واستثناء",
                        },
                    }
                ]
            }
        }
    }
    _apply_b28_20_harf_jar_from_l4(tr, ["حَاشَا"], lo)
    assert "B28_20_HARF_JAR" in (tr[0].get("gold_rule_refs") or [])


def test_b28_21_regression_mafool_bih():
    """Regression 28.21: accusative object path still resolves."""
    r = run_pipeline("ضَرَبَ عَمْرًا")
    lo = copy.deepcopy(r["layer_outputs"])
    tr = _tr(lo)["token_reasoning"]
    lo.setdefault("DEPENDENCY_SYNTAX_BUILDER", {})["dependency_links"] = []
    for e in tr:
        if str(e.get("token_id")) == "1":
            e["status"] = "unresolved"
            e["syntactic_role"] = "غير محسوم"
            e["grammatical_family"] = "NOUN"
            e["gold_rule_refs"] = []
    tokens = _get_tokens(lo)
    ce = lo.get("CLAUSE_ENGINE") or {}
    clause_analysis = ce.get("clause_analysis") or ce.get("clauses") or []
    l12_by_id = _l12_features_by_token_id(lo)
    _apply_b28_21_mafool_bih_fallback(
        tr,
        lo,
        tokens,
        lo["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or [],
        clause_analysis,
        l12_by_id,
    )
    obj = next(x for x in tr if str(x.get("token_id")) == "1")
    assert obj.get("syntactic_role") == "مفعول به"
    assert "B28_21_MAFOOL_BIH_FALLBACK" in (obj.get("gold_rule_refs") or [])


def test_b28_17_regression_imperative_and_iyya():
    """Regression 28.17: imperative + إِيَّا… unchanged."""
    r = run_pipeline("اهْدِنَا الصِّرَاطَ الْمُسْتَقِيمَ")
    rows = _tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    v = next(x for x in rows if (x.get("surface") or "").strip() == "اهْدِنَا")
    assert v.get("syntactic_role") == "فعل أمر"
    assert "B28_17_IMPERATIVE_AMR" in (v.get("gold_rule_refs") or [])
    r2 = run_pipeline("إِيَّاكَ نَعْبُدُ")
    rows2 = _tr(r2.get("layer_outputs") or {}).get("token_reasoning") or []
    iy = next(x for x in rows2 if (x.get("surface") or "").strip() == "إِيَّاكَ")
    assert iy.get("syntactic_role") == "مفعول به"
    assert "B28_17_IYYA_DETACHED_PRONOUN" in (iy.get("gold_rule_refs") or [])
