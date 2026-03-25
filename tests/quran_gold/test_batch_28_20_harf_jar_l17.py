# -*- coding: utf-8 -*-
"""Batch 28.20 — unresolved PARTICLE + L4 حرف جر evidence -> resolved حرف جر."""

from __future__ import annotations

from orchestrator.l17_rule_based_i3rab import _apply_b28_20_harf_jar_from_l4
from orchestrator.pipeline_orchestrator import run_pipeline


def test_b28_20_resolves_l4_harf_jar_candidate():
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
    assert tr[0]["status"] == "resolved"
    assert tr[0]["syntactic_role"] == "حرف جر"
    assert tr[0]["i3rab_case_or_mood"] == "مبني"
    assert "B28_20_HARF_JAR" in (tr[0].get("gold_rule_refs") or [])


def test_b28_20_does_not_widen_to_non_jar_operator():
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
                        "word": "كَأَنَّ",
                        "kind": "operator",
                        "operator": {
                            "effect_signature": "ACC_TAWKID",
                            "group": {"arabic": "التوكيد والتشبيه"},
                            "note": "كأن: حرف توكيد وتشبيه",
                        },
                    }
                ]
            }
        }
    }
    _apply_b28_20_harf_jar_from_l4(tr, ["كَأَنَّ"], lo)
    assert tr[0]["status"] == "candidate"
    assert tr[0]["syntactic_role"] == "أداة"
    assert "B28_20_HARF_JAR" not in (tr[0].get("gold_rule_refs") or [])


def test_b28_20_does_not_override_resolved_token():
    tr = [
        {
            "token_id": "0",
            "grammatical_family": "PARTICLE",
            "syntactic_role": "حرف عطف",
            "status": "resolved",
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
    assert tr[0]["syntactic_role"] == "حرف عطف"
    assert "B28_20_HARF_JAR" not in (tr[0].get("gold_rule_refs") or [])


def test_pipeline_hasha_resolves_harf_jar():
    r = run_pipeline("حَاشَا زيد")
    toks = (
        ((r.get("layer_outputs") or {}).get("L17_RULE_BASED_I3RAB") or {})
        .get("transformation_result", {})
        .get("token_reasoning", [])
    )
    t0 = toks[0]
    assert t0["grammatical_family"] == "PARTICLE"
    assert t0["syntactic_role"] == "حرف جر"
    assert t0["status"] == "resolved"
    assert "B28_20_HARF_JAR" in (t0.get("gold_rule_refs") or [])


def test_pipeline_inna_not_promoted_by_b28_20():
    r = run_pipeline("إِنَّ زَيْدًا قَائِمٌ")
    toks = (
        ((r.get("layer_outputs") or {}).get("L17_RULE_BASED_I3RAB") or {})
        .get("transformation_result", {})
        .get("token_reasoning", [])
    )
    t0 = toks[0]
    assert "B28_20_HARF_JAR" not in (t0.get("gold_rule_refs") or [])
