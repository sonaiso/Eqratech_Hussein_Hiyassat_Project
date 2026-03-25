# -*- coding: utf-8 -*-
"""Batch 33 — fused عَلَيْهِمْ / مِمَّا → حرف جر when L4 omits operator metadata."""

from __future__ import annotations

from orchestrator.l17_rule_based_i3rab import _apply_b33_fused_harf_jar_quran_surfaces
from orchestrator.pipeline_orchestrator import run_pipeline


def test_b33_pipeline_resolves_alaihim_l4_noun_kind():
    r = run_pipeline("غَيْرِ الْمَغْضُوبِ عَلَيْهِمْ")
    toks = (
        ((r.get("layer_outputs") or {}).get("L17_RULE_BASED_I3RAB") or {})
        .get("transformation_result", {})
        .get("token_reasoning", [])
    )
    t2 = toks[2]
    assert t2["syntactic_role"] == "حرف جر"
    assert t2["status"] == "resolved"
    assert "B33_FUSED_HARF_JAR_QURAN" in (t2.get("gold_rule_refs") or [])


def test_b33_unit_skips_verb_family():
    """If L5 marks the fused surface as **verb** (mis-tag), B33 must not promote حرف جر."""
    surf = "عَلَيْهِمْ"
    tr = [
        {
            "token_id": "0",
            "grammatical_family": "NOUN",
            "syntactic_role": "غير محسوم",
            "status": "unresolved",
            "reasoning_steps": [],
            "evidence_sources": [],
            "limitations": [],
        }
    ]
    lo: dict = {
        "L4_OPERATORS": {"transformation_result": {"words": []}},
        "L5_WORD_TYPING": {
            "transformation_result": {"words": [{"word": surf, "kind": "verb"}]}
        },
    }
    _apply_b33_fused_harf_jar_quran_surfaces(tr, [surf], lo, [])
    assert "B33_FUSED_HARF_JAR_QURAN" not in (tr[0].get("gold_rule_refs") or [])


def test_b33_unit_resolves_alaihim_mock():
    tr = [
        {
            "token_id": "2",
            "grammatical_family": "NOUN",
            "syntactic_role": "غير محسوم",
            "status": "unresolved",
            "reasoning_steps": [],
            "evidence_sources": [],
            "limitations": [],
        }
    ]
    lo = {
        "L4_OPERATORS": {
            "transformation_result": {
                "words": [
                    {"word": "عَلَيْهِمْ", "kind": "noun", "operator": None},
                ]
            }
        }
    }
    _apply_b33_fused_harf_jar_quran_surfaces(tr, ["غَيْرِ", "الْمَغْضُوبِ", "عَلَيْهِمْ"], lo, [])
    assert tr[0]["syntactic_role"] == "حرف جر"
    assert tr[0]["status"] == "resolved"
    assert "B33_FUSED_HARF_JAR_QURAN" in (tr[0].get("gold_rule_refs") or [])
