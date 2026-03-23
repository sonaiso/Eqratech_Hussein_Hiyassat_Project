# -*- coding: utf-8 -*-
"""Batch 28.8 — L17 targeted resolution (harf jar / wa-fa / mawsul)."""

from orchestrator.l17_rule_based_i3rab import _apply_b28_8_targeted_resolutions


def test_b28_8_harf_jar_particle_resolves():
    ent = {
        "token_id": "2",
        "grammatical_family": "PARTICLE",
        "syntactic_role": "أداة",
        "status": "candidate",
        "confidence": 0.4,
        "reasoning_steps": [],
        "evidence_sources": [],
        "limitations": [],
    }
    tokens = ["x", "y", "فِي"]
    tr = [ent]
    _apply_b28_8_targeted_resolutions(tr, tokens)
    assert tr[0]["status"] == "resolved"
    assert "حرف جر" in tr[0]["syntactic_role"]
    assert "B28_8_HARF_JAR" in (tr[0].get("gold_rule_refs") or [])


def test_b28_8_waw_atf_resolves():
    ent = {
        "token_id": "0",
        "grammatical_family": "PARTICLE",
        "syntactic_role": "أداة",
        "status": "candidate",
        "reasoning_steps": [],
        "evidence_sources": [],
        "limitations": [],
    }
    tokens = ["وَ"]
    tr = [ent]
    _apply_b28_8_targeted_resolutions(tr, tokens)
    assert tr[0]["status"] == "resolved"
    assert "عطف" in tr[0]["syntactic_role"]


def test_b28_8_mawsul_resolves():
    ent = {
        "token_id": "0",
        "grammatical_family": "NOUN",
        "syntactic_role": "غير محسوم",
        "status": "unresolved",
        "reasoning_steps": [],
        "evidence_sources": [],
        "limitations": ["noun role unresolved"],
    }
    tokens = ["الَّذِينَ"]
    tr = [ent]
    _apply_b28_8_targeted_resolutions(tr, tokens)
    assert tr[0]["status"] == "resolved"
    assert "موصول" in tr[0]["syntactic_role"]
