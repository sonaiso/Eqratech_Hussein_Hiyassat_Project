# -*- coding: utf-8 -*-
"""Batch 28.10 — L17 targeted resolution (fused لل… jar; واو+الموصول)."""

from orchestrator.l17_rule_based_i3rab import _apply_b28_10_targeted_resolutions
from orchestrator.quran_gold.batch_28_10_reporting import _b28_10_surface_family, infer_promoted_from_truth_rows


def _noun_unresolved() -> dict:
    return {
        "token_id": "0",
        "grammatical_family": "NOUN",
        "syntactic_role": "غير محسوم",
        "status": "unresolved",
        "reasoning_steps": [],
        "evidence_sources": [],
        "limitations": [],
        "gold_rule_refs": [],
    }


def test_b28_10_lam_al_fused_resolves():
    ent = _noun_unresolved()
    tokens = ["لِلَّهِ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert tr[0]["status"] == "resolved"
    assert "حرف جر" in (tr[0].get("syntactic_role") or "")
    assert "B28_10_LAM_AL_FUSED" in (tr[0].get("gold_rule_refs") or [])


def test_b28_10_waw_al_mawsul_resolves():
    ent = _noun_unresolved()
    tokens = ["وَالَّذِينَ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert tr[0]["status"] == "resolved"
    assert "موصول" in (tr[0].get("syntactic_role") or "")
    assert "B28_10_WAW_AL_MAWSUL" in (tr[0].get("gold_rule_refs") or [])


def test_b28_10_regression_near_pass_fused_lam_family():
    """Fused لل* surfaces that were NOUN-blocked in 28.9 should resolve here (Fatiha-style)."""
    ent = _noun_unresolved()
    ent["token_id"] = "2"
    tokens = ["x", "y", "لِلَّهِ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert "B28_10_LAM_AL_FUSED" in (tr[0].get("gold_rule_refs") or [])


def test_b28_10_negative_lam_does_not_tag_plain_lam_ha():
    ent = _noun_unresolved()
    tokens = ["لَهُ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert "B28_10_LAM_AL_FUSED" not in (tr[0].get("gold_rule_refs") or [])


def test_b28_10_negative_waw_al_not_walid_shape():
    ent = _noun_unresolved()
    tokens = ["وَالِدٍ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert "B28_10_WAW_AL_MAWSUL" not in (tr[0].get("gold_rule_refs") or [])


def test_b28_10_negative_respects_g007_ref():
    ent = _noun_unresolved()
    ent["gold_rule_refs"] = ["G007_MAFUL_BIH"]
    tokens = ["لِلَّهِ"]
    tr = [ent]
    _apply_b28_10_targeted_resolutions(tr, tokens)
    assert "B28_10_LAM_AL_FUSED" not in (tr[0].get("gold_rule_refs") or [])


def test_reporting_surface_family_and_promoted_inference():
    assert _b28_10_surface_family("لِلَّهِ") == "lam_al_fused_jar"
    assert _b28_10_surface_family("وَالَّذِينَ") == "waw_al_mawsul_surface"
    assert _b28_10_surface_family("لَهُ") == ""
    truth = [
        {
            "surah": 1,
            "ayah": 2,
            "word": "لِلَّهِ",
            "comparator_tier_current": "strict_structural_match",
            "audit_bucket": "ACCEPTED_STRICT_TIER",
        }
    ]
    promoted, ayahs = infer_promoted_from_truth_rows(truth)
    assert len(promoted) == 1
    assert ayahs == 1
