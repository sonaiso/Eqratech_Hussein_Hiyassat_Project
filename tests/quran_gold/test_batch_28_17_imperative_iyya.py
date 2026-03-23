# -*- coding: utf-8 -*-
"""Batch 28.17 — fiʿl amr (اهْدِنَا) and detached إِيَّا… pronouns."""

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.accepted_row_serializer import (
    canonicalize_accepted_metadata,
    validate_accepted_row_invariants,
)
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision, strict_acceptance_eligible


def _dec():
    return MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="",
        notes="test",
        trace=None,
    )


def _tr(lo: dict) -> dict:
    return (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}


def _by_surface(rows: list, surf: str):
    for r in rows:
        if (r.get("surface") or "").strip() == surf:
            return r
    return None


def test_imperative_ihdina_fatiha_1_6_fragment():
    r = run_pipeline("اهْدِنَا الصِّرَاطَ الْمُسْتَقِيمَ")
    rows = _tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    v = _by_surface(rows, "اهْدِنَا")
    assert v is not None
    assert v.get("syntactic_role") == "فعل أمر"
    assert "B28_17_IMPERATIVE_AMR" in (v.get("gold_rule_refs") or [])
    o = _by_surface(rows, "الصِّرَاطَ")
    assert o is not None and "مفعول" in (o.get("syntactic_role") or "")
    n = _by_surface(rows, "الْمُسْتَقِيمَ")
    assert n is not None and "نعت" in (n.get("syntactic_role") or "")


def test_detached_iyya_fatiha_1_5_fragment():
    r = run_pipeline("إِيَّاكَ نَعْبُدُ وَإِيَّاكَ نَسْتَعِينُ")
    rows = _tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    a = _by_surface(rows, "إِيَّاكَ")
    assert a is not None and a.get("syntactic_role") == "مفعول به"
    w = _by_surface(rows, "وَإِيَّاكَ")
    assert w is not None and w.get("syntactic_role") == "معطوف"
    assert "B28_17_IYYA_DETACHED_PRONOUN" in (a.get("gold_rule_refs") or [])


def test_batch_28_15_invariants_still_hold():
    disp = "مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    can = canonicalize_accepted_metadata(
        canonical_role="mudaf_ilaih",
        system_i3rab=disp,
        gold_i3rab=disp,
        l17={
            "syntactic_role": "مضاف إليه",
            "governing_factor": "المضاف",
            "marker": "الكسرة",
            "i3rab_case_or_mood": "مجرور",
        },
        trace=None,
        dec=_dec(),
    )
    row = {
        "accepted_role": can["accepted_role"],
        "accepted_case_bucket": can["accepted_case_bucket"],
        "accepted_marker": can["accepted_marker"],
        "accepted_structured_signature": can["accepted_structured_signature"],
        "system_i3rab": can["system_i3rab"],
    }
    assert validate_accepted_row_invariants(row) == []


def test_fatiha_1_1_to_1_4_strict_tier_smoke():
    d = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="",
        notes="",
        trace=None,
    )
    assert strict_acceptance_eligible(d)


def test_batch_28_16_mudari_not_regressed():
    r = run_pipeline("يَخْشَوْنَ اللَّهَ")
    rows = _tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    v = _by_surface(rows, "يَخْشَوْنَ")
    assert v is not None
    assert v.get("syntactic_role") == "فعل مضارع"
    assert "B28_16_MUDARI3_MARFUU" in (v.get("gold_rule_refs") or [])
