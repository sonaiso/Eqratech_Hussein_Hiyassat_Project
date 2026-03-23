# -*- coding: utf-8 -*-
"""Batch 28.16 — mudāriʿ marfūʿ vs false مبني على الفتح; IDAFA kasra+ال; 28.15 invariants."""

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.accepted_row_serializer import (
    canonicalize_accepted_metadata,
    validate_accepted_row_invariants,
)
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision


def _dec():
    return MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="",
        notes="test",
        trace=None,
    )


def _l17_tr(lo: dict) -> dict:
    return (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}


def _by_surface(tr: list, surface: str):
    for row in tr:
        if (row.get("surface") or "").strip() == surface:
            return row
    return None


def test_mudari_marfuu_yakhshawna_not_mabni_fatha():
    """Quran 2:3 fragment — يَخْشَوْنَ is mudāriʿ marfūʿ, not ماضٍ مبني على الفتح."""
    r = run_pipeline("يَخْشَوْنَ اللَّهَ")
    tr = _l17_tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    v = _by_surface(tr, "يَخْشَوْنَ")
    assert v is not None
    assert v.get("syntactic_role") == "فعل مضارع"
    assert "مرفوع" in (v.get("i3rab_case_or_mood") or "")
    assert "B28_16_MUDARI3_MARFUU" in (v.get("gold_rule_refs") or [])


def test_mudari_marfuu_yuminuna_low_conf_passive_override():
    """2:2 fragment — L8B may label يُؤْمِنُونَ passive with low confidence; L17 restores mudāriʿ."""
    r = run_pipeline("الَّذِينَ يُؤْمِنُونَ بِالْغَيْبِ")
    tr = _l17_tr(r.get("layer_outputs") or {}).get("token_reasoning") or []
    v = _by_surface(tr, "يُؤْمِنُونَ")
    assert v is not None
    assert v.get("syntactic_role") == "فعل مضارع"
    pp = _by_surface(tr, "بِالْغَيْبِ")
    assert pp is not None
    assert "نائب" not in (pp.get("syntactic_role") or "")


def test_idafa_yawm_iddin_stage15_and_l17_roles():
    """Fatiha 1:4-style chain — يَوْمِ الدِّينِ: IDAFA link + مضاف / مضاف إليه."""
    r = run_pipeline("مَالِكِ يَوْمِ الدِّينِ")
    lo = r.get("layer_outputs") or {}
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    idafa = [x for x in (dsb.get("dependency_links") or []) if x.get("relation") == "IDAFA"]
    assert any(x.get("rule") == "Pass_B28_16_idafa_kasra_definite" for x in idafa)
    assert any(x.get("head_id") == "1" and x.get("dependent_id") == "2" for x in idafa)
    tr = _l17_tr(lo).get("token_reasoning") or []
    y = _by_surface(tr, "يَوْمِ")
    d = _by_surface(tr, "الدِّينِ")
    assert y is not None and "مضاف" in (y.get("syntactic_role") or "")
    assert d is not None and "مضاف إليه" in (d.get("syntactic_role") or "")
    assert "B28_16_IDAFA_MUDAF" in (y.get("gold_rule_refs") or [])


def test_batch_28_15_invariants_preserved():
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
    assert "," not in can["accepted_structured_signature"]


def test_regression_strict_tier_eligible_for_erqa():
    """Smoke: strict tiers remain ERQA-eligible (batch 28.4 policy)."""
    from orchestrator.quran_gold.comparator import MatchDecision, strict_acceptance_eligible

    d = MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="",
        notes="",
        trace=None,
    )
    assert strict_acceptance_eligible(d)
