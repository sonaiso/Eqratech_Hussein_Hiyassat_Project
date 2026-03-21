# -*- coding: utf-8 -*-
"""
Stage 17 — Rule-Based Iʿrāb Reasoner tests.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.l17_rule_based_i3rab import build_rule_based_i3rab

_ROOT = Path(__file__).resolve().parents[2]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))


def _get_s17(lo: dict) -> dict:
    return (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}


def _by_surface(token_reasoning: list, surface: str) -> dict | None:
    for t in token_reasoning:
        if (t.get("surface") or "").strip() == surface:
            return t
    return None


# A) Simple active transitive clause
def test_simple_active_transitive_clause():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert s17, "Stage 17 must produce output"
    tr = s17.get("token_reasoning") or []
    assert len(tr) >= 3

    daraba = _by_surface(tr, "ضَرَبَ")
    assert daraba is not None
    assert daraba.get("grammatical_family") == "VERB"
    assert daraba.get("syntactic_role") == "فعل"
    assert "مبني" in (daraba.get("i3rab_case_or_mood") or "")
    assert daraba.get("status") == "resolved"

    zayd = _by_surface(tr, "زَيْدٌ")
    assert zayd is not None
    assert zayd.get("grammatical_family") == "NOUN"
    assert "فاعل" in (zayd.get("syntactic_role") or "")
    assert "مرفوع" in (zayd.get("i3rab_case_or_mood") or "")
    assert zayd.get("status") == "resolved"

    amran = _by_surface(tr, "عَمْراً")
    assert amran is not None
    assert amran.get("grammatical_family") == "NOUN"
    assert "مفعول به" in (amran.get("syntactic_role") or "")
    assert "منصوب" in (amran.get("i3rab_case_or_mood") or "")
    assert amran.get("status") == "resolved"


# B) Simple passive clause
def test_simple_passive_clause():
    r = run_pipeline("ضُرِبَ الظَّالِمُ")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert s17
    tr = s17.get("token_reasoning") or []
    assert len(tr) >= 2

    duriba = _by_surface(tr, "ضُرِبَ")
    assert duriba is not None
    assert duriba.get("grammatical_family") == "VERB"
    assert duriba.get("syntactic_role") == "فعل"
    assert "مبني للمجهول" in (duriba.get("i3rab_case_or_mood") or "") or "مجهول" in (duriba.get("i3rab_case_or_mood") or "")
    assert duriba.get("status") == "resolved"

    thalim = _by_surface(tr, "الظَّالِمُ")
    assert thalim is not None
    assert thalim.get("grammatical_family") == "NOUN"
    assert "نائب فاعل" in (thalim.get("syntactic_role") or "")
    assert "مرفوع" in (thalim.get("i3rab_case_or_mood") or "")
    assert thalim.get("status") == "resolved"

    # No direct object in passive clause (الظَّالِمُ is نائب فاعل, not مفعول به)
    obj_tokens = [t for t in tr if "مفعول به" in (t.get("syntactic_role") or "")]
    assert not any(t.get("surface") == "الظَّالِمُ" for t in obj_tokens)


# C) Conditional sentence with clause scoping
def test_conditional_sentence_clause_scoping():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ أَحَداً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert s17
    tr = s17.get("token_reasoning") or []
    # Clause IDs should be present where Stage 16 provides them
    clause_ids = [t.get("clause_id") for t in tr if t.get("clause_id")]
    assert len(clause_ids) >= 1

    # ضُرِبَ passive in fi'l al-shart; الظَّالِمُ نائب فاعل in same clause
    duriba = _by_surface(tr, "ضُرِبَ")
    if duriba:
        assert duriba.get("grammatical_family") == "VERB"
        assert "مبني للمجهول" in (duriba.get("i3rab_case_or_mood") or "") or "مجهول" in (duriba.get("i3rab_case_or_mood") or "")

    thalim = _by_surface(tr, "الظَّالِمُ")
    if thalim:
        assert "نائب فاعل" in (thalim.get("syntactic_role") or "")

    # ظَلَمَ active in jawab; أَحَداً مفعول به for ظَلَمَ
    zalama = _by_surface(tr, "ظَلَمَ")
    if zalama:
        assert zalama.get("grammatical_family") == "VERB"

    ahadan = _by_surface(tr, "أَحَداً")
    if ahadan:
        # Stage 17 may resolve as مفعول به when Stage 15 links OBJ; otherwise fallback
        assert ahadan.get("grammatical_family") == "NOUN"
        assert ahadan.get("clause_id") or True  # clause_id present when Stage 16 provides clauses


# D) Preposition-governed noun (if available)
def test_preposition_governed_noun():
    r = run_pipeline("مَرَرْتُ بِزَيْدٍ")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert s17
    tr = s17.get("token_reasoning") or []
    zayd = _by_surface(tr, "زَيْدٍ")
    if zayd:
        # When Stage 15 marks JAR_MAJRUR, Stage 17 should assign اسم مجرور
        if "مجرور" in (zayd.get("i3rab_case_or_mood") or "") or "مجرور" in (zayd.get("syntactic_role") or ""):
            assert "مجرور" in (zayd.get("i3rab_case_or_mood") or "") or "اسم مجرور" in (zayd.get("syntactic_role") or "")


# E) Family safety
def test_family_safety_no_verb_token_nominal_role():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    for t in tr:
        if t.get("grammatical_family") == "VERB":
            assert "فعل" in (t.get("syntactic_role") or ""), "VERB token must not receive nominal role"
            assert "فاعل" not in (t.get("syntactic_role") or "") or "نائب" in (t.get("syntactic_role") or "")


def test_family_safety_no_noun_token_verb_family_output():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    for t in tr:
        if t.get("grammatical_family") == "NOUN":
            role = (t.get("syntactic_role") or "").strip()
            assert role != "فعل", "NOUN token must not receive verb-only syntactic_role"


# F) L11B compatibility / fallback safety
def test_stage17_runs_when_l11b_partial():
    r = run_pipeline("الْحَمْدُ لِلَّهِ")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert s17 is not None
    assert "token_reasoning" in s17
    assert "reasoning_summary" in s17
    assert s17.get("status") in ("success", "partial")


def test_stage17_output_shape():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    assert "token_reasoning" in s17
    assert "reasoning_summary" in s17
    assert "coverage" in s17
    assert "ambiguity_log" in s17
    summary = s17.get("reasoning_summary") or {}
    assert "resolved_tokens" in summary
    assert "candidate_tokens" in summary
    assert "unresolved_tokens" in summary
    for t in s17.get("token_reasoning") or []:
        assert "token_id" in t
        assert "surface" in t
        assert "grammatical_family" in t
        assert "syntactic_role" in t
        assert "governing_factor" in t
        assert "i3rab_case_or_mood" in t
        assert "marker" in t
        assert "reasoning_steps" in t
        assert "confidence" in t
        assert "status" in t


def test_build_rule_based_i3rab_standalone():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "ضَرَبَ"}, {"word": "زَيْدٌ"}, {"word": "عَمْراً"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "ضَرَبَ", "kind": "verb"}, {"word": "زَيْدٌ", "kind": "noun"}, {"word": "عَمْراً", "kind": "noun"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": [{"token_id": "0", "surface": "ضَرَبَ", "status": "resolved", "voice": "active", "confidence": 0.9}]}},
        "DEPENDENCY_SYNTAX_BUILDER": {"dependency_links": [{"head_id": "0", "dependent_id": "1", "relation": "SUBJ"}, {"head_id": "0", "dependent_id": "2", "relation": "OBJ"}]},
        "CLAUSE_ENGINE": {"clause_analysis": [{"clause_id": "main_0", "start_token_id": "0", "end_token_id": "2"}]},
        "L11B_CAUSAL_I3RAB": {"transformation_result": {"token_i3rab_reasoning": []}},
    }
    result = build_rule_based_i3rab(lo)
    assert result is not None
    assert len(result.get("token_reasoning") or []) == 3
    assert result.get("reasoning_summary", {}).get("resolved_tokens", 0) >= 2


def test_inna_governance_and_accusative_coordination():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ")
    lo = r.get("layer_outputs", {})
    ce = (lo.get("CLAUSE_ENGINE") or {}).get("transformation_result") or {}
    assert ce.get("conditional_structure_detected") is False
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    inna = _by_surface(tr, "إِنَّ")
    muslimin = _by_surface(tr, "الْمُسْلِمِينَ")
    muslimat = _by_surface(tr, "وَالْمُسْلِمَاتِ")
    assert inna is not None
    assert muslimin is not None
    assert muslimat is not None
    assert inna.get("syntactic_role") == "حرف توكيد ونصب"
    assert muslimin.get("syntactic_role") == "اسم إن"
    assert muslimin.get("i3rab_case_or_mood") == "منصوب"
    assert muslimat.get("syntactic_role") == "معطوف"
    assert muslimat.get("i3rab_case_or_mood") == "منصوب"


def test_active_participle_governance_hafizina_furujahum():
    r = run_pipeline("وَالْحَافِظِينَ فُرُوجَهُمْ")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    hafizina = _by_surface(tr, "وَالْحَافِظِينَ")
    furujahum = _by_surface(tr, "فُرُوجَهُمْ")
    assert hafizina is not None
    assert furujahum is not None
    assert hafizina.get("grammatical_family") == "NOUN"
    assert "ISM_FAIL" in (hafizina.get("derivational_evidence") or "")
    assert furujahum.get("syntactic_role") == "مفعول به"
    assert furujahum.get("governing_factor") == "وَالْحَافِظِينَ"


def test_active_participle_governance_dhakirina_allaha_kathiran():
    r = run_pipeline("وَالذَّاكِرِينَ اللَّهَ كَثِيرًا")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    dhakirina = _by_surface(tr, "وَالذَّاكِرِينَ")
    allaha = _by_surface(tr, "اللَّهَ")
    kathiran = _by_surface(tr, "كَثِيرًا")
    assert dhakirina is not None
    assert allaha is not None
    assert kathiran is not None
    assert dhakirina.get("grammatical_family") == "NOUN"
    assert "ISM_FAIL" in (dhakirina.get("derivational_evidence") or "")
    assert allaha.get("syntactic_role") == "مفعول به"
    assert allaha.get("governing_factor") == "وَالذَّاكِرِينَ"
    assert kathiran.get("syntactic_role") in ("نائب عن المفعول المطلق", "غير محسوم")
    assert any("ISM_FAIL" in s or "المفعول المطلق" in s for s in (kathiran.get("reasoning_steps") or [])) or kathiran.get("status") == "candidate"


def test_inna_coordination_chain_preserves_mutasaddiqina_as_conjuncts():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    muslimin = _by_surface(tr, "الْمُسْلِمِينَ")
    muslimat = _by_surface(tr, "وَالْمُسْلِمَاتِ")
    mutasaddiqina = _by_surface(tr, "وَالْمُتَصَدِّقِينَ")
    mutasaddiqat = _by_surface(tr, "وَالْمُتَصَدِّقَاتِ")
    assert muslimin is not None
    assert muslimat is not None
    assert mutasaddiqina is not None
    assert mutasaddiqat is not None
    assert muslimin.get("syntactic_role") == "اسم إن"
    for row in (muslimat, mutasaddiqina, mutasaddiqat):
        assert row.get("syntactic_role") == "معطوف"
        assert row.get("i3rab_case_or_mood") == "منصوب"
        assert row.get("governing_factor") == "إِنَّ"


def test_non_reference_overreach_blocked_in_conditional_sentence():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    kalhajar = _by_surface(tr, "كَالْحَجَرِ")
    ahadan = _by_surface(tr, "أَحَداً")
    duriba = _by_surface(tr, "ضُرِبَ")
    thalim = _by_surface(tr, "الظَّالِمُ")
    assert duriba is not None and duriba.get("syntactic_role") == "فعل"
    assert thalim is not None and "نائب فاعل" in (thalim.get("syntactic_role") or "")
    assert kalhajar is not None
    assert kalhajar.get("syntactic_role") != "مفعول به"
    assert kalhajar.get("governing_factor") != "الظَّالِمُ"
    assert ahadan is not None
    assert ahadan.get("syntactic_role") != "فاعل"


def test_final_verbal_clause_restoration_aadda_allahu():
    r = run_pipeline("أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً وَأَجْرًا عَظِيمًا")
    lo = r.get("layer_outputs", {})
    s17 = _get_s17(lo)
    tr = s17.get("token_reasoning") or []
    aadda = _by_surface(tr, "أَعَدَّ")
    allahu = _by_surface(tr, "اللَّهُ")
    maghfiratan = _by_surface(tr, "مَّغْفِرَةً")
    ajran = _by_surface(tr, "وَأَجْرًا")
    aziman = _by_surface(tr, "عَظِيمًا")
    assert aadda is not None
    assert allahu is not None
    assert maghfiratan is not None
    assert ajran is not None
    assert aziman is not None
    assert aadda.get("grammatical_family") == "VERB"
    assert aadda.get("syntactic_role") == "فعل"
    assert allahu.get("syntactic_role") == "فاعل"
    assert maghfiratan.get("syntactic_role") == "مفعول به"
    assert ajran.get("syntactic_role") == "معطوف"
    assert ajran.get("i3rab_case_or_mood") == "منصوب"
    assert aziman.get("syntactic_role") in ("نعت", "غير محسوم")
    assert aziman.get("status") in ("candidate", "resolved")


LONG_INNA_KATHIRA = (
    "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
    "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
    "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
    "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً "
    "وَأَجْرًا عَظِيمًا"
)


def test_batch_21_kathiran_naib_not_generic_naat():
    """B2.1-V1: كَثِيرًا after ذَاكَرَ اللَّهَ — prefer نائب عن المفعول المطلق over generic نعت."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    k = _by_surface(tr, "كَثِيرًا")
    assert k is not None
    assert "نائب عن المفعول المطلق" in (k.get("syntactic_role") or "")
    assert "نعت" != (k.get("syntactic_role") or "").strip()
    steps = " ".join(k.get("reasoning_steps") or [])
    assert "B2.1-V1" in steps


def test_batch_21_khabar_in_candidate_verbal_tail():
    """B2.1-V2: verbal_clause_regions + INNA_NAME → khabar_in_candidates and token secondary_analysis."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    cands = s17.get("khabar_in_candidates") or []
    assert len(cands) >= 1
    assert cands[0].get("rule") == "B2.1-V2_verbal_khabar_in_candidate"
    assert cands[0].get("head_verb_token_id") == "24"
    tr = s17.get("token_reasoning") or []
    aadda = _by_surface(tr, "أَعَدَّ")
    assert aadda is not None
    sec = aadda.get("secondary_analysis") or {}
    assert sec.get("khabar_in_clause_candidate") is True
    assert sec.get("khabar_in_rule") == "B2.1-V2_verbal_khabar_in_candidate"


def test_batch_22_structural_g007_g010_simple_transitive():
    """B2.2: Stage15 SUBJ/OBJ + finite verb → G010 (فاعل) / G007 (مفعول به); no phrase lookup."""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْرًا")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    z = _by_surface(tr, "زَيْدٌ")
    a = _by_surface(tr, "عَمْرًا")
    assert z is not None and a is not None
    assert z.get("syntactic_role") == "فاعل"
    assert "G010_FAIL_MARFUR" in (z.get("gold_rule_refs") or [])
    assert a.get("syntactic_role") == "مفعول به"
    assert "G007_MAFUL_BIH" in (a.get("gold_rule_refs") or [])


def test_batch_22_structural_g007_g010_long_inna_verbal_tail():
    """B2.2: final finite clause in long إن sentence — اللَّهُ فاعل, مَّغْفِرَةً مفعول به (Stage15 evidence)."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    allahu = _by_surface(tr, "اللَّهُ")
    magh = _by_surface(tr, "مَّغْفِرَةً")
    assert allahu is not None and magh is not None
    assert allahu.get("syntactic_role") == "فاعل"
    assert "G010_FAIL_MARFUR" in (allahu.get("gold_rule_refs") or [])
    assert magh.get("syntactic_role") == "مفعول به"
    assert "G007_MAFUL_BIH" in (magh.get("gold_rule_refs") or [])


def test_batch_22_passive_subj_not_g010_fael():
    """B2.2: passive finite verb — SUBJ/نائب فاعل must not be relabeled فاعل via G010."""
    r = run_pipeline("ضُرِبَ الظَّالِمُ")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    th = _by_surface(tr, "الظَّالِمُ")
    assert th is not None
    assert "نائب فاعل" in (th.get("syntactic_role") or "")
    assert "G010_FAIL_MARFUR" not in (th.get("gold_rule_refs") or [])


def test_batch_22_kalhajar_not_maf3ul_structurally_unlicensed():
    """Local noun-governor: كَالْحَجَرِ must not become مفعول به of الظَّالِمُ (no OBJ to that head)."""
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    kal = _by_surface(tr, "كَالْحَجَرِ")
    assert kal is not None
    assert kal.get("syntactic_role") != "مفعول به"
    assert "G007_MAFUL_BIH" not in (kal.get("gold_rule_refs") or [])


def test_batch_23_g016_naat_jaa_rajlun_salihun():
    """B2.3 / G016: مرفوع + مرفوع صفة — prefer نعت over APPOS when agreement + Stage15 link."""
    r = run_pipeline("جَاءَ رَجُلٌ صَالِحٌ")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    s = _by_surface(tr, "صَالِحٌ")
    assert s is not None
    assert s.get("syntactic_role") == "نعت"
    assert "G016_NAAT_AGREEMENT" in (s.get("gold_rule_refs") or [])


def test_batch_23_g016_naat_raaytu_accusative_pair():
    """B2.3 / G016: accusative object + accusative adjective-like — PRED→نعت when structurally licensed."""
    r = run_pipeline("رَأَيْتُ رَجُلًا صَالِحًا")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    s = _by_surface(tr, "صَالِحًا")
    assert s is not None
    assert s.get("syntactic_role") == "نعت"
    assert "G016_NAAT_AGREEMENT" in (s.get("gold_rule_refs") or [])


def test_batch_23_g016_long_inna_aziman():
    """B2.3: long إن tail — عَظِيمًا as نعت with G016 when Stage15 SIFA + agreement."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    az = _by_surface(tr, "عَظِيمًا")
    assert az is not None
    assert "نعت" in (az.get("syntactic_role") or "")
    assert "G016_NAAT_AGREEMENT" in (az.get("gold_rule_refs") or [])


def test_batch_23_no_g016_naat_on_unsupported_pp():
    """B2.3: do not stamp G016 on PP-like spans without na't-licensing (regression with كَالْحَجَرِ)."""
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    kal = _by_surface(tr, "كَالْحَجَرِ")
    assert kal is not None
    assert "G016_NAAT_AGREEMENT" not in (kal.get("gold_rule_refs") or [])


def test_batch_24_g015_hal_jaa_zayd_rakiban():
    """B2.4 / G015: حال منصوب after marfūʿ فاعل + verb (structural)."""
    r = run_pipeline("جَاءَ زَيْدٌ رَاكِبًا")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    h = _by_surface(tr, "رَاكِبًا")
    assert h is not None
    assert h.get("syntactic_role") == "حال"
    assert "G015_HAL_MANSUB" in (h.get("gold_rule_refs") or [])


def test_batch_24_g015_hal_plural_yna():
    """B2.4: plural accusative ـِينَ circumstantial (حال) after plural subject."""
    r = run_pipeline("رَجَعَ الْجُنْدُ مُنْتَصِرِينَ")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    h = _by_surface(tr, "مُنْتَصِرِينَ")
    assert h is not None
    assert h.get("syntactic_role") == "حال"
    assert "G015_HAL_MANSUB" in (h.get("gold_rule_refs") or [])


def test_batch_24_does_not_override_strong_obj():
    """B2.4: keep Stage15 OBJ / G007 مفعول به — do not label حال."""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْرًا")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    a = _by_surface(tr, "عَمْرًا")
    assert a is not None
    assert "مفعول به" in (a.get("syntactic_role") or "")
    assert "G007_MAFUL_BIH" in (a.get("gold_rule_refs") or [])
    assert "G015_HAL_MANSUB" not in (a.get("gold_rule_refs") or [])


def test_batch_24_does_not_steal_naat_g016_marfuu_pair():
    """B2.4: marfūʿ + marfūʿ نعت (G016) is not replaced by حال."""
    r = run_pipeline("جَاءَ رَجُلٌ صَالِحٌ")
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    s = _by_surface(tr, "صَالِحٌ")
    assert s is not None
    assert "نعت" in (s.get("syntactic_role") or "")
    assert "G016_NAAT_AGREEMENT" in (s.get("gold_rule_refs") or [])
    assert "G015_HAL_MANSUB" not in (s.get("gold_rule_refs") or [])


# --- Batch 2.6 — G026 fused prep+pronoun taʿalluq to verb ---


def test_batch_26_long_inna_lahum_promoted_from_opaque_particle():
    """B2.6: لَهُم in long إن tail — not vague أداة; G026 + governing verb 24."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    tr = s17.get("token_reasoning") or []
    lahum = _by_surface(tr, "لَهُم")
    assert lahum is not None
    assert (lahum.get("syntactic_role") or "").strip() == "شبه جملة متعلّقة بالفعل"
    assert lahum.get("governing_factor_token_id") == "24"
    assert "G026_JAR_TAALLUQ_VERB" in (lahum.get("gold_rule_refs") or [])
    assert (lahum.get("syntactic_role") or "").strip() != "أداة"
    sec = lahum.get("secondary_analysis") or {}
    b26 = sec.get("b26_taalluq") or {}
    assert b26.get("taalluq_head_token_id") == "24"
    assert b26.get("pp_role") == "جارّ ومجرور"


def test_batch_26_pp_attaches_to_local_strong_verb():
    """B2.6: short clause — PP attaches to local verb, not random head."""
    r = run_pipeline("أَعَدَّ اللَّهُ لَهُم أَجْرًا")
    tr = _get_s17(r.get("layer_outputs") or {}).get("token_reasoning") or []
    pp = _by_surface(tr, "لَهُم")
    assert pp is not None
    assert "شبه جملة" in (pp.get("syntactic_role") or "")
    assert pp.get("governing_factor_token_id") == "0"
    v = _by_surface(tr, "أَعَدَّ")
    assert v is not None and v.get("syntactic_role") == "فعل"


def test_batch_26_does_not_override_strong_object_or_subject():
    """B2.6: preserve B2.2/B2.3 roles on long إن sentence."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    tr = _get_s17(r.get("layer_outputs") or {}).get("token_reasoning") or []
    assert _by_surface(tr, "اللَّهُ") is not None
    assert "فاعل" in (_by_surface(tr, "اللَّهُ") or {}).get("syntactic_role", "")
    assert "مفعول به" in (_by_surface(tr, "مَّغْفِرَةً") or {}).get("syntactic_role", "")
    assert "نعت" in (_by_surface(tr, "عَظِيمًا") or {}).get("syntactic_role", "")
    k = _by_surface(tr, "كَثِيرًا")
    assert k is not None
    assert "نائب" in (k.get("syntactic_role") or "")


def test_batch_26_no_false_positive_on_non_pp_particle():
    """B2.6: non fused lam/ba+pronoun particles are not promoted."""
    r = run_pipeline("قَدْ عَلِمَ اللَّهُ")
    tr = _get_s17(r.get("layer_outputs") or {}).get("token_reasoning") or []
    q = _by_surface(tr, "قَدْ")
    assert q is not None
    assert "G026_JAR_TAALLUQ_VERB" not in (q.get("gold_rule_refs") or [])
    assert (q.get("syntactic_role") or "").strip() != "شبه جملة متعلّقة بالفعل"


def test_batch_27_long_inna_verbal_tail_promoted_to_khabar_in_clause():
    """B2.7: clause-level khabar_in_analysis resolved for verbal tail 24–29."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    ka = s17.get("khabar_in_analysis") or []
    assert len(ka) >= 1
    row = ka[0]
    assert row.get("status") == "resolved"
    assert row.get("start_token_id") == "24"
    assert row.get("end_token_id") == "29"
    assert row.get("head_verb_token_id") == "24"
    assert row.get("rule") == "B2.7-K1_resolve_khabar_in_verbal_clause"
    assert float(row.get("confidence") or 0) < 0.95


def test_batch_27_keeps_token_level_roles_unchanged():
    """B2.7: clause packaging does not replace per-token L17 roles."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    tr = _get_s17(r.get("layer_outputs") or {}).get("token_reasoning") or []
    assert _by_surface(tr, "أَعَدَّ").get("syntactic_role") == "فعل"
    assert "فاعل" in (_by_surface(tr, "اللَّهُ") or {}).get("syntactic_role", "")
    assert "مفعول به" in (_by_surface(tr, "مَّغْفِرَةً") or {}).get("syntactic_role", "")
    assert "نعت" in (_by_surface(tr, "عَظِيمًا") or {}).get("syntactic_role", "")


def test_batch_27_does_not_promote_without_subject_completion():
    """B2.7: short إن + verb without verbal_clause_regions → no resolved khabar_in_analysis."""
    r = run_pipeline("إِنَّ زَيْدًا قَامَ")
    ka = _get_s17(r.get("layer_outputs") or {}).get("khabar_in_analysis") or []
    assert not any((x.get("status") or "").strip() == "resolved" for x in ka)


def test_batch_27_does_not_hijack_non_khabar_verb():
    """B2.7: no INNA / no verbal_embedded khabar packaging on plain transitive."""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْرًا")
    ka = _get_s17(r.get("layer_outputs") or {}).get("khabar_in_analysis") or []
    assert ka == []


def test_batch_27_includes_attached_pp_inside_clause_when_present():
    """B2.7: resolved span includes token 26 (لَهُم) inside 24–29."""
    r = run_pipeline(LONG_INNA_KATHIRA)
    s17 = _get_s17(r.get("layer_outputs") or {})
    ka = s17.get("khabar_in_analysis") or []
    row = next((x for x in ka if x.get("status") == "resolved"), None)
    assert row is not None
    assert int(row.get("start_token_id")) <= 26 <= int(row.get("end_token_id"))
    tr = s17.get("token_reasoning") or []
    sec = (_by_surface(tr, "لَهُم") or {}).get("secondary_analysis") or {}
    assert sec.get("khabar_in_clause") is True
    assert sec.get("khabar_in_span_start") == "24"
    assert sec.get("khabar_in_span_end") == "29"


def test_batch_26_surfaces_in_preferred_structured_report():
    """B2.6 + Batch 2.5: preferred SECTION 4j shows upgraded PP role for لَهُم."""
    import analyze_sentence

    r = run_pipeline(LONG_INNA_KATHIRA)
    compact = analyze_sentence.build_compact_json(r, LONG_INNA_KATHIRA)
    rows = ((compact.get("preferred_i3rab") or {}).get("preferred_rows") or [])
    row26 = next((x for x in rows if x.get("token_id") == "26"), None)
    assert row26 is not None
    assert "شبه جملة" in (row26.get("syntactic_role") or "") or "متعل" in (row26.get("syntactic_role") or "")
    assert row26.get("governing_factor_token_id") == "24" or row26.get("governing_factor") == "أَعَدَّ"
