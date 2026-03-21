# -*- coding: utf-8 -*-
"""
Stage 17 v2 — L12/L14 agreement-aware and derivational refinement tests.
"""

from __future__ import annotations

import pytest

from orchestrator.l17_rule_based_i3rab import build_rule_based_i3rab
from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.loader import load_quran_gold, lookup_i3rab


def _by_id(reasoning: list, token_id: str) -> dict | None:
    for e in reasoning:
        if str(e.get("token_id")) == token_id:
            return e
    return None


def _mock_lo(tokens: list, dependency_links: list, l12_features: list | None = None, l14_classifications: list | None = None) -> dict:
    """Minimal layer_outputs for Stage 17 with optional L12 and L14."""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "noun"} for w in tokens]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
        "DEPENDENCY_SYNTAX_BUILDER": {"dependency_links": dependency_links},
        "CLAUSE_ENGINE": {"clause_analysis": [{"clause_id": "main_0", "start_token_id": "0", "end_token_id": str(len(tokens) - 1)}]},
        "L11B_CAUSAL_I3RAB": {"transformation_result": {"token_i3rab_reasoning": []}},
    }
    if l12_features is not None:
        lo["L12_GENDER_NUMBER"] = {"transformation_result": {"token_features": l12_features}}
    if l14_classifications is not None:
        lo["L14_JAMID_MUSHTAQ"] = {
            "transformation_result": {
                "token_classifications": [
                    {"surface": c["surface"], "derivational_class": c.get("derivational_class", "UNKNOWN"), "jamid_or_mushtaq": c.get("jamid_or_mushtaq", "UNKNOWN")}
                    for c in l14_classifications
                ]
            }
        }
    return lo


# 1. Subject confidence strengthened by agreement
def test_subject_confidence_strengthened_by_agreement():
    tokens = ["ضَرَبَ", "زَيْدٌ", "عَمْراً"]
    links = [
        {"head_id": "0", "dependent_id": "1", "relation": "SUBJ"},
        {"head_id": "0", "dependent_id": "2", "relation": "OBJ"},
    ]
    l12 = [
        {"token_id": "0", "surface": "ضَرَبَ", "gender": "UNKNOWN", "number": "SINGULAR", "agreement_status": "unresolved"},
        {"token_id": "1", "surface": "زَيْدٌ", "gender": "MASCULINE", "number": "SINGULAR", "agreement_status": "agreed"},
        {"token_id": "2", "surface": "عَمْراً", "gender": "MASCULINE", "number": "SINGULAR", "agreement_status": "unresolved"},
    ]
    lo = _mock_lo(tokens, links, l12_features=l12)
    # L8B: verb at 0
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"token_id": "0", "surface": "ضَرَبَ", "status": "resolved", "voice": "active", "confidence": 0.9}
    ]
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "ضَرَبَ", "kind": "verb"},
        {"word": "زَيْدٌ", "kind": "noun"},
        {"word": "عَمْراً", "kind": "noun"},
    ]
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r1 = _by_id(result["token_reasoning"], "1")
    assert r1 is not None
    assert "فاعل" in (r1.get("syntactic_role") or "")
    # v2: L12 agreement supports فاعل
    steps = r1.get("reasoning_steps") or []
    assert any("L12" in s and ("agreement" in s or "فاعل" in s) for s in steps) or r1.get("refinement_applied") is True
    assert r1.get("confidence", 0) >= 0.75


# 2. SIFA agreement support
def test_sifa_agreement_support():
    tokens = ["الطَّالِبُ", "المُجْتَهِدُ"]
    links = [{"head_id": "0", "dependent_id": "1", "relation": "SIFA"}]
    l12 = [
        {"token_id": "0", "surface": "الطَّالِبُ", "gender": "MASCULINE", "number": "SINGULAR"},
        {"token_id": "1", "surface": "المُجْتَهِدُ", "gender": "MASCULINE", "number": "SINGULAR"},
    ]
    lo = _mock_lo(tokens, links, l12_features=l12)
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r1 = _by_id(result["token_reasoning"], "1")
    assert r1 is not None
    steps = r1.get("reasoning_steps") or []
    assert any("SIFA" in s and "L12" in s for s in steps) or r1.get("agreement_evidence") == "SIFA_agreed"
    assert r1.get("refinement_applied") is True or "Stage15:SIFA" in str(steps)


# 3. SIFA agreement conflict
def test_sifa_agreement_conflict():
    tokens = ["الطَّالِبَةُ", "المُجْتَهِدُ"]
    links = [{"head_id": "0", "dependent_id": "1", "relation": "SIFA"}]
    l12 = [
        {"token_id": "0", "surface": "الطَّالِبَةُ", "gender": "FEMININE", "number": "SINGULAR"},
        {"token_id": "1", "surface": "المُجْتَهِدُ", "gender": "MASCULINE", "number": "SINGULAR"},
    ]
    lo = _mock_lo(tokens, links, l12_features=l12)
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r1 = _by_id(result["token_reasoning"], "1")
    assert r1 is not None
    assert r1.get("agreement_evidence") == "SIFA_conflict"
    assert any("conflict" in s for s in (r1.get("reasoning_steps") or []))
    assert result.get("ambiguity_log")


# 4. JAMID safety
def test_jamid_safety():
    tokens = ["زَيْدٌ"]
    links = []
    l14 = [{"surface": "زَيْدٌ", "derivational_class": "JAMID", "jamid_or_mushtaq": "JAMID"}]
    lo = _mock_lo(tokens, links, l14_classifications=l14)
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r0 = _by_id(result["token_reasoning"], "0")
    assert r0 is not None
    steps = r0.get("reasoning_steps") or []
    assert any("JAMID" in s and "syntax" in s for s in steps) or "derivational_evidence" in r0


# 5. MASDAR caution
def test_masdar_caution():
    tokens = ["ضَرَبَ", "زَيْدٌ", "ضَرْباً"]
    links = [
        {"head_id": "0", "dependent_id": "1", "relation": "SUBJ"},
        {"head_id": "0", "dependent_id": "2", "relation": "OBJ"},
    ]
    lo = _mock_lo(tokens, links)
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"token_id": "0", "surface": "ضَرَبَ", "status": "resolved", "voice": "active", "confidence": 0.9}
    ]
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "ضَرَبَ", "kind": "verb"},
        {"word": "زَيْدٌ", "kind": "noun"},
        {"word": "ضَرْباً", "kind": "noun"},
    ]
    l14 = [
        {"surface": "ضَرَبَ", "derivational_class": "VERB", "jamid_or_mushtaq": "VERB"},
        {"surface": "زَيْدٌ", "derivational_class": "JAMID", "jamid_or_mushtaq": "JAMID"},
        {"surface": "ضَرْباً", "derivational_class": "MASDAR", "jamid_or_mushtaq": "MUSHTAQ"},
    ]
    lo["L14_JAMID_MUSHTAQ"] = {"transformation_result": {"token_classifications": l14}}
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r2 = _by_id(result["token_reasoning"], "2")
    assert r2 is not None
    assert "مفعول به" in (r2.get("syntactic_role") or "")
    assert r2.get("derivational_evidence") or any("MASDAR" in s for s in (r2.get("reasoning_steps") or []))
    assert r2.get("confidence", 1) <= 0.65 or "MASDAR" in str(r2.get("reasoning_steps"))


# 6. Tamyiz relation support
def test_tamyiz_relation_support():
    tokens = ["ثَلَاثَةُ", "كُتُبٍ"]
    links = []
    l12 = [
        {"token_id": "0", "surface": "ثَلَاثَةُ", "tamyiz_relation": "1"},
        {"token_id": "1", "surface": "كُتُبٍ", "tamyiz_relation": None},
    ]
    lo = _mock_lo(tokens, links, l12_features=l12)
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r0 = _by_id(result["token_reasoning"], "0")
    assert r0 is not None
    steps = r0.get("reasoning_steps") or []
    assert any("tamyiz" in s.lower() for s in steps)


# 7. Naib fa'il strengthened by agreement
def test_naib_fail_strengthened_by_agreement():
    tokens = ["ضُرِبَ", "الظَّالِمُ"]
    links = [{"head_id": "0", "dependent_id": "1", "relation": "NAIB_SUBJ"}]
    lo = _mock_lo(tokens, links)
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"token_id": "0", "surface": "ضُرِبَ", "status": "resolved", "voice": "passive", "confidence": 0.9}
    ]
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "ضُرِبَ", "kind": "verb"},
        {"word": "الظَّالِمُ", "kind": "noun"},
    ]
    l12 = [
        {"token_id": "0", "surface": "ضُرِبَ", "agreement_status": "unresolved"},
        {"token_id": "1", "surface": "الظَّالِمُ", "agreement_status": "agreed"},
    ]
    lo["L12_GENDER_NUMBER"] = {"transformation_result": {"token_features": l12}}
    result = build_rule_based_i3rab(lo)
    assert result is not None
    r1 = _by_id(result["token_reasoning"], "1")
    assert r1 is not None
    assert "نائب" in (r1.get("syntactic_role") or "")
    assert any("نائب" in s and "L12" in s for s in (r1.get("reasoning_steps") or [])) or r1.get("refinement_applied") is True


# 8. Output schema unchanged
def test_output_schema_unchanged():
    tokens = ["ضَرَبَ", "زَيْدٌ"]
    links = [{"head_id": "0", "dependent_id": "1", "relation": "SUBJ"}]
    lo = _mock_lo(tokens, links, l12_features=[], l14_classifications=[])
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"token_id": "0", "surface": "ضَرَبَ", "status": "resolved", "voice": "active"}
    ]
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [{"word": "ضَرَبَ", "kind": "verb"}, {"word": "زَيْدٌ", "kind": "noun"}]
    result = build_rule_based_i3rab(lo)
    assert result is not None
    assert "token_reasoning" in result
    assert "reasoning_summary" in result
    assert "coverage" in result
    assert "ambiguity_log" in result
    for e in result["token_reasoning"]:
        assert "token_id" in e
        assert "surface" in e
        assert "grammatical_family" in e
        assert "syntactic_role" in e
        assert "governing_factor" in e
        assert "i3rab_case_or_mood" in e
        assert "marker" in e
        assert "reasoning_steps" in e
        assert "evidence_sources" in e
        assert "confidence" in e
        assert "status" in e


# 9. Stage 15/16 regressions
def test_stage15_16_regressions():
    from orchestrator.pipeline_orchestrator import run_pipeline
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    result = build_rule_based_i3rab(lo)
    assert result is not None
    assert len(result["token_reasoning"]) >= 3
    assert (lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}).get("dependency_links") is not None
    assert (lo.get("CLAUSE_ENGINE") or {}).get("clause_analysis") is not None


# 10. v1 baseline when L12 or L14 missing
def test_v1_baseline_when_l12_l14_missing():
    tokens = ["ضَرَبَ", "زَيْدٌ", "عَمْراً"]
    links = [
        {"head_id": "0", "dependent_id": "1", "relation": "SUBJ"},
        {"head_id": "0", "dependent_id": "2", "relation": "OBJ"},
    ]
    lo = _mock_lo(tokens, links, l12_features=None, l14_classifications=None)
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"token_id": "0", "surface": "ضَرَبَ", "status": "resolved", "voice": "active", "confidence": 0.9}
    ]
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "ضَرَبَ", "kind": "verb"},
        {"word": "زَيْدٌ", "kind": "noun"},
        {"word": "عَمْراً", "kind": "noun"},
    ]
    assert "L12_GENDER_NUMBER" not in lo
    assert "L14_JAMID_MUSHTAQ" not in lo
    result = build_rule_based_i3rab(lo)
    assert result is not None
    assert len(result["token_reasoning"]) == 3
    r0 = _by_id(result["token_reasoning"], "0")
    r1 = _by_id(result["token_reasoning"], "1")
    r2 = _by_id(result["token_reasoning"], "2")
    assert r0 and "فعل" in (r0.get("syntactic_role") or "")
    assert r1 and "فاعل" in (r1.get("syntactic_role") or "")
    assert r2 and "مفعول به" in (r2.get("syntactic_role") or "")


def test_downstream_no_noun_family_to_verb_leakage():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُتَصَدِّقِينَ")
    lo = r.get("layer_outputs", {})
    rows = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    for surface in ("الْمُسْلِمِينَ", "وَالْمُتَصَدِّقِينَ"):
        row = next((x for x in rows if x.get("surface") == surface), None)
        assert row is not None
        assert row.get("grammatical_family") != "VERB"
        assert row.get("syntactic_role") != "فعل"


def test_downstream_masdar_pressure_reduced_for_ahadan():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ أَحَداً")
    lo = r.get("layer_outputs", {})
    l14_rows = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result", {}).get("token_classifications", [])
    l17_rows = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    a14 = next((x for x in l14_rows if x.get("surface") == "أَحَداً"), None)
    a17 = next((x for x in l17_rows if x.get("surface") == "أَحَداً"), None)
    assert a14 is not None
    assert a17 is not None
    assert not (a14.get("derivational_class") == "MASDAR" and (a14.get("confidence") or 0) >= 0.8)
    assert a17.get("grammatical_family") == "NOUN"


def test_full_reference_sentence_smoke_improves_resolved_coverage():
    sentence = (
        "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ "
        "وَالْقَانِتِينَ وَالْقَانِتَاتِ وَالصَّادِقِينَ وَالصَّادِقَاتِ "
        "وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
        "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ "
        "وَالْحَافِظِينَ فُرُوجَهُمْ وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا "
        "وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً وَأَجْرًا عَظِيمًا"
    )
    r = run_pipeline(sentence)
    lo = r.get("layer_outputs", {})
    ce = (lo.get("CLAUSE_ENGINE") or {}).get("transformation_result") or {}
    assert ce.get("conditional_structure_detected") is False
    rows = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    summary = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("reasoning_summary", {})
    assert summary.get("resolved_tokens", 0) >= 15
    for surface in ("الْمُسْلِمِينَ", "وَالْمُؤْمِنِينَ", "وَالْحَافِظِينَ", "وَالذَّاكِرِينَ", "مَّغْفِرَةً"):
        row = next((x for x in rows if x.get("surface") == surface), None)
        assert row is not None
        assert row.get("grammatical_family") != "VERB"
    aadda = next((x for x in rows if x.get("surface") == "أَعَدَّ"), None)
    allaha = next((x for x in rows if x.get("surface") == "اللَّهَ"), None)
    assert aadda is not None and aadda.get("syntactic_role") == "فعل"
    assert allaha is not None and allaha.get("syntactic_role") in ("مفعول به", "فاعل")


# --- V3 — Authentic Quranic examples (verified via data/quran_i3rab.csv + orchestrator.quran_gold.loader) ---


def test_v3_q11_hal_jamian_surah_3_103():
    """Surah 3:103 — جَمِيعًا حال منصوب; governing verb اعْتَصِمُوا (surface وَاعْتَصِمُوا)."""
    load_quran_gold()
    gold = lookup_i3rab(3, 103, "جَمِيعًا")
    assert gold is not None and "حَال" in gold
    sentence = "وَاعْتَصِمُوا بِحَبْلِ اللَّهِ جَمِيعًا"
    r = run_pipeline(sentence)
    rows = (r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    jam = next((x for x in rows if x.get("surface") == "جَمِيعًا"), None)
    assert jam is not None
    assert (jam.get("syntactic_role") or "").strip() == "حال"
    assert (jam.get("i3rab_case_or_mood") or "").strip() == "منصوب"
    assert (jam.get("marker") or "").strip() == "الفتحة"
    gf = (jam.get("governing_factor") or "")
    assert "اعْتَصِمُوا" in gf


def test_v3_q12_inna_ism_khabar_surah_49_13():
    """Surah 49:13 — إنَّ + اسم إن + خبر إن (elative كُمْ pair)."""
    load_quran_gold()
    assert lookup_i3rab(49, 13, "أَكْرَمَكُمْ") is not None
    assert lookup_i3rab(49, 13, "أَتْقَاكُمْ") is not None
    assert "خَبَر" in (lookup_i3rab(49, 13, "أَتْقَاكُمْ") or "")
    sentence = "إِنَّ أَكْرَمَكُمْ عِندَ اللَّهِ أَتْقَاكُمْ"
    r = run_pipeline(sentence)
    rows = (r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    inna = next((x for x in rows if x.get("surface") == "إِنَّ"), None)
    ism = next((x for x in rows if x.get("surface") == "أَكْرَمَكُمْ"), None)
    khabr = next((x for x in rows if x.get("surface") == "أَتْقَاكُمْ"), None)
    assert inna is not None
    assert "حرف" in (inna.get("syntactic_role") or "") or "توكيد" in (inna.get("syntactic_role") or "")
    assert ism is not None and "اسم إن" in (ism.get("syntactic_role") or "")
    assert khabr is not None and "خبر إن" in (khabr.get("syntactic_role") or "")
    assert (khabr.get("status") or "").strip() == "resolved"


def test_v3_q13_zarf_zaman_laylata_surah_2_187():
    """Surah 2:187 — لَيْلَةَ ظرف زمان منصوب (governing أُحِلَّ)."""
    load_quran_gold()
    gold = lookup_i3rab(2, 187, "لَيْلَةَ")
    assert gold is not None and "ظَرْف" in gold and "زَمَان" in gold
    sentence = "أُحِلَّ لَكُمْ لَيْلَةَ الصِّيَامِ الرَّفَثُ"
    r = run_pipeline(sentence)
    rows = (r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    lay = next((x for x in rows if x.get("surface") == "لَيْلَةَ"), None)
    assert lay is not None
    assert (lay.get("syntactic_role") or "").strip() == "ظرف زمان"
    assert (lay.get("i3rab_case_or_mood") or "").strip() == "منصوب"
    assert (lay.get("marker") or "").strip() == "الفتحة"
    assert (lay.get("status") or "").strip() == "resolved"
    assert float(lay.get("confidence") or 0) >= 0.80
    assert "أُحِلَّ" in (lay.get("governing_factor") or "")


def test_v3_q14_hal_clause_verb_yabkoon_surah_12_16():
    """Surah 12:16 — يَبْكُونَ: verbal clause in محل حال (v4 full analysis deferred)."""
    load_quran_gold()
    yb = lookup_i3rab(12, 16, "يَبْكُونَ")
    assert yb is not None and "حَال" in yb
    sentence = "وَجَاءُوا أَبَاهُمْ عِشَاءً يَبْكُونَ"
    r = run_pipeline(sentence)
    rows = (r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    yrow = next((x for x in rows if x.get("surface") == "يَبْكُونَ"), None)
    assert yrow is not None
    assert (yrow.get("syntactic_role") or "").strip() == "جملة حالية"
    assert (yrow.get("syntactic_role") or "").strip() != "فعل"
    lims = yrow.get("limitations") or []
    assert any("clause_level_hal_analysis_deferred_v4" in str(x) for x in lims)


def test_v3_q15_huwa_allah_ahad_khabar_candidate_surah_112_1():
    """Surah 112:1 fragment — اللَّهُ خبر (مرشح) in قُلْ هُوَ اللَّهُ أَحَدٌ."""
    idx = load_quran_gold()
    allah_word = next(k[2] for k in idx.keys() if k[0] == 112 and k[1] == 1 and k[2].startswith("الل"))
    assert lookup_i3rab(112, 1, allah_word) is not None
    sentence = "قُلْ هُوَ اللَّهُ أَحَدٌ"
    r = run_pipeline(sentence)
    rows = (r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result", {}).get("token_reasoning", [])
    a = next((x for x in rows if x.get("surface") == "اللَّهُ"), None)
    assert a is not None
    assert "خبر" in (a.get("syntactic_role") or "")
    assert (a.get("status") or "").strip() == "candidate"
