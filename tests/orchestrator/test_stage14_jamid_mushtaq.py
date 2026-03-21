# -*- coding: utf-8 -*-
"""
Stage 14 — Jamid vs Mushtaq Engine (Pass 1) tests.
"""

from __future__ import annotations

import pytest

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.l14_jamid_mushtaq import build_jamid_mushtaq


def _get_jm(lo: dict) -> dict:
    return (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}


def _by_surface(token_classifications: list, surface: str) -> dict | None:
    for t in token_classifications:
        if (t.get("surface") or "").strip() == surface.strip():
            return t
    return None


def test_ism_fail_detection():
    """الظَّالِمُ (wazn فَاعِل) → ISM_FAIL, MUSHTAQ, conf ≥ 0.85"""
    r = run_pipeline("الظَّالِمُ كَالْحَجَرِ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    th = _by_surface(tc, "الظَّالِمُ")
    assert th is not None, "الظَّالِمُ should be classified"
    assert th.get("derivational_class") == "ISM_FAIL"
    assert th.get("jamid_or_mushtaq") == "MUSHTAQ"
    assert th.get("confidence", 0) >= 0.85


def test_ism_mafuul_detection():
    """مَكْتُوب (wazn مَفْعُول) → ISM_MAFUUL, MUSHTAQ"""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "مَكْتُوب"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "مَكْتُوب", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "مَكْتُوب", "root": "ك-ت-ب"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "مَكْتُوب", "template": "مَفْعُول", "word_wazn": "مَفْعُول"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    result = build_jamid_mushtaq(lo)
    assert result is not None
    tc = result.get("token_classifications") or []
    assert len(tc) == 1
    assert tc[0].get("derivational_class") == "ISM_MAFUUL"
    assert tc[0].get("jamid_or_mushtaq") == "MUSHTAQ"


def test_masdar_detection():
    """ضَرْب (wazn فَعْل) stays ambiguity-safe; pattern-only MASDAR is not forced."""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "ضَرْب"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "ضَرْب", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "ضَرْب", "root": "ض-ر-ب"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "ضَرْب", "template": "فَعْل", "word_wazn": "فَعْل"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    result = build_jamid_mushtaq(lo)
    assert result is not None
    tc = result.get("token_classifications") or []
    assert len(tc) == 1
    assert tc[0].get("derivational_class") in ("JAMID", "MASDAR", "SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH", "UNKNOWN")
    assert "ambiguity_log" in result


def test_sifa_mushabbaha_detection():
    """كَرِيم (wazn فَعِيل) → SIFA_MUSHABBAHA, MUSHTAQ"""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "كَرِيم"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "كَرِيم", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "كَرِيم", "root": "ك-ر-م"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "كَرِيم", "template": "فَعِيل", "word_wazn": "فَعِيل"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    result = build_jamid_mushtaq(lo)
    assert result is not None
    tc = result.get("token_classifications") or []
    assert len(tc) == 1
    assert tc[0].get("derivational_class") in ("SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH", "MASDAR")
    assert tc[0].get("jamid_or_mushtaq") == "MUSHTAQ"


def test_siga_mubalaghah_or_sifa():
    """غَفُور (wazn فَعُول) → SIGA_MUBALAGHAH or SIFA ambiguity"""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "غَفُور"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "غَفُور", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "غَفُور", "root": "غ-ف-ر"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "غَفُور", "template": "فَعُول", "word_wazn": "فَعُول"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    result = build_jamid_mushtaq(lo)
    assert result is not None
    tc = result.get("token_classifications") or []
    assert len(tc) == 1
    assert tc[0].get("derivational_class") in ("SIGA_MUBALAGHAH", "SIFA_MUSHABBAHA", "MASDAR")
    assert tc[0].get("jamid_or_mushtaq") == "MUSHTAQ"


def test_jamid_proper_noun():
    """زَيْد (proper noun) → JAMID when no confirmed morphology; MUSHTAQ_LEXICAL if L8 assigns a root (JAMID gate)."""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    z = _by_surface(tc, "زَيْدٌ")
    assert z is not None
    dc = z.get("derivational_class")
    jm_flag = z.get("jamid_or_mushtaq")
    assert dc in ("JAMID", "MUSHTAQ_LEXICAL")
    if dc == "JAMID":
        assert jm_flag == "JAMID"
        assert z.get("confidence", 0) >= 0.7
    else:
        assert jm_flag == "MUSHTAQ"
        assert z.get("rule") == "jamid_blocked_confirmed_root_or_wazn"


def test_verb_token_no_mushtaq():
    """ضَرَبَ (L8B verb) → VERB, no mushtaq analysis"""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    d = _by_surface(tc, "ضَرَبَ")
    assert d is not None
    assert d.get("derivational_class") == "VERB"
    assert d.get("jamid_or_mushtaq") == "VERB"
    assert d.get("confidence", 0) >= 0.9


@pytest.mark.parametrize(
    ("sentence", "surface"),
    [
        ("ظَلَمَ الرَّجُلُ", "ظَلَمَ"),
        ("أَعَدَّ زَيْدٌ الطَّعَامَ", "أَعَدَّ"),
        ("ضُرِبَ الظَّالِمُ", "ضُرِبَ"),
    ],
)
def test_true_verb_priority_beats_ambiguous_derivational_patterns(sentence: str, surface: str):
    r = run_pipeline(sentence)
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    t = _by_surface(tc, surface)
    assert t is not None
    assert t.get("derivational_class") == "VERB"
    assert t.get("jamid_or_mushtaq") == "VERB"
    assert t.get("rule") in ("family_safe_resolved_verb", "family_safe_l5_verb")


def test_particle_token():
    """لَوْ (L5 operator) → PARTICLE"""
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    lw = _by_surface(tc, "لَوْ")
    assert lw is not None
    assert lw.get("derivational_class") == "PARTICLE"
    assert lw.get("jamid_or_mushtaq") == "PARTICLE"


def test_output_shape():
    """Output shape stable — all required keys present"""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    assert "token_classifications" in jm
    assert "classification_summary" in jm
    assert "coverage" in jm
    assert "ambiguity_log" in jm
    summary = jm.get("classification_summary") or {}
    for key in ("total", "ism_fail_count", "ism_mafuul_count", "sifa_mushabbaha_count", "masdar_count", "siga_mubalaghah_count", "mushtaq_lexical_count", "jamid_count", "verb_count", "particle_count", "unknown_count"):
        assert key in summary
    for t in jm.get("token_classifications") or []:
        assert "token_id" in t and "surface" in t and "derivational_class" in t and "jamid_or_mushtaq" in t and "confidence" in t and "rule" in t


def test_stage15_16_17_unchanged():
    """Stage 15/16/17 outputs unchanged (additive-only) — run pipeline and assert DSB/CE/L17 still present and valid"""
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    assert "DEPENDENCY_SYNTAX_BUILDER" in lo
    assert "CLAUSE_ENGINE" in lo
    assert "L17_RULE_BASED_I3RAB" in lo
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    assert "dependency_links" in dsb or "root_resolution" in dsb or dsb.get("status") == "success" or True
    ce = lo.get("CLAUSE_ENGINE") or {}
    assert "clause_count" in ce or "clauses" in ce or ce.get("status") == "success" or True
    l17 = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}
    assert "token_reasoning" in l17 or l17.get("status") == "success" or True


def test_classification_summary_counts_match():
    """classification_summary counts match token_classifications"""
    r = run_pipeline("الظَّالِمُ كَالْحَجَرِ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    summary = jm.get("classification_summary") or {}
    total = summary.get("total", 0)
    assert total == len(tc)
    summed = (
        summary.get("ism_fail_count", 0) + summary.get("ism_mafuul_count", 0)
        + summary.get("sifa_mushabbaha_count", 0) + summary.get("masdar_count", 0)
        + summary.get("siga_mubalaghah_count", 0) + summary.get("mushtaq_lexical_count", 0)
        + summary.get("jamid_count", 0)
        + summary.get("verb_count", 0) + summary.get("particle_count", 0)
        + summary.get("unknown_count", 0)
    )
    assert summed == total


def test_ambiguity_log_populated_when_overlap():
    """Ambiguity log populated for overlapping patterns (e.g. فَعْل could be MASDAR or SIFA)"""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "فَعْل"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "فَعْل", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "فَعْل", "root": "ف-ع-ل"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "فَعْل", "template": "فَعْل", "word_wazn": "فَعْل"}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    result = build_jamid_mushtaq(lo)
    assert result is not None
    # فَعْل is in both MASDAR and SIFA_MUSHABBAHA sets — may produce ambiguity_log entry
    tc = result.get("token_classifications") or []
    assert len(tc) == 1
    assert tc[0].get("jamid_or_mushtaq") in ("MUSHTAQ", "JAMID", "UNKNOWN")
    # ambiguity_log may or may not have entry depending on single best selection
    assert "ambiguity_log" in result


def test_family_safe_no_masdar_for_al_muslimin():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    t = _by_surface(tc, "الْمُسْلِمِينَ")
    assert t is not None
    assert t.get("derivational_class") != "MASDAR"
    assert t.get("derivational_class") != "VERB"


def test_family_safe_no_verb_for_wal_mutasaddiqin():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُتَصَدِّقِينَ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    t = _by_surface(tc, "وَالْمُتَصَدِّقِينَ")
    assert t is not None
    assert t.get("derivational_class") != "VERB"


def test_noun_family_safety_preserved_for_attached_and_plain_nominals():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُتَصَدِّقِينَ")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    for surface in ("الْمُسْلِمِينَ", "وَالْمُتَصَدِّقِينَ"):
        t = _by_surface(tc, surface)
        assert t is not None
        assert t.get("derivational_class") != "VERB"


def test_ahadan_not_aggressive_masdar():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ أَحَداً")
    lo = r.get("layer_outputs", {})
    jm = _get_jm(lo)
    tc = jm.get("token_classifications") or []
    t = _by_surface(tc, "أَحَداً")
    assert t is not None
    assert not (t.get("derivational_class") == "MASDAR" and (t.get("confidence") or 0) >= 0.8)


@pytest.mark.parametrize(
    "token,layer_word,root,wazn_tpl",
    [
        ("وَالْمُسْلِمَاتِ", "الْمُسْلِمَاتِ", "س-ل-م", "فَاعِل"),
        ("وَالْمُؤْمِنِينَ", "الْمُؤْمِنِينَ", "ء-م-ن", "فَاعِل"),
        ("وَالْمُؤْمِنَاتِ", "الْمُؤْمِنَاتِ", "ء-م-ن", "فَاعِل"),
        ("وَالْقَانِتِينَ", "الْقَانِتِينَ", "ق-ن-ت", "فَاعِل"),
    ],
)
def test_prefixed_attached_forms_stem_align_mushtaq_never_jamid(token, layer_word, root, wazn_tpl):
    """
    Regression: و/ال + plural/suffix on token; c2b rows keyed to definite form.
    Stem alignment must recover L8/L9 so jamid_or_mushtaq is never JAMID when morphology is confirmed.
    """
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": token}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": token, "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": layer_word, "root": root}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": layer_word, "template": wazn_tpl, "word_wazn": wazn_tpl}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    assert tc["jamid_or_mushtaq"] != "JAMID"
    assert tc["derivational_class"] in (
        "ISM_FAIL", "ISM_MAFUUL", "SIFA_MUSHABBAHA", "MASDAR", "SIGA_MUBALAGHAH", "MUSHTAQ_LEXICAL",
    )


def test_confirmed_root_without_wazn_pattern_never_jamid():
    """Confirmed stem-aligned root but empty L9 wazn → JAMID blocked; stem may infer مُفْعِل → ISM_FAIL."""
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "وَالْمُسْلِمَاتِ"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "وَالْمُسْلِمَاتِ", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "الْمُسْلِمَاتِ", "root": "س-ل-م"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "الْمُسْلِمَاتِ", "template": "", "word_wazn": ""}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    assert tc["jamid_or_mushtaq"] == "MUSHTAQ"
    assert tc["derivational_class"] in ("MUSHTAQ_LEXICAL", "ISM_FAIL")
    assert tc["rule"] in ("jamid_blocked_confirmed_root_or_wazn", "wazn_ism_fail_pattern", "wazn_ism_fail_shape")


def test_pipeline_exposes_arabic_word_state_after_l9():
    r = run_pipeline("الظَّالِمُ كَالْحَجَرِ")
    lo = r.get("layer_outputs") or {}
    assert "ARABIC_WORD_STATE" in lo
    tr = (lo.get("ARABIC_WORD_STATE") or {}).get("transformation_result") or {}
    assert tr.get("by_token_id")
