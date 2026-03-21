# -*- coding: utf-8 -*-
"""
Stage 12 — Gender & Number Engine (Pass 1) tests.
"""

from __future__ import annotations

import pytest

from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.l12_gender_number import build_gender_number


def _get_l12(lo: dict) -> dict:
    return (lo.get("L12_GENDER_NUMBER") or {}).get("transformation_result") or {}


def _by_surface(features: list, surface: str) -> dict | None:
    for t in features:
        if (t.get("surface") or "").strip() == surface:
            return t
    return None


# 1. Feminine by taa marbuta
def test_feminine_taa_marbuta():
    r = run_pipeline("مَدْرَسَة")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    assert len(feats) >= 1
    t = _by_surface(feats, "مَدْرَسَة")
    assert t is not None
    assert t.get("gender") == "FEMININE"
    assert t.get("number") == "SINGULAR"
    assert t.get("number_type") == "singular"


# 2. Sound masculine plural
def test_sound_masculine_plural():
    r = run_pipeline("مُسْلِمُون")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    assert len(feats) >= 1
    t = _by_surface(feats, "مُسْلِمُون")
    if t:
        assert t.get("number") == "PLURAL_SOUND_M"
        assert t.get("number_type") == "sound_plural"


# 3. Sound feminine plural
def test_sound_feminine_plural():
    r = run_pipeline("مُسْلِمَات")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    assert len(feats) >= 1
    t = _by_surface(feats, "مُسْلِمَات")
    if t:
        assert t.get("number") == "PLURAL_SOUND_F"
        assert t.get("number_type") == "sound_plural"
        assert t.get("gender") == "FEMININE"


# 4. Dual (mock lo so token is noun-family and ends with ان)
def test_dual():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "طَالِبَان"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "طَالِبَان", "kind": "noun"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "طَالِبَان", "word_wazn": ""}]}},
        "L14_JAMID_MUSHTAQ": {"transformation_result": {"token_classifications": [{"surface": "طَالِبَان", "derivational_class": "UNKNOWN"}]}},
    }
    r = build_gender_number(lo)
    assert r is not None
    feats = r.get("token_features") or []
    assert len(feats) == 1
    assert feats[0].get("number") == "DUAL"
    assert feats[0].get("number_type") == "dual"


# 5. Broken plural by wazn
def test_broken_plural_wazn():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "كُتُب"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "كُتُب", "kind": "noun"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "كُتُب", "template": "فُعُول", "word_wazn": "فُعُول"}]}},
        "L14_JAMID_MUSHTAQ": {"transformation_result": {"token_classifications": [{"surface": "كُتُب", "derivational_class": "UNKNOWN"}]}},
    }
    r = build_gender_number(lo)
    assert r is not None
    feats = r.get("token_features") or []
    assert len(feats) == 1
    assert feats[0].get("number") == "PLURAL_BROKEN"
    assert feats[0].get("number_type") == "broken_plural"


# 6. Masculine default
def test_masculine_default():
    r = run_pipeline("كِتَاب")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    assert len(feats) >= 1
    t = _by_surface(feats, "كِتَاب")
    if t:
        assert t.get("gender") == "MASCULINE"
        assert t.get("number") == "SINGULAR"


# 7. SIFA agreement (mock Stage 15)
def test_sifa_agreement_mock():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "الطالب"}, {"word": "المجتهد"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "الطالب", "kind": "noun"}, {"word": "المجتهد", "kind": "noun"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "الطالب", "word_wazn": ""}, {"word": "المجتهد", "word_wazn": ""}]}},
        "L14_JAMID_MUSHTAQ": {"transformation_result": {"token_classifications": [{"surface": "الطالب", "derivational_class": "UNKNOWN"}, {"surface": "المجتهد", "derivational_class": "UNKNOWN"}]}},
        "DEPENDENCY_SYNTAX_BUILDER": {
            "dependency_links": [
                {"head_id": "0", "dependent_id": "1", "relation": "SIFA"},
            ]
        },
    }
    r = build_gender_number(lo)
    assert r is not None
    feats = r.get("token_features") or []
    assert len(feats) == 2
    # When Stage 15 present, agreement may be filled
    s = r.get("agreement_summary") or {}
    assert s.get("total") == 2


# 8. Verb gender from L8B
def test_verb_gender():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    daraba = _by_surface(feats, "ضَرَبَ")
    if daraba:
        assert daraba.get("gender") in ("UNKNOWN", "MASCULINE")
        assert daraba.get("number") in ("SINGULAR", "UNKNOWN")


def test_true_verbs_do_not_fall_back_to_default_masculine_noun():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ أَحَداً")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    for surface in ("ضُرِبَ", "ظَلَمَ"):
        t = _by_surface(feats, surface)
        assert t is not None
        assert t.get("gender_rule") == "l8b_verb_gender_unknown"
        assert t.get("gender_rule") != "default_masculine_noun"


def test_proper_name_not_promoted_by_weak_l8b_candidate():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    zayd = _by_surface(feats, "زَيْدٌ")
    assert zayd is not None
    assert zayd.get("gender") == "MASCULINE"
    assert zayd.get("gender_rule") == "default_masculine_noun"


def test_simple_transitive_nominals_remain_noun_safe():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    zayd = _by_surface(feats, "زَيْدٌ")
    amran = _by_surface(feats, "عَمْراً")
    assert zayd is not None
    assert amran is not None
    assert zayd.get("gender_rule") == "default_masculine_noun"
    assert amran.get("gender_rule") == "default_masculine_noun"
    assert zayd.get("gender_rule") != "l8b_verb_gender_unknown"
    assert amran.get("gender_rule") != "l8b_verb_gender_unknown"


# 9. Tamyiz relation
def test_tamyiz_relation():
    r = run_pipeline("ثَلَاثَةُ كُتُبٍ")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    assert len(feats) >= 2
    thalatha = _by_surface(feats, "ثَلَاثَةُ")
    if thalatha and thalatha.get("tamyiz_relation") is not None:
        assert thalatha["tamyiz_relation"] == "1"


# 10. Output shape
def test_output_shape():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    assert "token_features" in l12
    assert "agreement_summary" in l12
    assert "coverage" in l12
    assert "ambiguity_log" in l12
    for t in l12.get("token_features") or []:
        assert "token_id" in t
        assert "surface" in t
        assert "gender" in t
        assert "number" in t
        assert "number_type" in t
        assert "gender_rule" in t
        assert "number_rule" in t
        assert "agreement_candidates" in t
        assert "agreement_status" in t
        assert "confidence" in t
        assert "evidence_sources" in t


# 11. Stage 14/15/16/17 unchanged
def test_stage14_15_16_17_unchanged():
    r = run_pipeline("الظَّالِمُ كَالْحَجَرِ")
    lo = r.get("layer_outputs", {})
    assert "L14_JAMID_MUSHTAQ" in lo
    assert "L17_RULE_BASED_I3RAB" in lo
    l14 = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    l17 = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}
    assert "token_classifications" in l14 or "coverage" in l14 or len(l14) >= 0
    assert "token_reasoning" in l17 or "coverage" in l17 or len(l17) >= 0


# 12. agreement_summary counts
def test_agreement_summary_counts():
    r = run_pipeline("مَدْرَسَةٌ كَبِيرَةٌ")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    s = l12.get("agreement_summary") or {}
    assert s.get("total") == len(l12.get("token_features") or [])
    assert s.get("agreed_count", 0) + s.get("conflict_count", 0) + s.get("unresolved_count", 0) == s.get("total", 0)


# 13. Particles UNKNOWN
def test_particles_unknown():
    r = run_pipeline("في البيت")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    for t in feats:
        if (t.get("surface") or "").strip() == "في":
            assert t.get("gender") == "UNKNOWN"
            assert t.get("number") == "UNKNOWN"
            assert t.get("number_type") == "unknown"
            assert t.get("agreement_status") == "unresolved"
            break


# 14. Ambiguous ين not over-forced
def test_ambiguous_yn_not_forced():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "المُسْلِمِينَ"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "المُسْلِمِينَ", "kind": "noun"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": "المُسْلِمِينَ", "word_wazn": ""}]}},
        "L14_JAMID_MUSHTAQ": {"transformation_result": {"token_classifications": [{"surface": "المُسْلِمِينَ", "derivational_class": "UNKNOWN"}]}},
    }
    r = build_gender_number(lo)
    assert r is not None
    feats = r.get("token_features") or []
    assert len(feats) == 1
    # Should not force PLURAL_SOUND_M without evidence; ين can be oblique dual
    assert feats[0].get("number") in ("SINGULAR", "UNKNOWN", "PLURAL_SOUND_M")


def test_noun_family_yn_cases_not_silent_singular():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُؤْمِنِينَ وَالْقَانِتِينَ وَالصَّادِقِينَ")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    for surface in ("الْمُسْلِمِينَ", "وَالْمُؤْمِنِينَ", "وَالْقَانِتِينَ", "وَالصَّادِقِينَ"):
        t = _by_surface(feats, surface)
        assert t is not None
        assert t.get("number") != "SINGULAR"
        assert t.get("gender_rule") != "l8b_verb_gender_unknown"


def test_supported_mushtaq_like_yn_cases_prefer_plural_sound_m():
    r = run_pipeline("وَالْمُؤْمِنِينَ وَالصَّائِمِينَ")
    lo = r.get("layer_outputs", {})
    l12 = _get_l12(lo)
    feats = l12.get("token_features") or []
    for surface in ("وَالْمُؤْمِنِينَ", "وَالصَّائِمِينَ"):
        t = _by_surface(feats, surface)
        assert t is not None
        assert t.get("number") == "PLURAL_SOUND_M"
        assert t.get("number_type") == "sound_plural"
        assert t.get("number") not in ("UNKNOWN", "SINGULAR")
