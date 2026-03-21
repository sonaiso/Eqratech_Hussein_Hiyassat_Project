# -*- coding: utf-8 -*-
"""Canonical stem/root/wazn recovery + Stage 15 core links (generalized rules; no sentence literals in code paths)."""

from __future__ import annotations

import pytest

from orchestrator.arabic_word_state import rebuild_arabic_word_state_from_layers, ref_word_state_for_token
from orchestrator.dependency_syntax.builder import build_dependency_syntax
from orchestrator.l14_jamid_mushtaq import build_jamid_mushtaq


def _lo_token(
    surface: str,
    *,
    kind: str,
    l8_root: str,
    l9_tpl: str = "",
    l9_ww: str = "",
) -> dict:
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": kind}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": l8_root}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": surface, "template": l9_tpl, "word_wazn": l9_ww}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


@pytest.mark.parametrize(
    "surface",
    ["وَالصَّائِمِينَ", "وَالصَّائِمَاتِ"],
)
def test_hollow_saim_canonical_root_stem_wazn(surface: str) -> None:
    lo = _lo_token(surface, kind="noun", l8_root="ص-ي-م", l9_tpl="", l9_ww="")
    rebuild_arabic_word_state_from_layers(lo)
    st = ref_word_state_for_token(lo, "0")
    assert st.get("canonical_root") == "ص-و-م"
    assert st.get("canonical_stem") == "صائم"
    assert st.get("canonical_wazn") == "فَاعِل"
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    assert tc.get("derivational_class") == "ISM_FAIL"
    assert tc.get("jamid_or_mushtaq") == "MUSHTAQ"


def test_geminate_verb_a3add_canonical_wazn_not_fa3al_shadda() -> None:
    surface = "أَعَدَّ"
    lo = _lo_token(
        surface,
        kind="verb",
        l8_root="ع-د-د",
        l9_tpl="فَعَلَّ",
        l9_ww="فَعَلَّ",
    )
    rebuild_arabic_word_state_from_layers(lo)
    st = ref_word_state_for_token(lo, "0")
    assert st.get("canonical_root") == "ع-د-د"
    assert "عَدَّ" in (st.get("canonical_stem") or "")
    assert st.get("canonical_wazn") == "فَعَّ"
    out = build_jamid_mushtaq(lo)
    assert out["token_classifications"][0].get("derivational_class") == "VERB"


def test_non_reference_hollow_qail() -> None:
    lo = _lo_token("قَائِلٌ", kind="noun", l8_root="ق-ي-ل", l9_tpl="", l9_ww="")
    rebuild_arabic_word_state_from_layers(lo)
    st = ref_word_state_for_token(lo, "0")
    assert st.get("canonical_root") == "ق-و-ل"
    assert st.get("canonical_wazn") == "فَاعِل"


def test_stage15_a3add_subj_obj_and_no_appos_verb_noun() -> None:
    """Minimal L10B shell: nominal main clause; Pass E2 attaches SUBJ/OBJ for strong finite verb."""
    lo = {
        "L2_TOKENIZATION": {
            "transformation_result": {
                "tokens": [
                    {"word": "أَعَدَّ"},
                    {"word": "اللَّهُ"},
                    {"word": "مَّغْفِرَةً"},
                ]
            }
        },
        "L5_WORD_TYPING": {
            "transformation_result": {
                "words": [
                    {"word": "أَعَدَّ", "kind": "verb"},
                    {"word": "اللَّهُ", "kind": "noun"},
                    {"word": "مَّغْفِرَةً", "kind": "noun"},
                ]
            }
        },
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "أَعَدَّ", "root": "ع-د-د"}]}},
        "L9_WAZN_MATCHING": {
            "transformation_result": {"words": [{"word": "أَعَدَّ", "template": "فَعَلَّ", "word_wazn": ""}]}
        },
        "L8B_VERB_BAB_GOVERNANCE": {
            "transformation_result": {
                "verb_governance_profiles": [
                    {
                        "token_id": "0",
                        "surface": "أَعَدَّ",
                        "status": "resolved",
                        "transitivity": "transitive_two_objects",
                        "objects": 2,
                        "voice": "active",
                        "confidence": 0.9,
                    }
                ]
            }
        },
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": [
                    {"token_id": "0", "surface": "أَعَدَّ", "pos_hint": "verb"},
                    {"token_id": "1", "surface": "اللَّهُ", "pos_hint": "noun"},
                    {"token_id": "2", "surface": "مَّغْفِرَةً", "pos_hint": "noun"},
                ],
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
            }
        },
        "L14_JAMID_MUSHTAQ": {
            "transformation_result": {
                "token_classifications": [
                    {"token_id": 0, "surface": "أَعَدَّ", "derivational_class": "VERB"},
                    {"token_id": 1, "surface": "اللَّهُ", "derivational_class": "UNKNOWN"},
                    {"token_id": 2, "surface": "مَّغْفِرَةً", "derivational_class": "UNKNOWN"},
                ]
            }
        },
    }
    rebuild_arabic_word_state_from_layers(lo)
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    subj = [x for x in links if x.get("head_id") == "0" and x.get("dependent_id") == "1" and x.get("relation") == "SUBJ"]
    obj = [x for x in links if x.get("head_id") == "0" and x.get("dependent_id") == "2" and x.get("relation") == "OBJ"]
    assert subj, "expected verb→Allah SUBJ"
    assert obj, "expected verb→maghfira OBJ"
    appos_bad = [x for x in links if x.get("relation") == "APPOS" and x.get("head_id") == "0" and x.get("dependent_id") == "1"]
    assert not appos_bad


def test_stage15_ism_fail_does_not_obj_spill_onto_following_finite_verb() -> None:
    """
    Batch 1.1: ISM_FAIL → immediate «object» must be nominal. A strong finite verb after the participle
    starts a new verbal clause — never OBJ(Pass_E3) from participle → verb (L5 may mis-tag the verb as noun).
    """
    lo = {
        "L2_TOKENIZATION": {
            "transformation_result": {"tokens": [{"word": "وَالذَّاكِرَاتِ"}, {"word": "أَعَدَّ"}]}
        },
        "L5_WORD_TYPING": {
            "transformation_result": {
                "words": [
                    {"word": "وَالذَّاكِرَاتِ", "kind": "noun"},
                    {"word": "أَعَدَّ", "kind": "noun"},
                ]
            }
        },
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": []}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": []}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": [
                    {"token_id": "0", "surface": "وَالذَّاكِرَاتِ", "pos_hint": "noun"},
                    {"token_id": "1", "surface": "أَعَدَّ", "pos_hint": "verb"},
                ],
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
            }
        },
        "L14_JAMID_MUSHTAQ": {
            "transformation_result": {
                "token_classifications": [
                    {"token_id": 0, "surface": "وَالذَّاكِرَاتِ", "derivational_class": "ISM_FAIL"},
                    {"token_id": 1, "surface": "أَعَدَّ", "derivational_class": "VERB"},
                ]
            }
        },
    }
    ds = build_dependency_syntax(lo)
    assert ds is not None
    obj_01 = [
        x
        for x in (ds.get("dependency_links") or [])
        if x.get("head_id") == "0" and x.get("dependent_id") == "1" and x.get("relation") == "OBJ"
    ]
    assert not obj_01, "expected no ISM_FAIL→finite-verb OBJ spill"


def test_stage15_ism_fail_immediate_object() -> None:
    lo = {
        "L2_TOKENIZATION": {
            "transformation_result": {"tokens": [{"word": "وَالْحَافِظِينَ"}, {"word": "فُرُوجَهُمْ"}]}
        },
        "L5_WORD_TYPING": {
            "transformation_result": {
                "words": [
                    {"word": "وَالْحَافِظِينَ", "kind": "noun"},
                    {"word": "فُرُوجَهُمْ", "kind": "noun"},
                ]
            }
        },
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": []}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": []}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": [
                    {"token_id": "0", "surface": "وَالْحَافِظِينَ", "pos_hint": "noun"},
                    {"token_id": "1", "surface": "فُرُوجَهُمْ", "pos_hint": "noun"},
                ],
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "nominal"},
                "clause_units": [],
            }
        },
        "L14_JAMID_MUSHTAQ": {
            "transformation_result": {
                "token_classifications": [
                    {"token_id": 0, "surface": "وَالْحَافِظِينَ", "derivational_class": "ISM_FAIL"},
                    {"token_id": 1, "surface": "فُرُوجَهُمْ", "derivational_class": "UNKNOWN"},
                ]
            }
        },
    }
    ds = build_dependency_syntax(lo)
    assert ds is not None
    obj = [x for x in (ds.get("dependency_links") or []) if x.get("head_id") == "0" and x.get("dependent_id") == "1"]
    assert obj and obj[0].get("relation") == "OBJ"


def test_stage15_coord_resumes_after_participial_object_span_batch_1_2() -> None:
    """Batch 1.2: وَالذَّاكِرَاتِ COORD attaches to وَالذَّاكِرِينَ, not to كَثِيرًا (after OBJ+intensifier span)."""
    from orchestrator.pipeline_orchestrator import run_pipeline

    s = (
        "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
        "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
        "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
        "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً وَأَجْرًا عَظِيمًا"
    )
    r = run_pipeline(s)
    lo = r["layer_outputs"]
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    tr = dsb.get("transformation_result") or dsb
    links = tr.get("dependency_links") or dsb.get("dependency_links") or []
    toks = lo["L2_TOKENIZATION"]["transformation_result"]["tokens"]
    words = [t["word"] for t in toks]
    assert words[20] == "وَالذَّاكِرِينَ" and words[22] == "كَثِيرًا" and words[23] == "وَالذَّاكِرَاتِ"
    coord_to_23 = [l for l in links if l.get("relation") == "COORD" and str(l.get("dependent_id")) == "23"]
    assert coord_to_23, "expected COORD link onto وَالذَّاكِرَاتِ"
    heads = {str(l.get("head_id")) for l in coord_to_23}
    assert "20" in heads and "22" not in heads
    bad = [l for l in links if l.get("relation") == "COORD" and l.get("head_id") == "22" and l.get("dependent_id") == "23"]
    assert not bad


def test_stage15_long_inna_sentence_no_obj_spill_late_participle_to_aadda() -> None:
    """Regression: late coordinated participle must not OBJ-govern the final finite أَعَدَّ (full pipeline)."""
    from orchestrator.pipeline_orchestrator import run_pipeline

    s = (
        "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
        "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
        "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
        "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً وَأَجْرًا عَظِيمًا"
    )
    r = run_pipeline(s)
    lo = r["layer_outputs"]
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    tr = dsb.get("transformation_result") or dsb
    links = tr.get("dependency_links") or dsb.get("dependency_links") or []
    toks = lo["L2_TOKENIZATION"]["transformation_result"]["tokens"]
    words = [t["word"] for t in toks]
    assert words[23] == "وَالذَّاكِرَاتِ" and words[24] == "أَعَدَّ"
    spill = [l for l in links if l.get("relation") == "OBJ" and l.get("head_id") == "23" and l.get("dependent_id") == "24"]
    assert not spill, "participle at 23 must not attach OBJ to finite verb at 24"
    # A finite verb must never be the dependent of OBJ (object slot is nominal).
    obj_dep_aadda = [
        l
        for l in links
        if l.get("relation") == "OBJ"
        and 0 <= int(l.get("dependent_id") or -1) < len(words)
        and (words[int(l["dependent_id"])] or "").strip() == "أَعَدَّ"
    ]
    assert not obj_dep_aadda
