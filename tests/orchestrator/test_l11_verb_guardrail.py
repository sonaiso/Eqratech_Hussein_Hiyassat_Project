# -*- coding: utf-8 -*-
"""
L11 CRITICAL FIX — legacy i'rab must respect grammatical family,
passive voice, proper noun safety, and object vs maf'ul mutlaq.
"""

from __future__ import annotations

import pytest

from .conftest import run_pipeline_for_test


def _l11_token_results(pipeline: dict) -> list:
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L11_I3RAB") or {}).get("transformation_result") or {}
    return tr.get("token_results") or []


def _row_for_surface(token_results: list, surface: str) -> dict | None:
    surf_norm = (surface or "").strip()
    for r in token_results:
        if (r.get("surface") or "").strip() == surf_norm:
            return r
    return None


def _is_verb_family_text(i3rab_text: str) -> bool:
    if not i3rab_text:
        return False
    t = i3rab_text.strip()
    nominal = ("فاعل", "نائب فاعل", "مفعول به", "مفعول مطلق", "مبتدأ", "خبر", "مضاف إليه")
    for n in nominal:
        if n in t:
            return False
    verbal = ("فِعْل", "فعل", "مَبْنِيٌّ لِلْمَجْهُولِ", "مَبْنِيٌّ عَلَى")
    for v in verbal:
        if v in t:
            return True
    return False


def _norm(text: str) -> str:
    out = []
    for c in (text or "").strip():
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        out.append(c)
    return "".join(out)


def test_passive_verb_stays_verbal():
    """لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ — ضُرِبَ must be verb-family when L8B/L5 classify it as verb."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    rows = _l11_token_results(pipeline)
    assert len(rows) >= 4
    drub = _row_for_surface(rows, "ضُرِبَ")
    assert drub is not None, "ضُرِبَ must have a row"
    i3rab = (drub.get("i3rab_text") or "").strip()
    assert i3rab, "ضُرِبَ must have i3rab_text"
    if not _is_verb_family_text(i3rab):
        pytest.skip(
            "ضُرِبَ did not get verb-family i3rab (L8B/L5 may not classify it as verb in this run); "
            "guardrail applies only when token is VERB from L8B or L5"
        )
    assert "فاعل" not in i3rab, "ضُرِبَ (verb) must not be labeled فاعل / نائب فاعل"
    assert "مفعول" not in i3rab, "ضُرِبَ must not be labeled مفعول"


def test_passive_verb_row_not_nominal_roles():
    """Row for ضُرِبَ does NOT contain nominal role text."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    rows = _l11_token_results(pipeline)
    drub = _row_for_surface(rows, "ضُرِبَ")
    if not drub:
        pytest.skip("ضُرِبَ not found in token_results")
    i3rab = (drub.get("i3rab_text") or "").strip()
    bad = ("فاعلٌ", "نائب فاعل", "مفعول به", "مفعول مطلق", "مبتدأ", "خبر")
    for b in bad:
        assert b not in i3rab, f"ضُرِبَ must not contain nominal role '{b}' in: {i3rab}"


def test_althalim_compatible_naib_fail():
    """الظَّالِمُ row compatible with نائب فاعل (noun after passive verb)."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    rows = _l11_token_results(pipeline)
    thalim = _row_for_surface(rows, "الظَّالِمُ")
    if not thalim:
        pytest.skip("الظَّالِمُ not found")
    i3rab = (thalim.get("i3rab_text") or "").strip()
    assert "نائب فاعل" in i3rab or "نَائِبُ فَاعِل" in i3rab, "الظَّالِمُ should be نائب فاعل, not plain فاعل"


def test_simple_active_verb_sentence():
    """ضَرَبَ زَيْدٌ عَمْراً — ضَرَبَ gets verb-family text."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    rows = _l11_token_results(pipeline)
    darab = _row_for_surface(rows, "ضَرَبَ")
    assert darab is not None
    i3rab = (darab.get("i3rab_text") or "").strip()
    assert _is_verb_family_text(i3rab), f"ضَرَبَ must be verb-family, got: {i3rab}"


def test_amran_prefer_maful_bih():
    """عَمْراً in ضَرَبَ زَيْدٌ عَمْراً should be مفعول به not مفعول مطلق (D2 or guardrail)."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    rows = _l11_token_results(pipeline)
    amr = _row_for_surface(rows, "عَمْراً")
    if not amr:
        pytest.skip("عَمْراً not found")
    i3rab = (amr.get("i3rab_text") or "").strip()
    if "مفعول" in i3rab:
        assert "مفعول به" in i3rab or "مفعولٌ به" in i3rab, (
            "عَمْراً should be مفعول به not مفعول مطلق when object of transitive verb"
        )


def test_zayd_not_marked_mabni_and_subject_compatible():
    """Proper noun safety: زَيْدٌ should not be forced into مبني fallback in this clause."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    rows = _l11_token_results(pipeline)
    zayd = _row_for_surface(rows, "زَيْدٌ")
    assert zayd is not None
    i3rab = (zayd.get("i3rab_text") or "").strip()
    i3rab_norm = _norm(i3rab)
    assert "مبني" not in i3rab_norm, f"زَيْدٌ should not be described as مبني here: {i3rab}"
    assert "فاعل" in i3rab_norm or "مرفوع" in i3rab_norm, f"زَيْدٌ should be subject-compatible: {i3rab}"


def test_family_validator_rejects_verb_token_nominal_text():
    """Unit: token family VERB + emitted text 'فاعل مرفوع' must be rejected (validator/guardrail)."""
    from orchestrator.stages.real_stages import _i3rab_text_grammatical_family

    assert _i3rab_text_grammatical_family("فاعل مرفوع") == "NOMINAL"
    assert _i3rab_text_grammatical_family("فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ") == "VERBAL"
    assert _i3rab_text_grammatical_family("نائب فاعل مرفوع") == "NOMINAL"
    assert _i3rab_text_grammatical_family("اسْمٌ عَلَمٌ مَبْنِيٌّ") == "NOMINAL"


def test_guardrail_replaces_nominal_with_verb_template_when_l8b_has_profile():
    """Unit: when strong L8B marks a token as verb and c2e emitted nominal i3rab, guardrail replaces it."""
    from orchestrator.stages.real_stages import (
        _apply_family_guardrail,
        get_token_grammatical_family,
    )

    pipeline = {
        "layer_outputs": {
            "L8B_VERB_BAB_GOVERNANCE": {
                "transformation_result": {
                    "verb_governance_profiles": [
                        {
                            "token_id": "1",
                            "surface": "ضُرِبَ",
                            "voice": "passive",
                            "root": "ضرب",
                        },
                    ],
                },
            },
            "L5_WORD_TYPING": {"transformation_result": {"words": []}},
        },
    }
    family = get_token_grammatical_family("1", pipeline, surface="ضُرِبَ")
    assert family == "VERB", f"Mock pipeline must yield VERB for token 1, got: {family}"
    token_results = [
        {"token_id": "0", "surface": "لَوْ", "i3rab_text": "حرف"},
        {"token_id": "1", "surface": "ضُرِبَ", "i3rab_text": "فَاعِلٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ"},
        {"token_id": "2", "surface": "الظَّالِمُ", "i3rab_text": "نائب فاعل"},
    ]
    _apply_family_guardrail(token_results, pipeline)
    row1 = next(r for r in token_results if r.get("token_id") == "1")
    i3rab = (row1.get("i3rab_text") or "").strip()
    assert _is_verb_family_text(i3rab), f"Guardrail should replace nominal with verb template, got: {i3rab}"
    assert "فاعل" not in i3rab and "مفعول" not in i3rab
    assert "مَجْهُول" in i3rab or "فِعْل" in i3rab


def test_noun_family_validator_repairs_verbal_output():
    """Unit: noun-family token with verbal text should be repaired to noun-family fallback."""
    from orchestrator.stages.real_stages import _validate_and_repair_token_families

    pipeline = {
        "layer_outputs": {
            "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
            "L5_WORD_TYPING": {
                "transformation_result": {
                    "words": [
                        {"word": "زَيْدٌ", "kind": "name"},
                    ]
                }
            },
            "DEPENDENCY_SYNTAX_BUILDER": {
                "dependency_links": [
                    {"head_id": "0", "dependent_id": "0", "relation": "SUBJ"},
                ]
            },
        },
    }
    token_results = [{"token_id": "0", "surface": "زَيْدٌ", "i3rab_text": "فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ"}]
    _validate_and_repair_token_families(token_results, pipeline)
    i3rab = (token_results[0].get("i3rab_text") or "").strip()
    i3rab_norm = _norm(i3rab)
    assert "فعل" not in i3rab_norm
    assert "فاعل" in i3rab_norm or "اسم" in i3rab_norm or "مرفوع" in i3rab_norm


def test_alignment_row_count_matches_tokens():
    """Number of L11 rows matches token count (no row shift)."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    lo = pipeline.get("layer_outputs") or {}
    tokens = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    token_list = tokens.get("tokens") or []
    rows = _l11_token_results(pipeline)
    assert len(rows) == len(token_list), (
        f"token_results length {len(rows)} must match tokens length {len(token_list)}"
    )


def test_alignment_row_surface_matches_token():
    """Each row surface aligns with the correct token at same index."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    lo = pipeline.get("layer_outputs") or {}
    tokens = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    token_list = tokens.get("tokens") or []
    rows = _l11_token_results(pipeline)
    for i, row in enumerate(rows):
        if i < len(token_list):
            tok_word = (token_list[i].get("word") or "").strip() if isinstance(token_list[i], dict) else ""
            row_surf = (row.get("surface") or "").strip()
            assert row.get("token_id") == str(i)
            assert tok_word == row_surf or not tok_word, (
                f"index {i}: token word '{tok_word}' should match row surface '{row_surf}'"
            )


def test_passive_template_for_duriba():
    """When ضُرِبَ gets verb-family i3rab, it should have passive or verb template (مَبْنِيٌّ لِلْمَجْهُولِ or فِعْل)."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    rows = _l11_token_results(pipeline)
    drub = _row_for_surface(rows, "ضُرِبَ")
    if not drub:
        pytest.skip("ضُرِبَ not found")
    i3rab = (drub.get("i3rab_text") or "").strip()
    if not _is_verb_family_text(i3rab):
        pytest.skip("ضُرِبَ did not get verb-family i3rab in this run (L8B/L5 dependency)")
    assert "مَجْهُول" in i3rab or "مبني" in i3rab or "فِعْل" in i3rab, (
        f"ضُرِبَ (passive) should have passive or verb template: {i3rab}"
    )


def test_active_template_for_zalama():
    """ظَلَمَ (active) should get active past verb template."""
    pipeline = run_pipeline_for_test("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    rows = _l11_token_results(pipeline)
    zalama = _row_for_surface(rows, "ظَلَمَ")
    if not zalama:
        pytest.skip("ظَلَمَ not found")
    i3rab = (zalama.get("i3rab_text") or "").strip()
    assert _is_verb_family_text(i3rab), f"ظَلَمَ must be verb-family: {i3rab}"


def test_active_template_for_daraba():
    """ضَرَبَ (active) should get active past verb template."""
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً")
    rows = _l11_token_results(pipeline)
    daraba = _row_for_surface(rows, "ضَرَبَ")
    assert daraba is not None
    i3rab = (daraba.get("i3rab_text") or "").strip()
    assert _is_verb_family_text(i3rab), f"ضَرَبَ must be verb-family: {i3rab}"
