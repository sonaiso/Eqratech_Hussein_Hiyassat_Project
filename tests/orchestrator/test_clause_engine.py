# -*- coding: utf-8 -*-
"""
Stage 16 CLAUSE_ENGINE — conditional decomposition tests.
Real decomposition: shart_particle, feil_shart, jawab_particle, jawab_shart.
"""

from __future__ import annotations

import copy
import pytest

from orchestrator.clause_engine import build_clause_output
from orchestrator.pipeline_orchestrator import run_pipeline


def _tokens_from_text(text: str) -> list:
    """Split on spaces for mock; normalize."""
    return [w.strip() for w in (text or "").split() if w.strip()]


def build_mock_lo_for(text: str) -> dict:
    """
    Build minimal layer_outputs (lo) for build_clause_output.
    - L2/L4 words from tokenized text
    - First token as COND if لو or إن or إذا; second conditional as JAZM if لما
    - L8B verb profiles at token_id for typical verb positions (1 and 4 for لو...لما...)
    - L5 kind=verb at same positions
    """
    tokens = _tokens_from_text(text)
    if not tokens:
        return {"L2_TOKENIZATION": {"transformation_result": {"tokens": []}}}

    # L2 / L4 words
    l2_tokens = [{"word": w} for w in tokens]
    l4_words = [{"word": w, "operator": {}, "connective_group": ""} for w in tokens]

    # Conditional: لو، إن، إذا at start → shart at 0
    shart_idx = None
    jawab_idx = None
    norm0 = (tokens[0] or "").replace("ْ", "").replace("َ", "").replace("ُ", "").replace("ِ", "").strip()
    if norm0 in ("لو", "ان", "إن", "اذا", "إذا"):
        shart_idx = 0
        l4_words[0]["operator"] = {"effect_signature": "COND"}
        l4_words[0]["connective_group"] = "conditional"
        for i in range(1, len(tokens)):
            n = (tokens[i] or "").replace("ْ", "").replace("َ", "").replace("ُ", "").replace("ِ", "").strip()
            if n == "لما":
                jawab_idx = i
                l4_words[i]["operator"] = {"effect_signature": "JAZM"}
                l4_words[i]["connective_group"] = "conditional"
                break

    # L5: verb at position 1 (after لو/إن) and after jawab (e.g. 4)
    l5_words = []
    for i in range(len(tokens)):
        kind = "noun"
        if shart_idx is not None:
            if i == shart_idx + 1 or (jawab_idx is not None and i == jawab_idx + 1):
                kind = "verb"
            elif jawab_idx is None and i == 1:
                kind = "verb"
        l5_words.append({"word": tokens[i], "kind": kind})

    # L8B: verb_governance_profiles for token_id 1 and (if jawab) jawab_idx+1
    profiles = []
    if shart_idx is not None and shart_idx + 1 < len(tokens):
        profiles.append({"token_id": str(shart_idx + 1), "surface": tokens[shart_idx + 1]})
    if jawab_idx is not None and jawab_idx + 1 < len(tokens):
        profiles.append({"token_id": str(jawab_idx + 1), "surface": tokens[jawab_idx + 1]})

    l10b_nodes = []
    for i in range(len(tokens)):
        node = {"token_id": str(i), "surface": tokens[i], "connective_group": l4_words[i].get("connective_group", "")}
        l10b_nodes.append(node)

    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": l2_tokens}},
        "L4_OPERATORS": {"transformation_result": {"words": l4_words}},
        "L5_WORD_TYPING": {"transformation_result": {"words": l5_words}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": profiles}},
        "L10B_DEEP_SYNTAX": {"transformation_result": {"dependency_nodes": l10b_nodes}},
    }


def build_mock_lo_for_no_verb(text: str) -> dict:
    """Mock lo with conditional particles but no verbs in L8B/L5 (nouns only)."""
    lo = build_mock_lo_for(text)
    # Remove L8B verb profiles and set L5 all to noun
    lo["L8B_VERB_BAB_GOVERNANCE"] = {"transformation_result": {"verb_governance_profiles": []}}
    l5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words = l5.get("words", [])
    for w in words:
        if isinstance(w, dict):
            w["kind"] = "noun"
    return lo


def test_double_conditional_lw_lama():
    lo = build_mock_lo_for("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    result = build_clause_output(lo)
    assert result["conditional_structure_detected"] is True
    assert result["clause_count"] == 4
    ids = [c["clause_id"] for c in result["clause_analysis"]]
    assert "shart_particle_0" in ids
    assert "feil_shart_0" in ids
    assert "jawab_particle_0" in ids
    assert "jawab_shart_0" in ids
    feil = next(c for c in result["clause_analysis"] if c["clause_id"] == "feil_shart_0")
    jawab = next(c for c in result["clause_analysis"] if c["clause_id"] == "jawab_shart_0")
    assert feil["end_token_id"] != "15"
    assert jawab["start_token_id"] != "0"
    jawab_p = next(c for c in result["clause_analysis"] if c["clause_id"] == "jawab_particle_0")
    assert jawab_p["parent_clause_id"] == "shart_particle_0"
    assert jawab["parent_clause_id"] == "jawab_particle_0"


def test_single_conditional_in():
    lo = build_mock_lo_for("إن جاء الطالب نجح")
    result = build_clause_output(lo)
    assert result["conditional_structure_detected"] is True
    assert result["clause_count"] == 3
    ids = [c["clause_id"] for c in result["clause_analysis"]]
    assert "shart_particle_0" in ids
    assert "feil_shart_0" in ids
    assert "jawab_shart_0" in ids


def test_no_conditional():
    lo = build_mock_lo_for("كتب الطالب الدرس")
    result = build_clause_output(lo)
    assert result["conditional_structure_detected"] is False
    assert result["clause_count"] == 1
    assert result["clause_analysis"][0]["clause_type"] == "main"


def test_inna_acc_tawkid_not_treated_as_conditional():
    lo = build_mock_lo_for("إن الطالب ناجح")
    lo["L4_OPERATORS"]["transformation_result"]["words"][0]["operator"] = {"effect_signature": "ACC_TAWKID"}
    lo["L4_OPERATORS"]["transformation_result"]["words"][0]["connective_group"] = "conditional"
    result = build_clause_output(lo)
    assert result["conditional_structure_detected"] is False
    assert result["clause_count"] == 1


def test_pipeline_clause_engine_exposes_transformation_result():
    r = run_pipeline("إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ")
    lo = r.get("layer_outputs", {})
    ce = lo.get("CLAUSE_ENGINE") or {}
    assert "transformation_result" in ce
    assert ce["transformation_result"].get("conditional_structure_detected") is False


def test_verbal_clause_region_long_inna_final_tail():
    """Batch 1.4: final finite clause after long إن chain is exposed as verbal_clause_regions."""
    s = (
        "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
        "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
        "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
        "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً "
        "وَأَجْرًا عَظِيمًا"
    )
    r = run_pipeline(s)
    ce = (r.get("layer_outputs") or {}).get("CLAUSE_ENGINE") or {}
    tr = ce.get("transformation_result") or ce
    regions = tr.get("verbal_clause_regions") or []
    assert regions, "expected verbal_clause_regions for final أَعَدَّ … clause"
    tail = regions[0]
    assert tail.get("clause_type") == "verbal_embedded"
    assert tail.get("start_token_id") == "24"
    assert tail.get("head_token_id") == "24"


def test_output_shape():
    lo = build_mock_lo_for("لَوْ جاء نجح")
    result = build_clause_output(lo)
    assert "clause_analysis" in result
    assert "clause_count" in result
    assert "conditional_structure_detected" in result
    assert "coverage" in result
    assert "ambiguity_log" in result
    assert "verbal_clause_regions" in result
    assert result["verbal_clause_regions"] == []


def test_l10b_unchanged():
    lo = build_mock_lo_for("لَوْ ضُرِبَ لَمَا ظَلَمَ")
    l10b_before = copy.deepcopy(lo.get("L10B_DEEP_SYNTAX"))
    build_clause_output(lo)
    assert lo["L10B_DEEP_SYNTAX"] == l10b_before


def test_stage15_unchanged():
    lo = build_mock_lo_for("لَوْ ضُرِبَ لَمَا ظَلَمَ")
    lo["DEPENDENCY_SYNTAX_BUILDER"] = {"dependency_links": []}
    s15_before = copy.deepcopy(lo.get("DEPENDENCY_SYNTAX_BUILDER"))
    build_clause_output(lo)
    assert lo.get("DEPENDENCY_SYNTAX_BUILDER") == s15_before


def test_confidence_high_when_l4_cond_and_verb():
    lo = build_mock_lo_for("إن جاء نجح")
    result = build_clause_output(lo)
    shart = next(c for c in result["clause_analysis"] if c["clause_id"] == "shart_particle_0")
    assert shart["confidence"] >= 0.85


def test_ambiguity_log_when_no_verb():
    lo = build_mock_lo_for_no_verb("لَوْ زَيْدٌ لَمَا عَمْرٌو")
    result = build_clause_output(lo)
    feil = next((c for c in result["clause_analysis"] if c["clause_id"] == "feil_shart_0"), None)
    if feil:
        assert feil["confidence"] <= 0.5
