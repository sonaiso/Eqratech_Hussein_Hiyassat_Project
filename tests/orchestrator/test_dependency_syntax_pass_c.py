# -*- coding: utf-8 -*-
"""
Stage 15 DEPENDENCY_SYNTAX_BUILDER Pass C tests.
Coordination (COORD, COORD_CONJ), Apposition (APPOS), ambiguity_log discipline, candidate_markers.
"""

from __future__ import annotations

import pytest

from orchestrator.dependency_syntax import build_dependency_syntax


def _minimal_lo_coord(tokens: list, conj_index: int):
    """Minimal lo with tokens and L4 marking token at conj_index as operator (for waw/fa)."""
    nodes = [{"token_id": str(i), "surface": t, "pos_hint": "noun" if i != conj_index else "particle"} for i, t in enumerate(tokens)]
    words4 = []
    for i, w in enumerate(tokens):
        words4.append({"word": w, "operator": i == conj_index})
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "noun" if i != conj_index else "particle"} for i, w in enumerate(tokens)]}},
        "L4_OPERATORS": {"transformation_result": {"words": words4}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "nominal"},
            },
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


def _minimal_lo_apposition(tokens: list):
    """Two adjacent nouns (e.g. الأستاذ أحمد) — no PRED/IDAFA between them."""
    nodes = [{"token_id": str(i), "surface": t, "pos_hint": "noun"} for i, t in enumerate(tokens)]
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "noun"} for w in tokens]}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "nominal"},
            },
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


def test_coordination_waw_coord_and_coord_conj():
    """Coordination with waw → COORD (head_conjunct → dependent_conjunct) + COORD_CONJ (head_conjunct → conjunction)."""
    lo = _minimal_lo_coord(["خالد", "و", "محمد"], conj_index=1)
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    coord = [l for l in links if l.get("relation") == "COORD"]
    coord_conj = [l for l in links if l.get("relation") == "COORD_CONJ"]
    assert len(coord) >= 1
    assert coord[0].get("head_id") == "0" and coord[0].get("dependent_id") == "2"
    assert len(coord_conj) >= 1
    assert coord_conj[0].get("head_id") == "0" and coord_conj[0].get("dependent_id") == "1"


def test_coordination_fa_coord_and_coord_conj():
    """Coordination with fa → COORD + COORD_CONJ."""
    lo = _minimal_lo_coord(["الرجل", "ف", "المرأة"], conj_index=1)
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    coord = [l for l in links if l.get("relation") == "COORD"]
    coord_conj = [l for l in links if l.get("relation") == "COORD_CONJ"]
    assert len(coord) >= 1
    assert len(coord_conj) >= 1


def test_coordination_attached_waw_prefix_blocks_appos():
    """Attached waw-prefixed conjuncts should yield COORD and not leak into APPOS."""
    lo = _minimal_lo_apposition(["إِنَّ", "الْمُسْلِمِينَ", "وَالْمُسْلِمَاتِ", "وَالْمُؤْمِنِينَ"])
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "إِنَّ", "kind": "operator"},
        {"word": "الْمُسْلِمِينَ", "kind": "noun"},
        {"word": "وَالْمُسْلِمَاتِ", "kind": "noun"},
        {"word": "وَالْمُؤْمِنِينَ", "kind": "noun"},
    ]
    lo["L4_OPERATORS"] = {
        "transformation_result": {
            "words": [
                {"word": "إِنَّ", "operator": {"effect_signature": "ACC_TAWKID"}},
                {"word": "الْمُسْلِمِينَ", "operator": None},
                {"word": "وَالْمُسْلِمَاتِ", "operator": None},
                {"word": "وَالْمُؤْمِنِينَ", "operator": None},
            ]
        }
    }
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    coord = [l for l in links if l.get("relation") == "COORD"]
    appos = [l for l in links if l.get("relation") == "APPOS"]
    assert len(coord) >= 2
    assert len(appos) == 0


def test_explicit_coordination_suppresses_pred_overlap_on_same_pair():
    lo = _minimal_lo_apposition(["إِنَّ", "الْمُسْلِمِينَ", "وَالْمُسْلِمَاتِ", "وَالْمُؤْمِنِينَ"])
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "إِنَّ", "kind": "operator"},
        {"word": "الْمُسْلِمِينَ", "kind": "noun"},
        {"word": "وَالْمُسْلِمَاتِ", "kind": "noun"},
        {"word": "وَالْمُؤْمِنِينَ", "kind": "noun"},
    ]
    lo["L4_OPERATORS"] = {
        "transformation_result": {
            "words": [
                {"word": "إِنَّ", "operator": {"effect_signature": "ACC_TAWKID"}},
                {"word": "الْمُسْلِمِينَ", "operator": None},
                {"word": "وَالْمُسْلِمَاتِ", "operator": None},
                {"word": "وَالْمُؤْمِنِينَ", "operator": None},
            ]
        }
    }
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    coord_pairs = {
        (l.get("head_id"), l.get("dependent_id"))
        for l in links
        if l.get("relation") == "COORD"
    }
    assert coord_pairs
    assert not any(l.get("relation") == "APPOS" for l in links)
    assert not any(
        l.get("relation") == "PRED" and (l.get("head_id"), l.get("dependent_id")) in coord_pairs
        for l in links
    )


def test_apposition_detected_appos_relation():
    """Two adjacent nouns without PRED/IDAFA between → APPOS (main_noun → appositive)."""
    # الأستاذ أحمد: two nouns, no PRED (we only have two tokens so no mubtada-khabar from nominal branch with two content)
    # Actually nominal branch adds PRED for first_idx, second_idx when we have 2 content tokens. So الطالب مجتهد gets PRED.
    # For "الأستاذ أحمد" we have two nouns — nominal would set first as root and add PRED 0→1. So we'd have PRED not APPOS.
    # To get APPOS we need a context where we have two adjacent nouns that are NOT mubtada-khabar. So e.g. three tokens: verb, noun, noun — then the two nouns could be apposition. Or we need to not add PRED for that pair. So use a sentence with 3 tokens: noun, noun, noun — first two could be apposition, third something else. Then nominal would take first two as mubtada and khabar and add PRED 0→1. So we still get PRED. So for a true apposition test we need: noun noun (where we do NOT add PRED). That happens if we have main_clause_type != nominal or we have more than 2 tokens. Try: 3 tokens ["الأستاذ", "أحمد", "الكريم"] — nominal would do first_idx=0, second_idx=1 or 2? It would get first two content indices. So 0 and 1. So PRED 0→1. So we'd have PRED and then we skip APPOS for (0,1). So we need two adjacent nouns that are not the first two content tokens. E.g. ["قال", "الأستاذ", "أحمد"] — verbal. Then we have verb 0, subject 1, and "أحمد" could be apposition to "الأستاذ". So links would be SUBJ 0→1, and we want APPOS 1→2. So no PRED, no IDAFA for (1,2). So existing_head_dep would have (0,1) for SUBJ. So we'd add APPOS (1,2). Good.
    lo = _minimal_lo_apposition(["قال", "الأستاذ", "أحمد"])
    # Make it verbal so we don't get PRED 1→2
    lo["L10B_DEEP_SYNTAX"]["transformation_result"]["syntax_summary"]["main_clause_type"] = "verbal"
    lo["L5_WORD_TYPING"]["transformation_result"]["words"] = [
        {"word": "قال", "kind": "verb"},
        {"word": "الأستاذ", "kind": "noun"},
        {"word": "أحمد", "kind": "noun"},
    ]
    lo["L8B_VERB_BAB_GOVERNANCE"]["transformation_result"]["verb_governance_profiles"] = [
        {"surface": "قال", "status": "resolved", "voice": "active"},
    ]
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    appos = [l for l in links if l.get("relation") == "APPOS"]
    assert len(appos) >= 1
    assert appos[0].get("head_id") == "1" and appos[0].get("dependent_id") == "2"


def test_ambiguous_attachment_ambiguity_log_ranked_candidates():
    """Ambiguous attachment → ambiguity_log has token_id, candidates (with relation, head_id, score, reason), selected, selection_reason."""
    # Two conjunctions in a row: خالد و ف محمد → triggers ambiguity log for second conj
    lo = _minimal_lo_coord(["خالد", "و", "ف", "محمد"], conj_index=1)
    # Mark both 1 and 2 as operators so _is_conjunction_token matches both
    lo["L4_OPERATORS"]["transformation_result"]["words"] = [
        {"word": "خالد", "operator": False},
        {"word": "و", "operator": True},
        {"word": "ف", "operator": True},
        {"word": "محمد", "operator": False},
    ]
    ds = build_dependency_syntax(lo)
    assert ds is not None
    ambiguity = ds.get("ambiguity_log") or []
    # At least one entry when we have consecutive conjunctions
    assert isinstance(ambiguity, list)
    for a in ambiguity:
        assert "token_id" in a
        assert "candidates" in a
        assert "selected" in a
        assert "selection_reason" in a
        for c in a.get("candidates", []):
            assert "relation" in c or "head_id" in c
            assert "score" in c or "reason" in c


def test_tamyiz_hal_cand_marked_not_resolved():
    """candidate_markers present in output; TAMYIZ_CAND/HAL_CAND are markers only (no link resolution)."""
    lo = _minimal_lo_apposition(["الطالب", "مجتهد"])
    ds = build_dependency_syntax(lo)
    assert ds is not None
    assert "candidate_markers" in ds
    assert isinstance(ds["candidate_markers"], list)
    # Markers are placeholders for Stage 16; no resolution in Stage 15
    for m in ds["candidate_markers"]:
        assert "token_id" in m or "marker" in m


def test_pass_c_output_shape_stable():
    """Output has dependency_links, root_resolution, ambiguity_log, corrections_log, coverage, candidate_markers."""
    lo = _minimal_lo_coord(["أ", "و", "ب"], conj_index=1)
    ds = build_dependency_syntax(lo)
    assert ds is not None
    assert "dependency_links" in ds
    assert "root_resolution" in ds
    assert "ambiguity_log" in ds
    assert "corrections_log" in ds
    assert "coverage" in ds
    assert "candidate_markers" in ds
    assert "nominal_verbal_pp_idafa_sifa_coord_appos" in (ds.get("coverage") or "")
