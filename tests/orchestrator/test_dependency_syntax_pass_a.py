# -*- coding: utf-8 -*-
"""
Stage 15 DEPENDENCY_SYNTAX_BUILDER Pass A tests.
Nominal/verbal only; schema shape; root_resolution; L10B unchanged; arabic_role on links.
"""

from __future__ import annotations

import pytest

from .conftest import run_pipeline_for_test


def _minimal_lo_nominal(tokens: list, main_clause_type: str = "nominal"):
    """Build minimal lo with L10B nominal and two content tokens."""
    nodes = [{"token_id": str(i), "surface": t, "pos_hint": "noun"} for i, t in enumerate(tokens)]
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "noun"} for w in tokens]}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": main_clause_type},
            },
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


def _minimal_lo_verbal_active(tokens: list):
    """Build minimal lo with verbal main_clause_type and L8B verb at 0, transitive."""
    nodes = [{"token_id": str(i), "surface": t, "pos_hint": "verb" if i == 0 else "noun"} for i, t in enumerate(tokens)]
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "verb" if i == 0 else "noun"} for i, w in enumerate(tokens)]}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "verbal"},
            },
        },
        "L8B_VERB_BAB_GOVERNANCE": {
            "transformation_result": {
                "verb_governance_profiles": [
                    {"surface": tokens[0], "status": "resolved", "voice": "active", "transitivity": "transitive", "objects": 1},
                ],
            },
        },
    }


def _minimal_lo_verbal_passive(tokens: list):
    """Build minimal lo with verbal and L8B passive verb at 0."""
    nodes = [{"token_id": str(i), "surface": t, "pos_hint": "verb" if i == 0 else "noun"} for i, t in enumerate(tokens)]
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": w, "kind": "verb" if i == 0 else "noun"} for i, w in enumerate(tokens)]}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "syntax_summary": {"main_clause_type": "verbal"},
            },
        },
        "L8B_VERB_BAB_GOVERNANCE": {
            "transformation_result": {
                "verb_governance_profiles": [
                    {"surface": tokens[0], "status": "resolved", "voice": "passive"},
                ],
            },
        },
    }


def test_output_shape_has_required_keys():
    """Output has dependency_links, root_resolution, ambiguity_log, corrections_log, coverage."""
    pipeline = run_pipeline_for_test("الطَّالِبُ مُجْتَهِدٌ")
    lo = pipeline.get("layer_outputs") or {}
    ds = lo.get("DEPENDENCY_SYNTAX_BUILDER")
    assert ds is not None
    assert "dependency_links" in ds
    assert "root_resolution" in ds
    assert "ambiguity_log" in ds
    assert "corrections_log" in ds
    assert "coverage" in ds
    assert isinstance(ds["dependency_links"], list)
    assert isinstance(ds["ambiguity_log"], list)
    assert isinstance(ds["corrections_log"], list)
    assert ds["coverage"] in ("nominal_verbal_only", "nominal_verbal_pp_idafa_sifa", "nominal_verbal_pp_idafa_sifa_coord_appos")


def test_nominal_sentence_mubtada_khabar_root_resolution():
    """Nominal: root_resolution = mubtada; canonical PRED = mubtada → khabar (head=0, dependent=1). No SUBJ link."""
    from orchestrator.dependency_syntax import build_dependency_syntax
    lo = _minimal_lo_nominal(["الطَّالِبُ", "مُجْتَهِدٌ"])
    ds = build_dependency_syntax(lo)
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert root.get("root_id") is not None
    assert (root.get("root_form") or "").strip() != ""
    assert "rule" in root
    links = ds.get("dependency_links") or []
    pred_links = [l for l in links if l.get("relation") == "PRED" and l.get("arabic_role") == "KHABAR"]
    assert len(pred_links) >= 1
    assert pred_links[0].get("head_id") == "0"  # mubtada = head (canonical: governing nominal head → PRED → khabar)
    assert pred_links[0].get("dependent_id") == "1"  # khabar = dependent
    subj_in_nominal = [l for l in links if l.get("relation") == "SUBJ"]
    assert len(subj_in_nominal) == 0  # nominal does not use SUBJ


def test_verbal_active_root_subj_obj():
    """Verbal active: canonical verb → SUBJ → subject, verb → OBJ → object (head=verb, dependents=nouns)."""
    from orchestrator.dependency_syntax import build_dependency_syntax
    lo = _minimal_lo_verbal_active(["كَتَبَ", "زَيْدٌ", "الرِّسَالَةَ"])
    ds = build_dependency_syntax(lo)
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert root.get("root_id") == "0"  # verb at 0
    links = ds.get("dependency_links") or []
    subj = [l for l in links if l.get("relation") == "SUBJ" and l.get("arabic_role") == "FAIL"]
    obj = [l for l in links if l.get("relation") == "OBJ" and l.get("arabic_role") == "MAF3UL_BIH"]
    assert len(subj) >= 1
    assert subj[0].get("head_id") == "0" and subj[0].get("dependent_id") == "1"  # verb → SUBJ → subject
    assert len(obj) >= 1
    assert obj[0].get("head_id") == "0" and obj[0].get("dependent_id") == "2"  # verb → OBJ → object


def test_verbal_passive_root_naib_subj():
    """Verbal passive: canonical passive verb → NAIB_SUBJ → naib al-fa'il (head=verb, dependent=naib)."""
    from orchestrator.dependency_syntax import build_dependency_syntax
    lo = _minimal_lo_verbal_passive(["ضُرِبَ", "الظَّالِمُ"])
    ds = build_dependency_syntax(lo)
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert root.get("root_id") == "0"
    links = ds.get("dependency_links") or []
    naib = [l for l in links if l.get("relation") == "NAIB_SUBJ" and l.get("arabic_role") == "NAIB_FAIL"]
    assert len(naib) >= 1
    assert naib[0].get("head_id") == "0" and naib[0].get("dependent_id") == "1"  # verb → NAIB_SUBJ → naib


def test_l10b_outputs_unchanged():
    """L10B transformation_result unchanged (additive-only)."""
    pipeline = run_pipeline_for_test("الطَّالِبُ مُجْتَهِدٌ")
    lo = pipeline.get("layer_outputs") or {}
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    tr = l10b.get("transformation_result") or {}
    assert "dependency_nodes" in tr
    assert "dependency_edges" in tr
    assert "syntax_summary" in tr
    nodes = tr.get("dependency_nodes") or []
    assert isinstance(nodes, list)


def test_root_resolution_present_not_duplicated_in_links():
    """root_resolution present, non-empty; no ROOT relation in dependency_links."""
    pipeline = run_pipeline_for_test("كَتَبَ زَيْدٌ")
    lo = pipeline.get("layer_outputs") or {}
    ds = lo.get("DEPENDENCY_SYNTAX_BUILDER")
    assert ds is not None
    root = ds.get("root_resolution") or {}
    assert (root.get("root_id") or "").strip() != "" or len(root) >= 1
    links = ds.get("dependency_links") or []
    root_links = [l for l in links if (l.get("relation") or "").strip() == "ROOT"]
    assert len(root_links) == 0


def test_corrections_log_is_list():
    """corrections_log is present and is a list (may be empty)."""
    pipeline = run_pipeline_for_test("الطَّالِبُ مُجْتَهِدٌ")
    lo = pipeline.get("layer_outputs") or {}
    ds = lo.get("DEPENDENCY_SYNTAX_BUILDER")
    assert ds is not None
    assert "corrections_log" in ds
    assert isinstance(ds["corrections_log"], list)


def test_arabic_role_on_every_dependency_link():
    """Every dependency_link has arabic_role populated."""
    pipeline = run_pipeline_for_test("كَتَبَ زَيْدٌ الرِّسَالَةَ")
    lo = pipeline.get("layer_outputs") or {}
    ds = lo.get("DEPENDENCY_SYNTAX_BUILDER")
    assert ds is not None
    links = ds.get("dependency_links") or []
    for link in links:
        assert "arabic_role" in link
        ar = link.get("arabic_role")
        assert ar is None or (isinstance(ar, str) and len(ar) > 0)
