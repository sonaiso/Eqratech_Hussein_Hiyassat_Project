# -*- coding: utf-8 -*-
"""
Stage 15 CRITICAL FIX — simple active transitives must attach direct objects.
"""

from __future__ import annotations

from orchestrator.dependency_syntax import build_dependency_syntax


def _build_lo(tokens: list[str], *, voice: str = "active", objects: int = 1, roots: list[str] | None = None):
    nodes = [
        {"token_id": str(i), "surface": t, "pos_hint": "verb" if i == 0 else "noun"}
        for i, t in enumerate(tokens)
    ]
    words5 = [{"word": t, "kind": "verb" if i == 0 else "noun"} for i, t in enumerate(tokens)]
    roots = roots or [""] * len(tokens)
    words8 = [{"word": t, "root": roots[i]} for i, t in enumerate(tokens)]
    profile = {
        "token_id": "0",
        "surface": tokens[0],
        "status": "resolved",
        "voice": voice,
        "transitivity": "متعدي" if objects else "unknown",
        "objects": objects,
        "confidence": 0.92 if voice == "active" else 0.9,
    }
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": w} for w in tokens]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": words5}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": words8}},
        "L10B_DEEP_SYNTAX": {
            "transformation_result": {
                "dependency_nodes": nodes,
                "dependency_edges": [],
                "clause_units": [
                    {"clause_id": "main", "type": "verbal", "start_token_id": "0", "end_token_id": str(len(tokens) - 1), "head_token_id": "0"}
                ],
                "syntax_summary": {"main_clause_type": "verbal"},
            }
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": [profile]}},
    }


def _links(ds: dict, relation: str) -> list[dict]:
    return [l for l in (ds.get("dependency_links") or []) if l.get("relation") == relation]


def test_simple_active_transitive_clause_attaches_subject_and_object():
    lo = _build_lo(
        ["ضَرَبَ", "زَيْدٌ", "عَمْراً"],
        voice="active",
        objects=1,
        roots=["ضرب", "زيد", "عمر"],
    )
    ds = build_dependency_syntax(lo)
    assert ds is not None
    subj = _links(ds, "SUBJ")
    obj = _links(ds, "OBJ")
    assert len([l for l in subj if l.get("head_id") == "0" and l.get("dependent_id") == "1"]) == 1
    assert any(l.get("head_id") == "0" and l.get("dependent_id") == "2" for l in obj)
    assert all(l.get("arabic_role") == "MAF3UL_BIH" for l in obj)
    assert not any(l.get("dependent_id") == "2" for l in subj)


def test_second_active_transitive_example_attaches_object():
    lo = _build_lo(
        ["أَكَلَ", "الطِّفْلُ", "التُّفَّاحَةَ"],
        voice="active",
        objects=1,
        roots=["أكل", "طفل", "فكه"],
    )
    ds = build_dependency_syntax(lo)
    assert ds is not None
    assert any(l.get("head_id") == "0" and l.get("dependent_id") == "1" for l in _links(ds, "SUBJ"))
    assert any(l.get("head_id") == "0" and l.get("dependent_id") == "2" for l in _links(ds, "OBJ"))


def test_passive_protection_no_normal_obj():
    lo = _build_lo(
        ["ضُرِبَ", "الظَّالِمُ"],
        voice="passive",
        objects=1,
        roots=["ضرب", "ظلم"],
    )
    ds = build_dependency_syntax(lo)
    assert ds is not None
    assert not _links(ds, "OBJ")
    naib = _links(ds, "NAIB_SUBJ")
    assert any(l.get("head_id") == "0" and l.get("dependent_id") == "1" for l in naib)


def test_maf3ul_mutlaq_protection_same_root_masdar_like_not_forced_obj():
    lo = _build_lo(
        ["ضَرَبَ", "زَيْدٌ", "ضَرْبًا"],
        voice="active",
        objects=1,
        roots=["ضرب", "زيد", "ضرب"],
    )
    ds = build_dependency_syntax(lo)
    assert ds is not None
    assert any(l.get("head_id") == "0" and l.get("dependent_id") == "1" for l in _links(ds, "SUBJ"))
    assert not any(l.get("head_id") == "0" and l.get("dependent_id") == "2" for l in _links(ds, "OBJ"))
    assert not any(l.get("dependent_id") == "2" and l.get("relation") == "APPOS" for l in (ds.get("dependency_links") or []))
    ambiguity = ds.get("ambiguity_log") or []
    assert any(a.get("token_id") == "2" for a in ambiguity)


def test_no_duplicate_conflict_same_token_not_subj_and_obj():
    lo = _build_lo(
        ["كَتَبَ", "الطَّالِبُ", "الدَّرْسَ"],
        voice="active",
        objects=1,
        roots=["كتب", "طلب", "درس"],
    )
    ds = build_dependency_syntax(lo)
    assert ds is not None
    links = ds.get("dependency_links") or []
    pairs = [(l.get("head_id"), l.get("dependent_id"), l.get("relation")) for l in links]
    assert len(pairs) == len(set(pairs))
    rels_for_1 = {l.get("relation") for l in links if l.get("head_id") == "0" and l.get("dependent_id") == "1"}
    rels_for_2 = {l.get("relation") for l in links if l.get("head_id") == "0" and l.get("dependent_id") == "2"}
    assert rels_for_1 == {"SUBJ"}
    assert rels_for_2 == {"OBJ"}
