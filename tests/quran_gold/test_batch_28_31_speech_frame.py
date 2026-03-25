# -*- coding: utf-8 -*-
"""Batch 28.31 — Stage 15: matrix reporting verb must not attach SUBJ/OBJ/PRED into quoted speech."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


def _links(r):
    return (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}


def _heads_to(r, head_surface: str):
    dsb = _links(r)
    tokens = []
    tr2 = (r.get("layer_outputs") or {}).get("L2_TOKENIZATION") or {}
    tr2 = (tr2.get("transformation_result") or {})
    toks = tr2.get("tokens") or []
    if toks:
        tokens = [t.get("word") or "" for t in toks if t.get("word")]
    if not tokens:
        tr5 = (r.get("layer_outputs") or {}).get("L5_WORD_TYPING") or {}
        tr5 = (tr5.get("transformation_result") or {})
        tokens = [w.get("word") or "" for w in (tr5.get("words") or []) if w.get("word")]
    out = []
    for link in dsb.get("dependency_links") or []:
        hi = int(link.get("head_id") or -1)
        if hi < 0 or hi >= len(tokens):
            continue
        if (tokens[hi] or "").strip() != head_surface:
            continue
        rel = (link.get("relation") or "").strip()
        if rel in ("SUBJ", "OBJ", "PRED"):
            out.append(link)
    return out


def test_b28_31_qul_no_matrix_subj_obj_pred_to_quote():
    r = run_pipeline("قُلْ هُوَ اللَّهُ أَحَدٌ")
    bad = _heads_to(r, "قُلْ")
    assert not bad, bad


def test_b28_31_qalu_no_subj_to_quoted_verb():
    r = run_pipeline("قَالُوا آمَنَّا")
    for link in _links(r).get("dependency_links") or []:
        assert not (
            link.get("head_id") == "0"
            and link.get("dependent_id") == "1"
            and link.get("relation") == "SUBJ"
        )


def test_b28_31_qala_yaa_adam_no_matrix_subj():
    r = run_pipeline("قَالَ يَا آدَمُ أَنْبِئْهُمْ بِأَسْمَائِهِمْ")
    bad = _heads_to(r, "قَالَ")
    assert not bad, bad


def test_b28_31_qala_al_rasul_keeps_matrix_subj():
    """Definite subject after قَالَ is not treated as quoted speech."""
    r = run_pipeline("قَالَ الرَّسُولُ حَقًّا")
    assert any(
        l.get("head_id") == "0"
        and l.get("dependent_id") == "1"
        and l.get("relation") == "SUBJ"
        for l in (_links(r).get("dependency_links") or [])
    )
