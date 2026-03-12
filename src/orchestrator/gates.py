# -*- coding: utf-8 -*-
"""
Stage 5 — Entry gates and eligibility for status assignment.

Lightweight checks on upstream outputs. Used by adapters to set
status (success / partial / skipped / failed / pass_through / missing)
and gates_applied. No analyzer logic; orchestration only.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from .adapters.fvafk_runner import FVAFK_RESULT_KEY

# Kinds that typically have no root (closed-class / non-content)
NO_ROOT_KINDS = frozenset({"operator", "particle", "pronoun", "أداة", "حرف", "ضمير"})


def compute_gates(pipeline: Dict[str, Any]) -> Dict[str, bool]:
    """
    Compute eligibility gates from pipeline (requires _fvafk_result).
    Returns dict of gate_name -> passed (bool).
    """
    data = pipeline.get(FVAFK_RESULT_KEY)
    if not isinstance(data, dict):
        return {
            "has_text": bool((pipeline.get("original_text") or "").strip()),
            "has_tokens": False,
            "has_segmentable_word": False,
            "has_morphology_candidate": False,
            "has_root_candidate": False,
            "has_syntax_candidate": False,
            "has_i3rab_evidence": False,
            "has_sentence_level_evidence": False,
        }
    text = (pipeline.get("original_text") or data.get("input") or "").strip()
    c2b = data.get("c2b") or {}
    words: List[Dict[str, Any]] = c2b.get("words") if isinstance(c2b.get("words"), list) else []
    token_count = len(words)

    has_text = bool(text)
    has_tokens = token_count > 0

    # At least one token that looks like a segmentable word (not only single char/punct)
    segmentable = False
    for w in words:
        word = (w.get("word") or "").strip()
        if len(word) >= 2 and any("\u0600" <= c <= "\u06FF" for c in word):
            segmentable = True
            break
    has_segmentable_word = segmentable

    # At least one content word (noun/verb) or word with a root
    morphology_candidate = False
    root_candidate = False
    for w in words:
        kind = (w.get("kind") or "").strip().lower()
        root = w.get("root")
        if root and (isinstance(root, dict) and (root.get("formatted") or root.get("letters"))):
            root_candidate = True
        if kind not in NO_ROOT_KINDS:
            morphology_candidate = True
        if root_candidate:
            morphology_candidate = True
    has_morphology_candidate = morphology_candidate
    has_root_candidate = root_candidate

    # Syntax: multiple tokens or c2d/syntax data
    c2d = data.get("c2d") or {}
    syntax_links = (data.get("syntax") or {}).get("links") or {}
    has_syntax_candidate = token_count > 1 or bool(c2d.get("sentence_type")) or bool(syntax_links.get("isnadi"))

    # At least one word has i3rab text
    i3rab_evidence = False
    for w in words:
        c2e = w.get("c2e") or {}
        if isinstance(c2e, dict) and (c2e.get("i3rab_text") or "").strip():
            i3rab_evidence = True
            break
    has_i3rab_evidence = i3rab_evidence

    # Sentence-level: multiple tokens with c2d and/or rhetoric; or any rhetoric
    rhetoric = data.get("rhetoric_signals") or []
    sentence_evidence = (token_count > 1 and bool(c2d.get("sentence_type"))) or len(rhetoric) > 0
    has_sentence_level_evidence = sentence_evidence

    return {
        "has_text": has_text,
        "has_tokens": has_tokens,
        "has_segmentable_word": has_segmentable_word,
        "has_morphology_candidate": has_morphology_candidate,
        "has_root_candidate": has_root_candidate,
        "has_syntax_candidate": has_syntax_candidate,
        "has_i3rab_evidence": has_i3rab_evidence,
        "has_sentence_level_evidence": has_sentence_level_evidence,
    }


def gate_entry(gate: str, passed: bool, reason: str = "") -> Dict[str, Any]:
    """Build a single gates_applied entry."""
    return {
        "gate": gate,
        "status": "passed" if passed else "failed",
        "reason": reason or ("eligible" if passed else "not eligible"),
    }
