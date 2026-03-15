# -*- coding: utf-8 -*-
"""
Lookup API for operator semantic hints. Used by semantic role projector for PP role tightening.
"""

from __future__ import annotations

from typing import Any, Dict, Optional

from .loader import load_operator_semantics


def _normalize(s: str) -> str:
    if not s:
        return ""
    return "".join(
        c for c in s
        if not ("\u064b" <= c <= "\u0652") and c != "\u0670"
    ).strip()


def get_operator_semantic_hints(token_surface: str) -> Optional[Dict[str, Any]]:
    """
    Return normalized semantic/syntactic hints for an operator (e.g. preposition) token.
    Diacritic-tolerant. Returns None if operator not in catalog.

    Returns dict with at least:
      - operator_type
      - semantic_functions (list of role names, e.g. GOAL, SOURCE)
      - syntactic_functions
      - confidence_hint
      - source_file
      - preferred_semantic_role (single role or None)
      - withhold_location_for (list of normalized object surfaces for which not to assign LOCATION)
    """
    if not (token_surface or "").strip():
        return None
    catalog = load_operator_semantics()
    norm = _normalize(token_surface)
    if not norm:
        return None
    out = catalog.get(norm)
    if out is None:
        return None
    return {
        "operator_type": out.get("operator_type"),
        "semantic_functions": list(out.get("semantic_functions") or []),
        "syntactic_functions": list(out.get("syntactic_functions") or []),
        "confidence_hint": out.get("confidence_hint"),
        "source_file": out.get("source_file"),
        "preferred_semantic_role": out.get("preferred_semantic_role"),
        "withhold_location_for": list(out.get("withhold_location_for") or []),
    }
