# -*- coding: utf-8 -*-
"""
Reusable lookup API for connectives knowledge.
Diacritic-insensitive where reasonable; preserves original and normalized token.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from .loader import load_connectives_from_dir
from .models import (
    GROUP_ADVERSATIVE,
    GROUP_CONDITIONAL,
    GROUP_EXPLANATION_CAUSATION,
    GROUP_NEGATION,
)

# Module-level cache (shared resource)
_connectives_cache: Optional[List[Dict[str, Any]]] = None
_normalized_index: Optional[Dict[str, Dict[str, Any]]] = None


def _normalize(s: str) -> str:
    if not s or not isinstance(s, str):
        return ""
    result = []
    for c in s:
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _ensure_loaded() -> None:
    global _connectives_cache, _normalized_index
    if _connectives_cache is not None:
        return
    _connectives_cache = load_connectives_from_dir()
    _normalized_index = {}
    for conn in _connectives_cache:
        norm = (conn.get("normalized_token") or "").strip()
        if norm and norm not in _normalized_index:
            _normalized_index[norm] = conn
        token = (conn.get("token") or "").strip()
        if token and token not in _normalized_index:
            _normalized_index[token] = conn


def load_connectives_knowledge(force_reload: bool = False) -> List[Dict[str, Any]]:
    """Load (cached) normalized connectives. Returns list of normalized entries."""
    global _connectives_cache, _normalized_index
    if force_reload:
        _connectives_cache = None
        _normalized_index = None
    _ensure_loaded()
    return list(_connectives_cache or [])


def get_connective_by_token(token: str) -> Optional[Dict[str, Any]]:
    """Return normalized connective entry for token, or None. Diacritic-insensitive."""
    if not token:
        return None
    _ensure_loaded()
    t = (token or "").strip()
    if t in (_normalized_index or {}):
        return (_normalized_index or {}).get(t)
    norm = _normalize(t)
    return (_normalized_index or {}).get(norm) if norm else None


def get_connectives_by_group(group: str) -> List[Dict[str, Any]]:
    """Return all normalized connectives in the given group."""
    _ensure_loaded()
    if not group:
        return []
    return [c for c in (_connectives_cache or []) if (c.get("group") or "") == group]


def classify_connective(token: str) -> Optional[Dict[str, Any]]:
    """
    Classify token as connective. Returns normalized entry (with group) or None.
    Safe for use from any stage; returns stable schema only (group, category_name, etc.).
    """
    return get_connective_by_token(token)


def is_conditional_connective(token: str) -> bool:
    """True iff token is recognized as conditional connective from shared knowledge."""
    c = get_connective_by_token(token)
    return c is not None and (c.get("group") or "") == GROUP_CONDITIONAL


def is_negation_connective(token: str) -> bool:
    """True iff token is recognized as negation connective from shared knowledge."""
    c = get_connective_by_token(token)
    return c is not None and (c.get("group") or "") == GROUP_NEGATION


def is_explanatory_or_causal_connective(token: str) -> bool:
    """True iff token is recognized as explanation/causation connective from shared knowledge."""
    c = get_connective_by_token(token)
    return c is not None and (c.get("group") or "") == GROUP_EXPLANATION_CAUSATION


def is_adversative_connective(token: str) -> bool:
    """True iff token is recognized as adversative connective from shared knowledge."""
    c = get_connective_by_token(token)
    return c is not None and (c.get("group") or "") == GROUP_ADVERSATIVE
