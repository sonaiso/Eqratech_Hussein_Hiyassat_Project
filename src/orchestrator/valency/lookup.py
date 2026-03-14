# -*- coding: utf-8 -*-
"""
Resolve valency frame for a root. Triliteral only; quadrilateral returns unknown.
"""

from __future__ import annotations

from typing import Optional

from .loader import load_valency_kb
from .models import ValencyFrame, CONF_UNKNOWN


def _normalize_root(r: str) -> str:
    if not r or not isinstance(r, str):
        return ""
    return r.strip().replace("-", "").replace(" ", "")


def _root_letter_count(root: str) -> int:
    """Number of base letters (strip dashes/spaces only)."""
    s = _normalize_root(root)
    if not s:
        return 0
    return len(s)


def resolve_valency(root: str | None) -> ValencyFrame | None:
    """
    Resolve valency frame for root. Triliteral only; exact KB match → frame with confidence 0.90.
    Quadrilateral or non-3-letter → return None (caller may use unknown placeholder).
    No match → return ValencyFrame with valency_class=unknown, required_roles=[], confidence=0.20.
    """
    if not root:
        return ValencyFrame(
            root="",
            valency_class="unknown",
            required_roles=[],
            optional_roles=[],
            source="",
            confidence=CONF_UNKNOWN,
        )
    root_norm = _normalize_root(root)
    if _root_letter_count(root_norm) != 3:
        # Quadrilateral or other → return None so L8B can attach unknown placeholder
        return None
    kb = load_valency_kb()
    frame = kb.get(root_norm)
    if frame is not None:
        return frame
    return ValencyFrame(
        root=root_norm,
        valency_class="unknown",
        required_roles=[],
        optional_roles=[],
        source="",
        confidence=CONF_UNKNOWN,
    )
