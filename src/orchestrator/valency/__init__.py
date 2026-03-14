# -*- coding: utf-8 -*-
"""
L8C — Valency Matrix Seed Layer (knowledge only).
Semantic verb governance metadata; no syntax, iʿrāb, or dependency logic.
"""

from .models import ValencyFrame, CONF_EXACT_KB, CONF_WEAK_PATTERN, CONF_UNKNOWN
from .loader import load_valency_kb
from .lookup import resolve_valency

__all__ = [
    "ValencyFrame",
    "load_valency_kb",
    "resolve_valency",
    "CONF_EXACT_KB",
    "CONF_WEAK_PATTERN",
    "CONF_UNKNOWN",
]
