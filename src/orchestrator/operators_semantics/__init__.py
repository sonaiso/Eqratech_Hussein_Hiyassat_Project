# -*- coding: utf-8 -*-
"""
Operator semantics for PP semantic role projection.
Loads from operator catalog CSV (enriched preferred) and exposes get_operator_semantic_hints.
Used by semantic_roles/projector for prepositional phrase role tightening.
"""

from .loader import load_operator_semantics
from .lookup import get_operator_semantic_hints

__all__ = [
    "load_operator_semantics",
    "get_operator_semantic_hints",
]
