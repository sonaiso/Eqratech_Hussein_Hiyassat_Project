# -*- coding: utf-8 -*-
"""
Shared Connectives Knowledge Layer.

Loads and normalizes connectives from data/connectives_api/ (categories 3, 18, 23, 29).
Exposes lookup API for use by L4, L10B, L11B, L12, L12B, etc.
Does not perform dependency parsing, i'rab, or sentence classification.
"""

from .lookup import (
    classify_connective,
    get_connective_by_token,
    get_connectives_by_group,
    is_adversative_connective,
    is_conditional_connective,
    is_explanatory_or_causal_connective,
    is_negation_connective,
    load_connectives_knowledge,
)
from .models import (
    GROUP_ADVERSATIVE,
    GROUP_CONDITIONAL,
    GROUP_EXPLANATION_CAUSATION,
    GROUP_NEGATION,
)

__all__ = [
    "load_connectives_knowledge",
    "get_connective_by_token",
    "get_connectives_by_group",
    "classify_connective",
    "is_conditional_connective",
    "is_negation_connective",
    "is_explanatory_or_causal_connective",
    "is_adversative_connective",
    "GROUP_CONDITIONAL",
    "GROUP_NEGATION",
    "GROUP_EXPLANATION_CAUSATION",
    "GROUP_ADVERSATIVE",
]
