# -*- coding: utf-8 -*-
"""
Normalized internal schema for connectives knowledge.
Stable fields only; raw JSON kept under "raw" for traceability.
"""

from __future__ import annotations

from typing import Any, Dict

# Canonical group names (stable API)
GROUP_CONDITIONAL = "conditional"
GROUP_NEGATION = "negation"
GROUP_EXPLANATION_CAUSATION = "explanation_causation"
GROUP_ADVERSATIVE = "adversative"

# Category ID (from API JSON) → canonical group
CATEGORY_ID_TO_GROUP: Dict[int, str] = {
    3: GROUP_CONDITIONAL,           # أدوات الشرط
    18: GROUP_NEGATION,             # أدوات النفي
    23: GROUP_EXPLANATION_CAUSATION,  # التفسير والتعليل
    29: GROUP_ADVERSATIVE,          # أدوات الاستدراك
}


def normalized_connective(
    token: str,
    normalized_token: str,
    category_id: int,
    category_name: str,
    group: str,
    source_file: str,
    raw: Dict[str, Any],
) -> Dict[str, Any]:
    """Build normalized connective entry. Stable schema; raw kept for traceability."""
    return {
        "token": token,
        "normalized_token": normalized_token,
        "category_id": category_id,
        "category_name": category_name,
        "group": group,
        "source_file": source_file,
        "raw": raw,
    }
