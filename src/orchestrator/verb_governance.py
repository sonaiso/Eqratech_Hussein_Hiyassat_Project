# -*- coding: utf-8 -*-
"""
L10B-V — Verb Governance Engine.

Structured knowledge and inference for Arabic verb transitivity and argument structure.
Used inside L10B to boost dependency resolution and flag anomalies.
"""

from __future__ import annotations

import json
import os
from typing import Any, Dict, List, Optional

# Default path: project data/ relative to this package (src/orchestrator/)
_VERB_GOVERNANCE_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
    "data",
    "verb_governance.json",
)

_VERB_GOVERNANCE_CACHE: Optional[Dict[str, Dict[str, Any]]] = None


def load_verb_governance(path: Optional[str] = None) -> Dict[str, Dict[str, Any]]:
    """Load verb governance JSON. Returns dict lemma -> entry. Cached."""
    global _VERB_GOVERNANCE_CACHE
    if _VERB_GOVERNANCE_CACHE is not None:
        return _VERB_GOVERNANCE_CACHE
    p = path or _VERB_GOVERNANCE_PATH
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _VERB_GOVERNANCE_CACHE = {k: v for k, v in data.items() if isinstance(v, dict)}
        else:
            _VERB_GOVERNANCE_CACHE = {}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        _VERB_GOVERNANCE_CACHE = {}
    return _VERB_GOVERNANCE_CACHE


def infer_expected_arguments(verb_node: Dict[str, Any]) -> Dict[str, Any]:
    """
    Infer expected arguments for a verb from governance data.

    verb_node: dict with at least "lemma" or "root" (string). May include token_id, surface.

    Returns:
        {
            "expected_subject": bool,
            "expected_objects": int,
            "expected_pp_relations": ["على", "إلى", ...],
            "optional_roles": [...],
        }
    """
    lemma = (verb_node.get("lemma") or verb_node.get("root") or "").strip()
    if not lemma:
        return {
            "expected_subject": True,
            "expected_objects": 0,
            "expected_pp_relations": [],
            "optional_roles": [],
        }
    gov = load_verb_governance()
    entry = gov.get(lemma)
    if not entry:
        return {
            "expected_subject": True,
            "expected_objects": 0,
            "expected_pp_relations": [],
            "optional_roles": [],
        }
    trans = (entry.get("transitivity") or "").strip().lower()
    objects = int(entry.get("objects") or 0)
    prep_required = bool(entry.get("prepositional_required"))
    required_prep = (entry.get("required_preposition") or "").strip()
    expected_pp: List[str] = []
    if prep_required and required_prep:
        expected_pp.append(required_prep)
    optional_roles: List[str] = []
    if trans in ("mental_verb", "transformational") and objects >= 2:
        optional_roles.extend(["مفعول به أول", "مفعول به ثاني"])
    return {
        "expected_subject": True,
        "expected_objects": objects,
        "expected_pp_relations": expected_pp,
        "optional_roles": optional_roles,
    }
