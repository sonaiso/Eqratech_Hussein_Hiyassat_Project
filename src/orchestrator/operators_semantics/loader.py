# -*- coding: utf-8 -*-
"""
Load operator semantic/syntactic metadata from operator catalog CSV.
Prefers operators_catalog_split_project_enriched.csv; falls back to
operators_catalog_split_project_with_evidence.csv.
"""

from __future__ import annotations

import csv
from pathlib import Path
from typing import Any, Dict, List, Optional

# Project data dir: src/orchestrator/operators_semantics/loader.py -> repo root is parents[3]
_REPO_ROOT = Path(__file__).resolve().parents[3]
_DATA_DIR = _REPO_ROOT / "data"
_ENRICHED = _DATA_DIR / "operators_catalog_split_project_enriched.csv"
_WITH_EVIDENCE = _DATA_DIR / "operators_catalog_split_project_with_evidence.csv"

_OPERATOR_CACHE: Optional[Dict[str, Dict[str, Any]]] = None
_SOURCE_FILE_USED: Optional[str] = None


def _normalize(s: str) -> str:
    """Strip Arabic diacritics for matching."""
    if not s:
        return ""
    return "".join(
        c for c in s
        if not ("\u064b" <= c <= "\u0652") and c != "\u0670"
    ).strip()


# Semantic role hints derived from Purpose/Usage and project_effect_signature
# Maps normalized operator stem -> preferred semantic role and constraints
# (diacritics stripped; alef variants إى/الى both mapped)
_PREP_SEMANTIC_MAP = {
    "الى": {"preferred": "GOAL", "alternatives": [], "withhold_location_for": []},
    "إلى": {"preferred": "GOAL", "alternatives": [], "withhold_location_for": []},
    "من": {"preferred": "SOURCE", "alternatives": [], "withhold_location_for": []},
    "مِن": {"preferred": "SOURCE", "alternatives": [], "withhold_location_for": []},
    "في": {"preferred": "LOCATION", "alternatives": [], "withhold_location_for": []},
    "فِي": {"preferred": "LOCATION", "alternatives": [], "withhold_location_for": []},
    # على: do not default to LOCATION; abstract object (e.g. الله) -> GOAL or withhold
    "على": {"preferred": "GOAL", "alternatives": ["LOCATION"], "withhold_location_for": ["الله"]},
    "عَلَى": {"preferred": "GOAL", "alternatives": ["LOCATION"], "withhold_location_for": ["الله"]},
    # ب: INSTRUMENT when means/مرور; withhold for oath (قسم)
    "ب": {"preferred": "INSTRUMENT", "alternatives": [], "withhold_location_for": []},
    "بِ": {"preferred": "INSTRUMENT", "alternatives": [], "withhold_location_for": []},
    # ك: simile
    "ك": {"preferred": "STATE", "alternatives": [], "withhold_location_for": []},
    "كَ": {"preferred": "STATE", "alternatives": [], "withhold_location_for": []},
    # لِ: benefactive/possession - no single semantic role in our set
    "ل": {"preferred": None, "alternatives": [], "withhold_location_for": []},
    "لِ": {"preferred": None, "alternatives": [], "withhold_location_for": []},
}


def _read_csv(path: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                rows.append(dict(row))
    except OSError:
        pass
    return rows


def load_operator_semantics(force_reload: bool = False) -> Dict[str, Dict[str, Any]]:
    """
    Load operator catalog and build normalized operator -> semantic hints.
    Prefer enriched CSV; fall back to with_evidence. Returns dict keyed by normalized operator stem.
    """
    global _OPERATOR_CACHE, _SOURCE_FILE_USED
    if _OPERATOR_CACHE is not None and not force_reload:
        return _OPERATOR_CACHE

    result: Dict[str, Dict[str, Any]] = {}
    source_file = ""

    for path in (_ENRICHED, _WITH_EVIDENCE):
        if not path.exists():
            continue
        rows = _read_csv(path)
        if not rows:
            continue
        source_file = str(path.name)
        # CSV columns: Operator, Purpose/Usage, project_effect_signature, English Group Name, etc.
        for row in rows:
            op = (row.get("Operator") or "").strip()
            if not op:
                continue
            norm = _normalize(op)
            if not norm or norm in result:
                continue
            purpose = (row.get("Purpose/Usage") or "").strip()
            effect = (row.get("project_effect_signature") or "").strip()
            # Use our prep semantic map for known prepositions; else generic
            hint = _PREP_SEMANTIC_MAP.get(norm)
            if hint:
                result[norm] = {
                    "operator_type": effect or "GEN",
                    "semantic_functions": [hint["preferred"]] + hint["alternatives"] if hint["preferred"] else [],
                    "syntactic_functions": [effect] if effect else [],
                    "confidence_hint": "operator_catalog",
                    "source_file": source_file,
                    "preferred_semantic_role": hint["preferred"],
                    "withhold_location_for": hint.get("withhold_location_for", []),
                    "purpose_usage": purpose,
                }
            else:
                result[norm] = {
                    "operator_type": effect or "GEN",
                    "semantic_functions": [],
                    "syntactic_functions": [effect] if effect else [],
                    "confidence_hint": "operator_catalog",
                    "source_file": source_file,
                    "preferred_semantic_role": None,
                    "withhold_location_for": [],
                    "purpose_usage": purpose,
                }
        # Also ensure diacritic variants from _PREP_SEMANTIC_MAP are in result
        for prep_norm, hint in _PREP_SEMANTIC_MAP.items():
            if prep_norm not in result:
                result[prep_norm] = {
                    "operator_type": "GEN",
                    "semantic_functions": ([hint["preferred"]] + hint["alternatives"]) if hint["preferred"] else [],
                    "syntactic_functions": ["GEN"],
                    "confidence_hint": "operator_catalog",
                    "source_file": source_file or "builtin",
                    "preferred_semantic_role": hint["preferred"],
                    "withhold_location_for": hint.get("withhold_location_for", []),
                    "purpose_usage": "",
                }
        break

    if not result:
        # No CSV loaded: use builtin prep map only
        for prep_norm, hint in _PREP_SEMANTIC_MAP.items():
            result[prep_norm] = {
                "operator_type": "GEN",
                "semantic_functions": ([hint["preferred"]] + hint["alternatives"]) if hint["preferred"] else [],
                "syntactic_functions": ["GEN"],
                "confidence_hint": "builtin",
                "source_file": "builtin",
                "preferred_semantic_role": hint["preferred"],
                "withhold_location_for": hint.get("withhold_location_for", []),
                "purpose_usage": "",
            }
        source_file = "builtin"

    _OPERATOR_CACHE = result
    _SOURCE_FILE_USED = source_file
    return result


def get_source_file_used() -> Optional[str]:
    """Return which CSV file was used for the current cache, or None if not loaded yet."""
    if _OPERATOR_CACHE is None:
        load_operator_semantics()
    return _SOURCE_FILE_USED
