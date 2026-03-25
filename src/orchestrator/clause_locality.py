# -*- coding: utf-8 -*-
"""
Batch 28.24 — unified clause-locality for Stage 15 vs L17.

Stage 15 (dependency_syntax/builder) historically used L10B ``clause_units`` for
``token_to_clause`` / ``_same_clause``. L17 used CLAUSE_ENGINE ``clause_analysis``,
where a single ``main_0`` span flattens all tokens into one clause id — diverging
from L10B's finer units on the same sentence.

This module provides one normalized ``token_id_str -> clause_id`` map:
- When L16 has **non-trivial** structure (conditional, hal/tamyiz/sila rows, etc.),
  use L16 clause spans (same ordering rules as ``_clause_id_for_token``).
- When L16 only emits a trivial **main** clause (typical case), use **L10B**
  ``clause_units`` so L17 locality matches Stage 15 attachment scans.

Read-only: no pipeline stage mutation.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional


def token_to_clause_from_units(clause_units: List[Dict[str, Any]]) -> Dict[str, str]:
    """Map token_id (str) to clause_id — mirrors dependency_syntax.builder._token_to_clause."""
    out: Dict[str, str] = {}
    for c in clause_units or []:
        cid = c.get("clause_id") or c.get("type") or "main"
        start = c.get("start_token_id")
        end = c.get("end_token_id")
        try:
            s, e = int(start or 0), int(end or 0)
            for t in range(s, e + 1):
                out[str(t)] = str(cid)
        except (TypeError, ValueError):
            continue
    return out


def l10b_token_to_clause_map(lo: Dict[str, Any]) -> Dict[str, str]:
    """Clause locality from L10B only (Stage 15 legacy source)."""
    tr = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
    units = tr.get("clause_units") or []
    return token_to_clause_from_units(units)


def _clause_analysis_to_token_map_first_wins(clause_analysis: List[Dict[str, Any]]) -> Dict[str, str]:
    """
    Build dense map from L16 clause rows. Overlapping spans: first clause in list wins
    (matches l17 _clause_id_for_token iteration order).
    """
    out: Dict[str, str] = {}
    for c in clause_analysis or []:
        cid = c.get("clause_id")
        if cid is None:
            continue
        cid_s = str(cid)
        try:
            start = int(c.get("start_token_id") or 0)
            end = int(c.get("end_token_id") or 0)
        except (TypeError, ValueError):
            continue
        for t in range(start, end + 1):
            k = str(t)
            if k not in out:
                out[k] = cid_s
    return out


def _l16_locality_authoritative(tr: Dict[str, Any], clause_analysis: List[Dict[str, Any]]) -> bool:
    """True when L16 clause spans should override L10B for locality (non-trivial L16)."""
    if tr.get("conditional_structure_detected"):
        return True
    ca = clause_analysis or []
    if len(ca) > 1:
        return True
    for c in ca:
        ct = (c.get("clause_type") or "").strip().lower()
        if ct and ct != "main":
            return True
    return False


def ensure_locality_map(lo: Dict[str, Any], locality_map: Any) -> Dict[str, str]:
    """
    Normalize caller input: Batch 28.24 uses ``Dict[str, str]`` token maps; unit tests may
    still pass legacy L16 ``clause_analysis`` row lists.
    """
    if isinstance(locality_map, dict):
        return locality_map
    if isinstance(locality_map, list):
        return _clause_analysis_to_token_map_first_wins(locality_map)
    return build_clause_locality_token_map(lo)


def build_clause_locality_token_map(lo: Dict[str, Any]) -> Dict[str, str]:
    """
    Single source of truth for in-ayah clause membership labels (string clause_id per token).

    - Non-trivial L16 → L16 span map (first-winning overlap policy).
    - Else → L10B clause_units map (matches Stage 15 dependency builder).
    """
    ce = lo.get("CLAUSE_ENGINE") or {}
    tr = ce.get("transformation_result") or ce
    clause_analysis = list(tr.get("clause_analysis") or tr.get("clauses") or [])
    if _l16_locality_authoritative(tr, clause_analysis):
        return _clause_analysis_to_token_map_first_wins(clause_analysis)
    return l10b_token_to_clause_map(lo)


def same_clause_locality_stage15_style(
    token_to_clause: Dict[str, str],
    left_idx: int,
    right_idx: int,
) -> bool:
    """
    Match dependency_syntax.builder._same_clause: empty / missing clause id is permissive
    (treated as compatible), so locality does not over-split when units are incomplete.
    """
    left = (token_to_clause.get(str(left_idx)) or "").strip()
    right = (token_to_clause.get(str(right_idx)) or "").strip()
    return not left or not right or left == right


def clause_id_for_token_from_map(token_index: int, token_to_clause: Dict[str, str]) -> Optional[str]:
    """Return clause id for token, or None if unassigned (same as missing key)."""
    v = token_to_clause.get(str(token_index))
    return v if v is not None else None
