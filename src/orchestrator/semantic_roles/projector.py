# -*- coding: utf-8 -*-
"""
SEMANTIC_ROLE_PROJECTION — maps syntactic roles and valency into abstract semantic roles.
Read-only from L8B, L10B, L11B. Does not modify syntax, i'rab, or validation.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from .models import (
    CONF_MEDIUM,
    CONF_STRONG,
    CONF_WEAK,
    ROLE_AGENT,
    ROLE_GOAL,
    ROLE_INSTRUMENT,
    ROLE_LOCATION,
    ROLE_PATIENT,
    ROLE_SOURCE,
    ROLE_STATE,
)


def _normalize(s: str) -> str:
    """Strip Arabic diacritics for matching."""
    if not s:
        return ""
    return "".join(c for c in s if not ("\u064b" <= c <= "\u0652") and c != "\u0670").strip()


# Normalized (no diacritics) preposition -> semantic role for Rule 4
_NORM_PREP_TO_ROLE: Dict[str, str] = {}
for _prep, _role in [
    ("الى", ROLE_GOAL), ("إلى", ROLE_GOAL),
    ("من", ROLE_SOURCE), ("مِن", ROLE_SOURCE),
    ("في", ROLE_LOCATION), ("فِي", ROLE_LOCATION),
    ("على", ROLE_LOCATION), ("عَلَى", ROLE_LOCATION),
    ("ب", ROLE_INSTRUMENT), ("بِ", ROLE_INSTRUMENT),
]:
    _NORM_PREP_TO_ROLE[_normalize(_prep) or _prep] = _role


def _tokens_from_lo(lo: Dict[str, Any]) -> List[str]:
    """Token list from L2 or L5."""
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    if tokens:
        return [t.get("word") or "" for t in tokens if t.get("word")]
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words = tr5.get("words") or []
    return [w.get("word") or "" for w in words if w.get("word")]


def project_semantic_roles(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """
    Project semantic roles from L8B, L10B, L11B. Returns dict to store under
    lo["SEMANTIC_ROLE_PROJECTION"] or None if upstream data missing.
    """
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    l11b = lo.get("L11B_CAUSAL_I3RAB") or {}
    l8b = lo.get("L8B_VERB_BAB_GOVERNANCE") or {}

    tr10b = l10b.get("transformation_result") or {}
    tr11b = l11b.get("transformation_result") or {}
    tr8b = l8b.get("transformation_result") or {}

    nodes = tr10b.get("dependency_nodes") or []
    edges = tr10b.get("dependency_edges") or []
    reasoning = tr11b.get("token_i3rab_reasoning") or []
    profiles_l8b = tr8b.get("verb_governance_profiles") or []

    tokens = _tokens_from_lo(lo)
    if not tokens:
        tokens = [r.get("surface") or "" for r in reasoning]
    if not tokens:
        return None

    # L8B: surface -> profile (voice, valency_class, valency_required_roles)
    profile_by_surface: Dict[str, Dict] = {}
    for p in profiles_l8b:
        surf = (p.get("surface") or "").strip()
        if surf:
            profile_by_surface[surf] = p

    # Token index -> L11B role, governing_factor
    role_by_idx: Dict[int, str] = {}
    for i, r in enumerate(reasoning):
        if i >= len(tokens):
            break
        role = (r.get("role") or "").strip()
        if role and role != "—":
            role_by_idx[i] = role

    # Token index -> L10B relation, head_id
    node_by_idx: Dict[int, Dict] = {i: n for i, n in enumerate(nodes) if n.get("token_id") == str(i)}
    # Edge to_id -> (from_id, relation) for majrur (preposition head)
    majrur_from: Dict[int, int] = {}  # token_index -> head_token_index
    for e in edges:
        if (e.get("relation") or "").strip() == "majrur":
            try:
                to_id = int(e.get("to_id", -1))
                from_id = int(e.get("from_id", -1))
                majrur_from[to_id] = from_id
            except (TypeError, ValueError):
                pass

    semantic_roles: List[Dict[str, Any]] = []
    assigned = 0

    for i in range(len(tokens)):
        surface = (tokens[i] or "").strip()
        role = role_by_idx.get(i) or ""
        node = node_by_idx.get(i) or {}
        rel = (node.get("relation") or "").strip()

        semantic_role: Optional[str] = None
        confidence = 0.0
        source = ""

        # Rule 1 — نائب فاعل + passive frame → PATIENT
        if role == "نائب فاعل":
            # Check if previous token is passive verb (L8B)
            if i >= 1:
                prev_surface = (tokens[i - 1] or "").strip()
                prof = profile_by_surface.get(prev_surface)
                if prof and (prof.get("voice") or "").strip() == "passive":
                    semantic_role = ROLE_PATIENT
                    confidence = CONF_STRONG
                    source = "passive_naib_fael_projection"

        # Rule 2 — فاعل + transitive valency + active → AGENT
        if not semantic_role and role == "فاعل":
            if i >= 1:
                prev_surface = (tokens[i - 1] or "").strip()
                prof = profile_by_surface.get(prev_surface)
                if prof:
                    vc = (prof.get("valency_class") or "").strip()
                    voice = (prof.get("voice") or "").strip()
                    if vc.startswith("transitive") and voice != "passive":
                        semantic_role = ROLE_AGENT
                        confidence = CONF_STRONG
                        source = "active_fael_transitive_projection"

        # Rule 3 — مفعول به + valency required contains مفعول به → PATIENT
        if not semantic_role and role == "مفعول به":
            # Check any verb profile has valency_required_roles containing مفعول به
            for p in profiles_l8b:
                req = p.get("valency_required_roles") or []
                if "مفعول به" in req or "مفعول به" in [str(x) for x in req]:
                    semantic_role = ROLE_PATIENT
                    confidence = CONF_MEDIUM
                    source = "mafoul_bih_valency_projection"
                    break

        # Rule 4 — majrur + preposition دلالي → GOAL/SOURCE/LOCATION/INSTRUMENT
        if not semantic_role and rel == "majrur":
            head_idx = majrur_from.get(i)
            if head_idx is not None and head_idx < len(tokens):
                prep_surface = (tokens[head_idx] or "").strip()
                prep_norm = _normalize(prep_surface)
                semantic_role = _NORM_PREP_TO_ROLE.get(prep_norm) or _NORM_PREP_TO_ROLE.get(prep_surface)
                if semantic_role:
                    confidence = CONF_WEAK
                    source = "majrur_preposition_projection"

        # Rule 5 — حال + motion/transformation hint → STATE (weak)
        if not semantic_role and role == "حال":
            semantic_role = ROLE_STATE
            confidence = CONF_WEAK
            source = "hal_state_projection"

        # Rule 6 — valency-only with unresolved syntax: do not assign (no hallucination)
        # (handled by only assigning when we have a matched rule above)

        if semantic_role and confidence >= CONF_WEAK:
            semantic_roles.append({
                "token_index": i,
                "surface": surface,
                "semantic_role": semantic_role,
                "confidence": round(confidence, 2),
                "source": source,
            })
            assigned += 1

    total = len(tokens)
    projection_coverage = round(assigned / total, 3) if total else 0.0

    return {
        "semantic_roles": semantic_roles,
        "projection_coverage": projection_coverage,
    }
