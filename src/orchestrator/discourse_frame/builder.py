# -*- coding: utf-8 -*-
"""
Build discourse frames from connectives, L10B clause structure, L12/L12B.
Additive only; does not override syntax or i'rab.
Tightening: conditional/adversative/explanation vs causation/negation/scope/weak-frame suppression.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

# Scope hint policy (Rule 5)
SCOPE_TOKEN_LOCAL = "token-local"
SCOPE_PHRASE_LEVEL = "phrase-level"
SCOPE_CLAUSE_LEVEL = "clause-level"
SCOPE_SENTENCE_LEVEL = "sentence-level"

# Confidence bands
CONF_STRONG = "strong"
CONF_MEDIUM = "medium"
CONF_WEAK = "weak"

# Frame type constants
FRAME_CONDITIONAL = "conditional"
FRAME_ADVERSATIVE = "adversative"
FRAME_EXPLANATION = "explanation"
FRAME_CAUSATION = "causation"
FRAME_NEGATION = "negation"


def _is_nonconditional_inna_like(token: str) -> bool:
    """
    Conservative discourse guard:
    إِنَّ / أَنَّ and ambiguous undiacritized إن/أن/ان must not emit conditional frames.
    """
    if not token:
        return False
    t = (token or "").strip()
    if "ْ" in t:
        return False
    norm = []
    for c in t:
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        norm.append(c)
    return "".join(norm).strip() in ("إن", "أن", "ان")


def _has_clause_support_conditional(lo: Dict[str, Any]) -> bool:
    """True if L10B main_clause_type or clause_units support conditional structure."""
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    tr = l10b.get("transformation_result") or {}
    summary = tr.get("syntax_summary") or {}
    main_type = (summary.get("main_clause_type") or "").strip().lower()
    if "conditional" in main_type or "شرط" in main_type:
        return True
    clauses = tr.get("clause_units") or []
    for c in clauses:
        ctype = (c.get("type") or "").strip().lower()
        if "conditional" in ctype or "condition" in ctype:
            return True
    return False


def _has_discourse_support(lo: Dict[str, Any], group: str) -> bool:
    """True if L12B has discourse inference matching group (e.g. conditional, adversative)."""
    l12b = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr = l12b.get("transformation_result") or {}
    inferences = tr.get("analogical_inferences") or []
    for inf in inferences:
        if inf.get("reasoning_type") != "discourse":
            continue
        if (inf.get("connective_group") or "").strip() == group:
            return True
    return False


def _has_causation_support(lo: Dict[str, Any]) -> bool:
    """True if L12/L12B suggests cause/effect (conservative)."""
    l12b = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr = l12b.get("transformation_result") or {}
    inferences = tr.get("analogical_inferences") or []
    for inf in inferences:
        claim = (inf.get("claim") or "").lower()
        if "cause" in claim or "effect" in claim or "سبب" in claim or "نتيجة" in claim:
            return True
    return False


def _connective_tokens_from_lo(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Collect connective tokens from L10B nodes (connective_group) or L12B discourse inferences."""
    out: List[Dict[str, Any]] = []
    seen: set = set()
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    tr10b = l10b.get("transformation_result") or {}
    nodes = tr10b.get("dependency_nodes") or []
    for n in nodes:
        group = (n.get("connective_group") or "").strip()
        if not group:
            continue
        surf = (n.get("surface") or "").strip()
        key = (surf, group)
        if key in seen:
            continue
        seen.add(key)
        out.append({"token": surf, "connective_group": group, "source": "L10B"})
    l12b = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr12b = l12b.get("transformation_result") or {}
    for inf in tr12b.get("analogical_inferences") or []:
        if inf.get("reasoning_type") != "discourse":
            continue
        group = (inf.get("connective_group") or "").strip()
        token = (inf.get("token") or "").strip()
        if not group or not token:
            continue
        key = (token, group)
        if key in seen:
            continue
        seen.add(key)
        out.append({"token": token, "connective_group": group, "source": "L12B"})
    return out


def build_discourse_frames(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """
    Build discourse frames from L4/L10B/L12/L12B and connectives layer.
    Returns dict for lo["DISCOURSE_FRAME_BUILDER"] or None.
    Tightening: conditional/adversative/explanation vs causation/negation/scope/weak suppression.
    """
    try:
        from ..connectives import classify_connective
        from ..connectives.models import (
            GROUP_ADVERSATIVE,
            GROUP_CONDITIONAL,
            GROUP_EXPLANATION_CAUSATION,
            GROUP_NEGATION,
        )
    except Exception:
        return None

    frames: List[Dict[str, Any]] = []
    clause_support_conditional = _has_clause_support_conditional(lo)
    discourse_conditional = _has_discourse_support(lo, GROUP_CONDITIONAL)
    discourse_adversative = _has_discourse_support(lo, GROUP_ADVERSATIVE)
    causation_support = _has_causation_support(lo)

    connective_items = _connective_tokens_from_lo(lo)
    if not connective_items:
        return {
            "frames": [],
            "frame_count": 0,
            "frame_types": [],
            "coverage_hint": "no connective tokens from L10B/L12B",
            "strong_frame_count": 0,
            "weak_frame_count": 0,
        }

    for item in connective_items:
        token = (item.get("token") or "").strip()
        group = (item.get("connective_group") or "").strip()
        if not token or not group:
            continue
        if group == "conditional" and _is_nonconditional_inna_like(token):
            continue
        c = classify_connective(token)
        if not c:
            continue
        frame_type: Optional[str] = None
        confidence = CONF_WEAK
        scope_hint = SCOPE_TOKEN_LOCAL
        limitation: Optional[str] = None

        # Rule 1 — Conditional
        if group == GROUP_CONDITIONAL:
            frame_type = FRAME_CONDITIONAL
            if clause_support_conditional:
                confidence = CONF_STRONG
                scope_hint = SCOPE_CLAUSE_LEVEL
            elif discourse_conditional:
                confidence = CONF_MEDIUM
                scope_hint = SCOPE_SENTENCE_LEVEL
            else:
                confidence = CONF_WEAK
                limitation = "conditional frame inferred from connective recognition only"

        # Rule 2 — Adversative
        elif group == GROUP_ADVERSATIVE:
            frame_type = FRAME_ADVERSATIVE
            if discourse_adversative:
                confidence = CONF_MEDIUM
                scope_hint = SCOPE_SENTENCE_LEVEL
            else:
                confidence = CONF_WEAK
                limitation = "adversative frame lacks downstream contrast support"

        # Rule 3 — Explanation vs Causation
        elif group == GROUP_EXPLANATION_CAUSATION:
            if causation_support:
                frame_type = FRAME_CAUSATION
                confidence = CONF_MEDIUM
                scope_hint = SCOPE_SENTENCE_LEVEL
            else:
                frame_type = FRAME_EXPLANATION
                confidence = CONF_MEDIUM
                limitation = "causation vs explanation not fully disambiguated"

        # Rule 4 — Negation
        elif group == GROUP_NEGATION:
            frame_type = FRAME_NEGATION
            if discourse_conditional or clause_support_conditional:
                confidence = CONF_MEDIUM
                scope_hint = SCOPE_CLAUSE_LEVEL
            else:
                confidence = CONF_WEAK
                limitation = "negation frame from token only; no sentence-level polarity"

        else:
            frame_type = group.replace(" ", "_") if group else "unknown"
            confidence = CONF_WEAK
            limitation = "connective group not in conditional/adversative/explanation/negation"

        # Rule 6 — Weak-frame suppression: keep WEAK but with clear limitation; do not suppress entirely
        # (we keep all frames but mark confidence and limitation so downstream can filter)
        if not frame_type:
            continue

        frames.append({
            "trigger": token,
            "frame_type": frame_type,
            "scope_hint": scope_hint,
            "confidence": confidence,
            "connective_group": group,
            "limitation": limitation,
        })

    frame_types = list(dict.fromkeys(f.get("frame_type") for f in frames if f.get("frame_type")))
    strong_count = sum(1 for f in frames if f.get("confidence") == CONF_STRONG)
    weak_count = sum(1 for f in frames if f.get("confidence") == CONF_WEAK)
    total = len(connective_items) or 1
    coverage_hint = f"{len(frames)} frames from {len(connective_items)} connective tokens"

    return {
        "frames": frames,
        "frame_count": len(frames),
        "frame_types": frame_types,
        "coverage_hint": coverage_hint,
        "strong_frame_count": strong_count,
        "weak_frame_count": weak_count,
    }
