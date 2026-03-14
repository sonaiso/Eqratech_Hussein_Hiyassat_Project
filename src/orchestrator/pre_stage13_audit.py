# -*- coding: utf-8 -*-
"""
Pre-Stage-13 Readiness Audit.

Diagnostic structural audit run once per pipeline before L13 (validation).
Evaluates reliability and maturity of upstream evidence sources.
Not a linguistic stage; orchestration-level only.
"""

from __future__ import annotations

from typing import Any, Dict, List, Tuple

# Source id -> (layer_id, default fusion_weight, decision_reliability, default depth)
_AUDIT_SOURCES: List[Tuple[str, str, float, str, int]] = [
    ("ROOT_EXTRACTION", "L8_ROOT_EXTRACTION", 0.95, "strong", 3),
    ("VERB_GOVERNANCE", "L8B_VERB_BAB_GOVERNANCE", 0.72, "strong", 2),
    ("PATTERN_MATCH", "L9_WAZN_MATCHING", 0.85, "strong", 3),
    ("OPERATOR_DETECTION", "L4_OPERATORS", 0.80, "strong", 2),
    ("WORD_TYPING", "L5_WORD_TYPING", 0.65, "moderate", 2),
    ("MORPHO_FEATURES", "L9_WAZN_MATCHING", 0.60, "moderate", 2),
    ("SYNTAX", "L10_SYNTAX", 0.55, "moderate_limited", 2),
    ("DEEP_SYNTAX", "L10B_DEEP_SYNTAX", 0.58, "moderate_limited", 2),
    ("I3RAB", "L11_I3RAB", 0.50, "moderate_textual", 2),
    ("SEMANTIC_RHETORICAL", "L12_SEMANTIC_RHETORICAL", 0.35, "weak", 1),
    ("ANALOGICAL_REASONING", "L12B_ANALOGICAL_REASONING", 0.40, "supportive", 1),
]


def _availability(lo: Dict[str, Any], layer_id: str) -> bool:
    """True if layer ran and has usable output (not missing/failed with empty result)."""
    layer = lo.get(layer_id) or {}
    status = (layer.get("status") or "").strip().lower()
    if status in ("missing", "failed"):
        return False
    tr = layer.get("transformation_result") or {}
    if layer_id == "L8_ROOT_EXTRACTION":
        words = tr.get("words") or []
        return len(words) > 0 and any(w.get("root") for w in words)
    if layer_id == "L8B_VERB_BAB_GOVERNANCE":
        profiles = tr.get("verb_governance_profiles") or []
        summary = tr.get("governance_summary") or {}
        return (summary.get("resolved_profiles") or 0) > 0 or (summary.get("verb_count") or 0) > 0
    if layer_id == "L9_WAZN_MATCHING":
        words = tr.get("words") or []
        return len(words) > 0 and any(w.get("template") or w.get("word_wazn") for w in words)
    if layer_id == "L4_OPERATORS":
        return (tr.get("operator_count") or 0) >= 0 and len(tr.get("words") or []) > 0
    if layer_id == "L5_WORD_TYPING":
        return len(tr.get("words") or []) > 0
    if layer_id == "L10_SYNTAX":
        if status == "failed":
            return False
        return len(tr.get("word_forms") or []) > 0 or bool((tr.get("links") or {}).get("isnadi"))
    if layer_id == "L10B_DEEP_SYNTAX":
        if status == "failed":
            return False
        summary = tr.get("syntax_summary") or {}
        return (summary.get("resolved_edges") or 0) > 0 or len(tr.get("dependency_edges") or []) > 0
    if layer_id == "L11_I3RAB":
        results = tr.get("token_results") or []
        return any(t.get("i3rab_text") for t in results)
    if layer_id == "L12_SEMANTIC_RHETORICAL":
        return bool(tr.get("sentence_type")) or len(tr.get("rhetoric_signals") or []) > 0
    if layer_id == "L12B_ANALOGICAL_REASONING":
        return (tr.get("analogical_summary") or {}).get("total_inferences", 0) > 0 or len(tr.get("ambiguity_resolutions") or []) > 0
    return status not in ("missing", "failed")


def _structural_depth(lo: Dict[str, Any], source_id: str, layer_id: str) -> int:
    """0=missing, 1=surface heuristics, 2=structured partial, 3=structurally modeled."""
    layer = lo.get(layer_id) or {}
    status = (layer.get("status") or "").strip().lower()
    tr = layer.get("transformation_result") or {}
    if status in ("missing", "failed"):
        return 0
    if source_id == "ROOT_EXTRACTION":
        return 3
    if source_id == "VERB_GOVERNANCE":
        summary = (tr.get("governance_summary") or {})
        return 2 if (summary.get("resolved_profiles") or 0) > 0 else 1
    if source_id == "PATTERN_MATCH":
        return 3
    if source_id == "OPERATOR_DETECTION":
        return 2
    if source_id == "WORD_TYPING":
        return 2
    if source_id == "MORPHO_FEATURES":
        return 2
    if source_id == "SYNTAX":
        links = (tr.get("links") or {}).get("isnadi") or []
        return 2 if links else 1
    if source_id == "DEEP_SYNTAX":
        summary = tr.get("syntax_summary") or {}
        return 2 if (summary.get("resolved_edges") or 0) > 0 else 1
    if source_id == "I3RAB":
        return 2  # structured token_results but textual
    if source_id == "SEMANTIC_RHETORICAL":
        return 1
    if source_id == "ANALOGICAL_REASONING":
        return 1
    return 1


def _known_limitations(source_id: str, availability: bool, depth: int) -> List[str]:
    """Known limitations per source."""
    out: List[str] = []
    if source_id == "SYNTAX":
        out.append("syntax depth may be shallow; full dependency parse not guaranteed")
    if source_id == "I3RAB":
        out.append("i3rab evidence is text-based; no deep syntactic case reasoning")
    if source_id == "SEMANTIC_RHETORICAL":
        out.append("rhetoric detection is surface/syntax-assisted")
    if source_id == "ANALOGICAL_REASONING":
        out.append("analogical reasoning is heuristic-based; no ML or corpus lookup")
    if not availability:
        out.append("source unavailable or empty")
    if depth == 0:
        out.append("structural depth missing")
    return out


class PreStage13ReadinessAudit:
    """
    Audit upstream evidence sources before L13.
    Produces readiness_score, readiness_band, per-source reliability, blocking_issues, advisory_notes.
    """

    def run_audit(self, pipeline_object: Dict[str, Any]) -> Dict[str, Any]:
        lo = pipeline_object.get("layer_outputs") or {}
        sources: List[Dict[str, Any]] = []
        blocking_issues: List[str] = []
        advisory_notes: List[str] = []
        weighted_sum = 0.0
        weight_total = 0.0

        for source_id, layer_id, weight, reliability, default_depth in _AUDIT_SOURCES:
            availability = _availability(lo, layer_id)
            depth = _structural_depth(lo, source_id, layer_id)
            limitations = _known_limitations(source_id, availability, depth)
            fusion_weight = weight
            if availability:
                weighted_sum += fusion_weight
            weight_total += fusion_weight
            sources.append({
                "source": source_id,
                "availability": availability,
                "structural_depth": depth,
                "decision_reliability": reliability,
                "known_limitations": limitations,
                "fusion_weight": fusion_weight,
            })
            if source_id == "ROOT_EXTRACTION" and not availability:
                blocking_issues.append("no root extraction")
            if limitations:
                if source_id == "SEMANTIC_RHETORICAL":
                    advisory_notes.append("rhetoric evidence weak")
                if source_id == "I3RAB":
                    advisory_notes.append("i3rab textual only")
                if source_id == "ANALOGICAL_REASONING":
                    advisory_notes.append("analogical reasoning heuristic-based")

        # Blocking: no tokens
        L2 = lo.get("L2_TOKENIZATION") or {}
        tr2 = L2.get("transformation_result") or {}
        if len(tr2.get("tokens") or []) == 0:
            blocking_issues.append("no tokens")
        # Syntax failed completely
        L10 = lo.get("L10_SYNTAX") or {}
        if L10.get("status") == "failed":
            blocking_issues.append("syntax failed completely")

        advisory_notes = list(dict.fromkeys(advisory_notes))

        readiness_score = weighted_sum / weight_total if weight_total else 0.0
        if readiness_score >= 0.75:
            readiness_band = "HIGH"
        elif readiness_score >= 0.55:
            readiness_band = "MEDIUM"
        else:
            readiness_band = "LOW"

        return {
            "readiness_score": round(readiness_score, 4),
            "readiness_band": readiness_band,
            "sources": sources,
            "blocking_issues": blocking_issues,
            "advisory_notes": advisory_notes,
        }
