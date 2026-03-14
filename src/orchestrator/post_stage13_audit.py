# -*- coding: utf-8 -*-
"""
Post-Stage-13 Fusion Audit.

Runs AFTER L13 Cognitive Fusion. Evaluates whether fusion output is
stable, coherent, and aligned with upstream evidence.
Does NOT replace validation. Does NOT modify fusion or upstream outputs.
Deterministic, conservative, inspection-only.
"""

from __future__ import annotations

from typing import Any, Dict, List

CONFIDENCE_MIN = 0.05
CONFIDENCE_MAX = 0.98

STRONG_SOURCES = frozenset({"ROOT", "WAZN", "OPERATOR", "WORD_TYPING"})
WEAK_SOURCES = frozenset({"RHETORICAL", "ANALOGICAL"})


def _issue(code: str, message: str, severity: str, token: str = "") -> Dict[str, Any]:
    out: Dict[str, Any] = {"code": code, "message": message, "severity": severity}
    if token:
        out["token"] = token
    return out


class PostStage13FusionAudit:
    """
    Post-fusion consistency audit. Only inspects pipeline; never overwrites L13 results.
    """

    def run_audit(self, pipeline_object: Dict[str, Any]) -> Dict[str, Any]:
        issues: List[Dict[str, Any]] = []
        advisory_notes: List[str] = []
        cf = pipeline_object.get("cognitive_fusion") or {}
        pre_audit = pipeline_object.get("pre_stage13_audit") or {}
        lo = pipeline_object.get("layer_outputs") or {}

        token_states = cf.get("token_states") or []
        fusion_mode = (cf.get("fusion_mode") or "").strip()
        global_conf = cf.get("global_confidence")
        unresolved_summary = cf.get("unresolved_ambiguities", 0)

        # MISSING_FUSION_STATE
        if not token_states and not cf:
            return {
                "fusion_consistency": "low",
                "resolved_conflicts": 0,
                "remaining_ambiguities": 0,
                "issues": [_issue("MISSING_FUSION_STATE", "No fusion state in pipeline.", "error")],
                "advisory_notes": ["Fusion output missing; audit cannot evaluate."],
                "source_alignment": {"strong_sources_respected": False, "weak_source_overreach": True},
            }
        if not token_states:
            issues.append(_issue("MISSING_FUSION_STATE", "Fusion token_states empty.", "warning"))

        # Resolved/remaining counts
        resolved_conflicts = sum(len(ts.get("conflicts_resolved") or []) for ts in token_states)
        remaining_from_tokens = sum(len(ts.get("ambiguities_remaining") or []) for ts in token_states)
        if remaining_from_tokens != unresolved_summary:
            issues.append(_issue(
                "UNRESOLVED_AMBIGUITY_MISMATCH",
                f"Sum of token ambiguities_remaining ({remaining_from_tokens}) != summary ({unresolved_summary}).",
                "info",
            ))
        remaining_ambiguities = unresolved_summary

        # Confidence sanity
        if global_conf is not None and (global_conf < CONFIDENCE_MIN or global_conf > CONFIDENCE_MAX):
            issues.append(_issue(
                "CONFIDENCE_OUT_OF_RANGE",
                f"Global confidence {global_conf} outside [{CONFIDENCE_MIN}, {CONFIDENCE_MAX}].",
                "error",
            ))
        for ts in token_states:
            c = ts.get("confidence")
            if c is not None and (c < CONFIDENCE_MIN or c > CONFIDENCE_MAX):
                issues.append(_issue(
                    "CONFIDENCE_OUT_OF_RANGE",
                    f"Token confidence {c} out of range.",
                    "warning",
                    ts.get("token", ""),
                ))

        # POS consistency: fusion stable_pos vs L5 kind (only clear noun/verb contradiction)
        tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
        words5 = tr5.get("words") or []
        kind_by_token = {w.get("word"): (w.get("kind") or "").strip().lower() for w in words5}
        for ts in token_states:
            token = ts.get("token") or ""
            stable_pos = (ts.get("stable_pos") or "").strip().lower()
            upstream_kind = kind_by_token.get(token, "")
            if not upstream_kind or not stable_pos or stable_pos == "unknown":
                continue
            up_noun = upstream_kind in ("noun", "اسم")
            up_verb = upstream_kind in ("verb", "فعل")
            st_noun = "noun" in stable_pos or "اسم" in stable_pos
            st_verb = "verb" in stable_pos or "فعل" in stable_pos
            if up_noun and st_verb:
                issues.append(_issue("FUSION_POS_CONTRADICTION", "Fusion stable_pos contradicts L5 kind (noun vs verb).", "warning", token))
            elif up_verb and st_noun:
                issues.append(_issue("FUSION_POS_CONTRADICTION", "Fusion stable_pos contradicts L5 kind (verb vs noun).", "warning", token))

        # Role consistency: in normal mode, stable_role should not contradict L10 when L10 has strong evidence
        tr10 = (lo.get("L10_SYNTAX") or {}).get("transformation_result") or {}
        links = (tr10.get("links") or {}).get("isnadi") or []
        if fusion_mode == "conservative" and token_states:
            roles_assigned = sum(1 for ts in token_states if (ts.get("stable_role") or "").strip())
            if roles_assigned > 0:
                issues.append(_issue(
                    "CONSERVATIVE_MODE_VIOLATION",
                    "Conservative mode expected but fusion assigned stable_role.",
                    "warning",
                ))
                advisory_notes.append("Conservative mode should not resolve syntactic roles.")

        # Weak-source overreach: token has upstream root/wazn but fusion evidence only weak
        weak_overreach = False
        strong_respected = True
        tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
        tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
        words8 = tr8.get("words") or []
        words9 = tr9.get("words") or []
        for ts in token_states:
            token = ts.get("token") or ""
            stack = ts.get("evidence_stack") or []
            sources = {s.get("source") for s in stack if s.get("source")}
            has_strong_in_stack = bool(sources & STRONG_SOURCES)
            only_weak_in_stack = sources and not has_strong_in_stack and (sources & WEAK_SOURCES)
            has_root = any((w.get("word") or "") == token and w.get("root") for w in words8)
            has_wazn = any((w.get("word") or "") == token and (w.get("template") or w.get("word_wazn")) for w in words9)
            if (has_root or has_wazn) and only_weak_in_stack:
                weak_overreach = True
                issues.append(_issue(
                    "WEAK_SOURCE_OVERREACH",
                    "Token has upstream root/wazn but fusion evidence only weak sources.",
                    "info",
                    token,
                ))
            if (has_root or has_wazn) and has_strong_in_stack:
                strong_respected = strong_respected and True

        source_alignment = {
            "strong_sources_respected": not weak_overreach,
            "weak_source_overreach": weak_overreach,
        }

        # Grade fusion_consistency
        error_count = sum(1 for i in issues if i.get("severity") == "error")
        warning_count = sum(1 for i in issues if i.get("severity") == "warning")
        if error_count >= 1 or warning_count >= 2:
            fusion_consistency = "low"
        elif warning_count >= 1 or remaining_ambiguities > len(token_states) or weak_overreach:
            fusion_consistency = "medium"
        else:
            fusion_consistency = "high"

        return {
            "fusion_consistency": fusion_consistency,
            "resolved_conflicts": resolved_conflicts,
            "remaining_ambiguities": remaining_ambiguities,
            "issues": issues,
            "advisory_notes": list(dict.fromkeys(advisory_notes)),
            "source_alignment": source_alignment,
        }
