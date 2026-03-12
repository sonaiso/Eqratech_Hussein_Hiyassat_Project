# -*- coding: utf-8 -*-
"""
L13 — Real validation layer.

Checks cross-layer consistency from existing stage outputs only.
Emits structured issues, global_validity, and validated_layers_summary.
No analyzer logic; lightweight and honest.
"""

from __future__ import annotations

from typing import Any, Dict, List

from .builders import build_layer_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import STAGE_ORDER


def _issue(code: str, message: str, layer_id: str, severity: str) -> Dict[str, Any]:
    return {"code": code, "message": message, "layer_id": layer_id, "severity": severity}


def run_validation(layer_outputs: Dict[str, Any]) -> tuple[List[Dict[str, Any]], str, Dict[str, str], Any]:
    """
    Inspect layer_outputs (L0..L14) and return (issues, global_validity, validated_layers_summary, final_confidence).
    Uses existing outputs only; no deep linguistic logic.
    """
    issues: List[Dict[str, Any]] = []
    summary: Dict[str, str] = {}

    if not isinstance(layer_outputs, dict):
        issues.append(_issue("MISSING_PREREQUISITE", "layer_outputs missing or invalid", "L13", "error"))
        return issues, "invalid", summary, None

    for lid in STAGE_ORDER:
        lo = layer_outputs.get(lid) or {}
        if not isinstance(lo, dict):
            summary[lid] = "missing"
            continue
        st = lo.get("status", "missing")
        summary[lid] = st

    # L2 tokens
    L2 = layer_outputs.get("L2_TOKENIZATION") or {}
    tr2 = L2.get("transformation_result") or {}
    token_count = len(tr2.get("tokens") or [])
    tokens_empty = token_count == 0

    # L8 root extraction
    L8 = layer_outputs.get("L8_ROOT_EXTRACTION") or {}
    st8 = L8.get("status", "missing")
    tr8 = L8.get("transformation_result") or {}
    words8 = tr8.get("words") or []
    roots_present = sum(1 for w in words8 if w.get("root")) if words8 else 0
    if st8 == "success" and token_count > 0 and roots_present == 0 and words8:
        issues.append(_issue("EMPTY_SUCCESS", "L8 marked success but no roots extracted", "L8_ROOT_EXTRACTION", "warning"))
    if st8 == "success" and tokens_empty:
        issues.append(_issue("MISSING_PREREQUISITE", "L8 success but L2 has no tokens", "L8_ROOT_EXTRACTION", "warning"))

    # L9 wazn
    L9 = layer_outputs.get("L9_WAZN_MATCHING") or {}
    st9 = L9.get("status", "missing")
    tr9 = L9.get("transformation_result") or {}
    words9 = tr9.get("words") or []
    wazn_present = sum(1 for w in words9 if w.get("template") or w.get("word_wazn")) if words9 else 0
    if st9 == "success" and token_count > 0 and wazn_present == 0 and words9:
        issues.append(_issue("EMPTY_SUCCESS", "L9 marked success but no wazn/template", "L9_WAZN_MATCHING", "warning"))
    if st9 == "success" and tokens_empty:
        issues.append(_issue("MISSING_PREREQUISITE", "L9 success but L2 has no tokens", "L9_WAZN_MATCHING", "warning"))

    # L10 syntax
    L10 = layer_outputs.get("L10_SYNTAX") or {}
    st10 = L10.get("status", "missing")
    if st10 == "failed":
        issues.append(_issue("INCONSISTENT_STATUS", "L10 syntax failed", "L10_SYNTAX", "info"))

    # L11 i3rab
    L11 = layer_outputs.get("L11_I3RAB") or {}
    st11 = L11.get("status", "missing")
    tr11 = L11.get("transformation_result") or {}
    token_results = tr11.get("token_results") or []
    i3rab_evidence = sum(1 for t in token_results if t.get("i3rab_text")) if token_results else 0
    if st11 == "success" and token_count > 0 and i3rab_evidence == 0 and token_results:
        issues.append(_issue("I3RAB_MISSING", "L11 marked success but no i3rab_text in token_results", "L11_I3RAB", "warning"))
    if st11 == "success" and not token_results and token_count > 0:
        issues.append(_issue("EMPTY_SUCCESS", "L11 success with empty token_results", "L11_I3RAB", "warning"))

    # L12 semantic/rhetorical
    L12 = layer_outputs.get("L12_SEMANTIC_RHETORICAL") or {}
    st12 = L12.get("status", "missing")
    tr12 = L12.get("transformation_result") or {}
    rhetoric_count = tr12.get("rhetoric_count") or 0
    sentence_type = tr12.get("sentence_type")
    if st12 == "success" and token_count <= 1 and rhetoric_count == 0:
        issues.append(_issue("WEAK_SENTENCE_EVIDENCE", "L12 success with single token and no rhetoric", "L12_SEMANTIC_RHETORICAL", "info"))

    # L14 is not in layer_outputs when L13 runs (stage order: L13 then L14); skip L14 check.

    # Global validity
    error_count = sum(1 for i in issues if i.get("severity") == "error")
    warning_count = sum(1 for i in issues if i.get("severity") == "warning")
    info_count = sum(1 for i in issues if i.get("severity") == "info")
    if error_count >= 1:
        global_validity = "invalid"
    elif warning_count >= 2:
        global_validity = "weak"
    elif warning_count >= 1 or info_count >= 1:
        global_validity = "partial"
    else:
        global_validity = "valid"

    # Optional final_confidence: simple heuristic from issues
    final_confidence = None
    if global_validity != "invalid":
        final_confidence = max(0.0, min(1.0, 1.0 - 0.25 * error_count - 0.12 * warning_count - 0.02 * info_count))

    return issues, global_validity, summary, final_confidence


class RealL13Validation(BaseStage):
    """L13: Validation — cross-layer consistency, issues, global_validity."""

    def __init__(self) -> None:
        super().__init__("L13_VALIDATION", STAGE_NAMES["L13_VALIDATION"], 13)

    def run(self, pipeline: Dict[str, Any]) -> Dict[str, Any]:
        layer_outputs = pipeline.get("layer_outputs") or {}
        issues, global_validity, validated_layers_summary, final_confidence = run_validation(layer_outputs)
        status = "partial" if (issues and any(i.get("severity") in ("warning", "error") for i in issues)) else "success"
        transformation_result: Dict[str, Any] = {
            "global_validity": global_validity,
            "issues": issues,
            "validated_layers_summary": validated_layers_summary,
            "issue_count": len(issues),
        }
        if final_confidence is not None:
            transformation_result["final_confidence"] = round(final_confidence, 3)
        next_input = {"global_validity": global_validity, "validated_layers_summary": validated_layers_summary}
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input={"layer_outputs_keys": list(layer_outputs.keys())},
            transformation_result=transformation_result,
            raw_module_output=transformation_result,
            next_input=next_input,
        )
