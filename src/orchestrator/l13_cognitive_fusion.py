# -*- coding: utf-8 -*-
"""
L13 — Cognitive Fusion Layer.

Critical reasoning stage: reconcile, prioritize, stabilize, reduce ambiguity.
Does NOT invent linguistic facts. Does NOT override upstream evidence.
Reads only from structured outputs (L4, L5, L8, L9, L10, L11, L12, L12B, pre_stage13_audit).
"""

from __future__ import annotations

from typing import Any, Dict, List, Tuple

from .builders import build_layer_output, get_previous_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict

# Hierarchy weights (do not invent; only use for arbitration)
SOURCE_WEIGHTS = {
    "ROOT": 0.95,
    "WAZN": 0.85,
    "OPERATOR": 0.80,
    "MORPHO": 0.60,
    "SYNTAX": 0.55,
    "I3RAB": 0.50,
    "ANALOGICAL": 0.40,
    "RHETORICAL": 0.35,
    "WORD_TYPING": 0.65,
}

CONFIDENCE_MIN = 0.05
CONFIDENCE_MAX = 0.98


def _get_tokens(pipeline: PipelineDict) -> List[str]:
    """Token list from L2 or L5; never re-analyze raw."""
    lo = pipeline.get("layer_outputs") or {}
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    if tokens:
        return [t.get("word") or "" for t in tokens if t.get("word")]
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words = tr5.get("words") or []
    return [w.get("word") or "" for w in words if w.get("word")]


def _fusion_one_token(
    token: str,
    idx: int,
    lo: Dict[str, Any],
    conservative: bool,
) -> Dict[str, Any]:
    """
    Build fusion_state for one token. Never invent.
    Priority: Root+Wazn > Operator > Morpho > Syntax > I3rab > Analogical > Rhetorical.
    """
    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    tr10 = (lo.get("L10_SYNTAX") or {}).get("transformation_result") or {}
    tr11 = (lo.get("L11_I3RAB") or {}).get("transformation_result") or {}
    tr12 = (lo.get("L12_SEMANTIC_RHETORICAL") or {}).get("transformation_result") or {}
    tr12b = (lo.get("L12B_ANALOGICAL_REASONING") or {}).get("transformation_result") or {}

    words5 = tr5.get("words") or []
    words8 = tr8.get("words") or []
    words9 = tr9.get("words") or []
    token_results = tr11.get("token_results") or []
    inferences_12b = tr12b.get("analogical_inferences") or []

    word_5 = next((w for w in words5 if (w.get("word") or "") == token), None)
    word_8 = next((w for w in words8 if (w.get("word") or "") == token), None)
    word_9 = next((w for w in words9 if (w.get("word") or "") == token), None)
    tok_11 = next((t for t in token_results if (t.get("surface") or "") == token), None)

    op_words = tr4.get("words") or []
    is_operator = any((w.get("word") or "") == token and w.get("operator") for w in op_words)

    evidence_stack: List[Dict[str, str]] = []
    stable_pos = ""
    stable_role = ""
    tense_final = ""
    definiteness_final = ""
    number_final = ""
    gender_final = ""
    conflicts_resolved: List[str] = []
    ambiguities_remaining: List[str] = []
    fusion_error_flag = False

    # 1) Operator (never override)
    if is_operator:
        stable_pos = "operator"
        evidence_stack.append({"source": "OPERATOR", "weight": SOURCE_WEIGHTS["OPERATOR"]})
    # 2) Word typing from L5 (only if not operator)
    if word_5 and not stable_pos:
        kind = (word_5.get("kind") or "").strip() or ""
        if kind:
            stable_pos = kind
            evidence_stack.append({"source": "WORD_TYPING", "weight": SOURCE_WEIGHTS["WORD_TYPING"]})
    if not stable_pos and word_5:
        stable_pos = (word_5.get("kind") or "").strip() or "unknown"

    # 3) Root (confirm only; never generate)
    root_val = ""
    if word_8 and word_8.get("root"):
        root_val = word_8.get("root") if isinstance(word_8.get("root"), str) else ""
    if root_val:
        evidence_stack.append({"source": "ROOT", "weight": SOURCE_WEIGHTS["ROOT"]})

    # 4) Wazn (confirm only; never generate)
    wazn_val = (word_9.get("template") or word_9.get("word_wazn") or "") if word_9 else ""
    if isinstance(wazn_val, str) and wazn_val:
        evidence_stack.append({"source": "WAZN", "weight": SOURCE_WEIGHTS["WAZN"]})
    if word_9 and (word_9.get("template") or word_9.get("word_wazn")):
        evidence_stack.append({"source": "MORPHO", "weight": SOURCE_WEIGHTS["MORPHO"]})

    # 5) Syntax (only if evidence; never assign without evidence)
    if not conservative:
        links = (tr10.get("links") or {}).get("isnadi") or []
        wf = tr10.get("word_forms") or []
        role = ""
        if links or wf:
            evidence_stack.append({"source": "SYNTAX", "weight": SOURCE_WEIGHTS["SYNTAX"]})
            for w in wf:
                if (w.get("word") or w.get("surface") or "") == token:
                    role = (w.get("role") or w.get("syntax_role") or "").strip()
                    break
        if role:
            stable_role = role

    # 6) I3rab (textual hints only)
    if tok_11 and (tok_11.get("i3rab_text") or "").strip():
        evidence_stack.append({"source": "I3RAB", "weight": SOURCE_WEIGHTS["I3RAB"]})
        if not conservative:
            pass  # could set definiteness/number/gender from c2e if we had it in L11

    # 7) Analogical (only in normal mode; do not upgrade to fact)
    if not conservative:
        for inf in inferences_12b:
            if (inf.get("token") or "") == token and inf.get("status") == "strong":
                evidence_stack.append({"source": "ANALOGICAL", "weight": SOURCE_WEIGHTS["ANALOGICAL"]})
                break
    # 8) Rhetorical (weak; never upgrade to grammatical fact)
    if tr12.get("sentence_type") or (tr12.get("rhetoric_signals") or []):
        pass  # could add RHETORICAL with low weight only if token involved; skip to avoid overclaim

    # Confidence: sum(supporting) / sum(all available for token)
    all_weights = list(SOURCE_WEIGHTS.values())
    sum_all = sum(all_weights)
    sum_supporting = sum(e.get("weight", 0) for e in evidence_stack if isinstance(e.get("weight"), (int, float)))
    if sum_all <= 0:
        confidence = CONFIDENCE_MIN
    else:
        confidence = sum_supporting / sum_all
    confidence = max(CONFIDENCE_MIN, min(CONFIDENCE_MAX, round(confidence, 4)))
    if confidence >= 0.98:
        confidence = CONFIDENCE_MAX
    if confidence <= 0.05:
        confidence = CONFIDENCE_MIN

    return {
        "token": token,
        "stable_pos": stable_pos or "unknown",
        "stable_role": stable_role or "",
        "tense_final": tense_final,
        "definiteness_final": definiteness_final,
        "number_final": number_final,
        "gender_final": gender_final,
        "confidence": confidence,
        "evidence_stack": evidence_stack,
        "conflicts_resolved": conflicts_resolved,
        "ambiguities_remaining": ambiguities_remaining,
        "fusion_error_flag": fusion_error_flag,
    }


def _run_fusion(pipeline: PipelineDict) -> Tuple[Dict[str, Any], str]:
    """Compute cognitive_fusion dict and fusion_mode. Returns (cognitive_fusion, status)."""
    tokens = _get_tokens(pipeline)
    audit = pipeline.get("pre_stage13_audit") or {}
    readiness_band = (audit.get("readiness_band") or "").strip()
    conservative = readiness_band == "LOW"
    fusion_mode = "conservative" if conservative else "normal"

    lo = pipeline.get("layer_outputs") or {}
    token_states: List[Dict[str, Any]] = []
    for i, token in enumerate(tokens):
        state = _fusion_one_token(token, i, lo, conservative)
        token_states.append(state)

    confidences = [s.get("confidence") or 0.0 for s in token_states]
    global_confidence = (sum(confidences) / len(confidences)) if confidences else CONFIDENCE_MIN
    global_confidence = max(CONFIDENCE_MIN, min(CONFIDENCE_MAX, round(global_confidence, 4)))
    high = sum(1 for c in confidences if c >= 0.6)
    low = sum(1 for c in confidences if c < 0.4)
    unresolved = sum(len(s.get("ambiguities_remaining") or []) for s in token_states)

    return {
        "fusion_mode": fusion_mode,
        "token_states": token_states,
        "global_confidence": global_confidence,
        "tokens_high_confidence": high,
        "tokens_low_confidence": low,
        "unresolved_ambiguities": unresolved,
    }, "success" if token_states else "partial"


class RealL13CognitiveFusion(BaseStage):
    """L13: Cognitive Fusion — hierarchical evidence arbitration; no invention."""

    def __init__(self) -> None:
        super().__init__(
            "L13_COGNITIVE_FUSION",
            STAGE_NAMES["L13_COGNITIVE_FUSION"],
            22,
        )

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        received = get_previous_output(pipeline, self.stage_index) or {}
        try:
            fusion_result, status = _run_fusion(pipeline)
        except Exception as e:
            fusion_result = {
                "fusion_mode": "conservative",
                "token_states": [],
                "global_confidence": CONFIDENCE_MIN,
                "tokens_high_confidence": 0,
                "tokens_low_confidence": 0,
                "unresolved_ambiguities": 0,
            }
            status = "failed"
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result=fusion_result,
                raw_module_output=fusion_result,
                next_input=received,
                errors=[str(e)],
            )
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result=fusion_result,
            raw_module_output=fusion_result,
            next_input=fusion_result,
            reused_module={
                "file": "orchestrator/l13_cognitive_fusion.py",
                "symbol": "RealL13CognitiveFusion",
                "mode": "adapter",
            },
        )
