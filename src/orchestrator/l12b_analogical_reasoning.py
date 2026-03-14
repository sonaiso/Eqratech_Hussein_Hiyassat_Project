# -*- coding: utf-8 -*-
"""
L12B — Analogical Reasoning layer.

Lightweight, deterministic orchestration-level layer. Uses only existing
outputs from L5–L12. Resolves ambiguity and proposes inferred features
when evidence is weak. Does not call external analyzers.
"""

from __future__ import annotations

from typing import Any, Dict, List

from .builders import build_layer_output, get_previous_output
from .gates import compute_gates, gate_entry
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict


def _collect_inferences_and_resolutions(pipeline: PipelineDict) -> tuple[
    List[Dict[str, Any]],
    List[Dict[str, Any]],
]:
    """Inspect L5–L12 and produce analogical_inferences and ambiguity_resolutions."""
    lo = pipeline.get("layer_outputs") or {}
    inferences: List[Dict[str, Any]] = []
    resolutions: List[Dict[str, Any]] = []

    L5 = lo.get("L5_WORD_TYPING") or {}
    L8 = lo.get("L8_ROOT_EXTRACTION") or {}
    L9 = lo.get("L9_WAZN_MATCHING") or {}
    L10 = lo.get("L10_SYNTAX") or {}
    L11 = lo.get("L11_I3RAB") or {}
    L12 = lo.get("L12_SEMANTIC_RHETORICAL") or {}

    tr5 = L5.get("transformation_result") or {}
    tr8 = L8.get("transformation_result") or {}
    tr9 = L9.get("transformation_result") or {}
    tr10 = L10.get("transformation_result") or {}
    tr11 = L11.get("transformation_result") or {}
    tr12 = L12.get("transformation_result") or {}

    words5 = tr5.get("words") or []
    words8 = tr8.get("words") or []
    words9 = tr9.get("words") or []
    token_results = tr11.get("token_results") or []
    sentence_type = (tr12.get("sentence_type") or "").strip()
    rhetoric = tr12.get("rhetoric_signals") or []

    # Build word -> kind, root, template for alignment
    word_to_kind: Dict[str, str] = {w.get("word"): (w.get("kind") or "") for w in words5}
    word_to_root: Dict[str, str] = {}
    for w in words8:
        r = w.get("root")
        word_to_root[w.get("word")] = r if isinstance(r, str) and r else ""
    word_to_wazn: Dict[str, str] = {}
    for w in words9:
        t = w.get("template") or w.get("word_wazn")
        word_to_wazn[w.get("word")] = t if isinstance(t, str) and t else ""

    # 1) Morphological analogy: wazn = فاعل + kind = noun -> اسم فاعل
    faa3il_patterns = ("فاعل", "فَاعِل", "فاعِل")
    for w in words5:
        token = w.get("word") or ""
        kind = (word_to_kind.get(token) or "").strip().lower()
        wazn = (word_to_wazn.get(token) or "").strip()
        if kind in ("noun", "اسم") and wazn and any(p in wazn for p in faa3il_patterns):
            inferences.append({
                "token": token,
                "claim": "Likely active participle (ism fa'il) analogically similar to corpus patterns.",
                "reasoning_type": "morphological",
                "based_on": f"wazn={wazn}, word_typing=noun",
                "confidence_hint": "pattern match",
                "limitation": "Deterministic rule; no corpus lookup.",
                "status": "strong",
            })

    # 2) Pattern similarity: root + wazn exist, syntax role missing
    word_forms = tr10.get("word_forms") or []
    links = (tr10.get("links") or {}).get("isnadi") or []
    has_syntax_role = len(links) > 0 or any(
        (wf.get("role") or wf.get("syntax_role") or "") for wf in word_forms if isinstance(wf, dict)
    )
    for w in words8:
        token = w.get("word") or ""
        root = word_to_root.get(token)
        wazn = word_to_wazn.get(token)
        if root and wazn and not has_syntax_role:
            inferences.append({
                "token": token,
                "claim": "Possible syntactic role based on pattern similarity.",
                "reasoning_type": "syntactic",
                "based_on": f"root and wazn present; L10 links absent",
                "confidence_hint": "analogical similarity",
                "limitation": "No dependency parse; role is inferred only.",
                "status": "weak",
            })
            break

    # 3) Conditional rhetorical: sentence_type = شرط + operator لو/إن
    if sentence_type and "شرط" in sentence_type:
        inferences.append({
            "token": "",
            "claim": "Causal temporal framing inference from conditional sentence.",
            "reasoning_type": "semantic",
            "based_on": f"sentence_type={sentence_type}",
            "confidence_hint": "sentence classification",
            "limitation": "Surface sentence type only.",
            "status": "proposed",
        })

    # 3b) Discourse hints from shared connectives knowledge (optional, lightweight)
    try:
        from .connectives import classify_connective
        for w in words5:
            token = (w.get("word") or "").strip()
            if not token:
                continue
            c = classify_connective(token)
            if c:
                group = c.get("group") or ""
                inferences.append({
                    "token": token,
                    "claim": f"Discourse hint: {group} connective from shared connectives knowledge.",
                    "reasoning_type": "discourse",
                    "based_on": "connectives layer lookup",
                    "confidence_hint": "lexical match",
                    "limitation": "Hint only; not grammatical fact.",
                    "status": "weak",
                    "connective_group": group,
                })
    except Exception:
        pass

    # 4) I3rab fallback: i3rab_text exists but no structured role
    for t in token_results:
        surface = t.get("surface") or ""
        i3rab_text = (t.get("i3rab_text") or "").strip()
        if i3rab_text and not t.get("syntactic_function") and not t.get("governing_factor"):
            inferences.append({
                "token": surface,
                "claim": "Role inferred via surface i3rab analogy.",
                "reasoning_type": "syntactic",
                "based_on": "i3rab_text present; structured role absent",
                "confidence_hint": "surface i3rab analogy",
                "limitation": "Text-based i3rab only; no deep case reasoning.",
                "status": "weak",
            })

    # Ambiguity resolutions: when multiple competing roles could apply (simplified)
    if len(inferences) > 1 and words5:
        first_token = words5[0].get("word") or ""
        if first_token and word_to_kind.get(first_token) in ("noun", "verb", "اسم", "فعل"):
            resolutions.append({
                "token": first_token,
                "competing_roles": ["subject", "predicate"],
                "preferred_role": "subject",
                "reason": "First content word in sentence often subject in SV order.",
                "confidence_hint": "analogical similarity",
            })

    return inferences, resolutions


class RealL12BAnalogicalReasoning(BaseStage):
    """L12B: Analogical reasoning — infer from L5–L12 only; no external analyzers."""

    def __init__(self) -> None:
        super().__init__(
            "L12B_ANALOGICAL_REASONING",
            STAGE_NAMES["L12B_ANALOGICAL_REASONING"],
            16,
        )

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        gates = compute_gates(pipeline)
        gates_applied_list: List[Dict[str, Any]] = [
            gate_entry("has_tokens", gates["has_tokens"]),
            gate_entry("has_morphology_candidate", gates["has_morphology_candidate"]),
            gate_entry("has_syntax_candidate", gates["has_syntax_candidate"]),
        ]

        if not gates["has_tokens"]:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "skipped",
                received_input=get_previous_output(pipeline, self.stage_index) or {},
                transformation_result={
                    "analogical_inferences": [],
                    "ambiguity_resolutions": [],
                    "analogical_summary": {
                        "total_inferences": 0,
                        "strong_count": 0,
                        "weak_count": 0,
                    },
                },
                raw_module_output={},
                next_input={},
                gates_applied=gates_applied_list,
                warnings=["No tokens; analogical reasoning skipped."],
            )

        try:
            inferences, resolutions = _collect_inferences_and_resolutions(pipeline)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=get_previous_output(pipeline, self.stage_index) or {},
                transformation_result={
                    "analogical_inferences": [],
                    "ambiguity_resolutions": [],
                    "analogical_summary": {"total_inferences": 0, "strong_count": 0, "weak_count": 0},
                },
                raw_module_output={},
                next_input={},
                errors=[str(e)],
                gates_applied=gates_applied_list,
            )

        strong_count = sum(1 for i in inferences if i.get("status") == "strong")
        weak_count = sum(1 for i in inferences if i.get("status") in ("weak", "proposed"))
        summary = {
            "total_inferences": len(inferences),
            "strong_count": strong_count,
            "weak_count": weak_count,
        }
        status = "success" if inferences else "partial"
        received = get_previous_output(pipeline, self.stage_index) or {}
        next_input = {
            "analogical_inferences": inferences,
            "ambiguity_resolutions": resolutions,
            "analogical_summary": summary,
        }
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result={
                "analogical_inferences": inferences,
                "ambiguity_resolutions": resolutions,
                "analogical_summary": summary,
            },
            raw_module_output={"analogical_inferences": inferences, "ambiguity_resolutions": resolutions},
            next_input=next_input,
            gates_applied=gates_applied_list,
            reused_module={"file": "orchestrator/l12b_analogical_reasoning.py", "symbol": "RealL12BAnalogicalReasoning", "mode": "adapter"},
        )
