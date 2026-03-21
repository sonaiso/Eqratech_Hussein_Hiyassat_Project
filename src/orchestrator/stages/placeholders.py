# -*- coding: utf-8 -*-
"""
Placeholder stages — valid LayerOutput, no real analysis.

Each emits a canonical LayerOutput with status pass_through, partial, or missing.
L11_I3RAB is explicit and present even as placeholder.
"""

from __future__ import annotations

from typing import Any, Dict

from ..builders import build_layer_output, get_previous_output
from ..types import LayerOutputDict, PipelineDict, STAGE_ORDER
from .base_stage import BaseStage


# Human-readable names for each stage (for layer_name)
STAGE_NAMES: Dict[str, str] = {
    "L0_INPUT": "Input acquisition",
    "L1_NORMALIZATION": "Normalization",
    "L2_TOKENIZATION": "Tokenization",
    "L3_SEGMENTATION": "Segmentation",
    "L4_OPERATORS": "Particles / operators",
    "L5_WORD_TYPING": "Word typing / routing",
    "L6_PHONOLOGY": "Phonology / CV",
    "L7_SYLLABIFICATION": "Syllabification",
    "L8_ROOT_EXTRACTION": "Root hypothesis extraction",
    "L8B_VERB_BAB_GOVERNANCE": "Verb bab / governance profile",
    "L9_WAZN_MATCHING": "Wazn matching",
    "L14_JAMID_MUSHTAQ": "Jamid vs Mushtaq (derivational classification)",
    "L13_VERB_TRANSFORMATION": "Verb transformation engine",
    "L12_GENDER_NUMBER": "Gender & Number",
    "L10_SYNTAX": "Syntax / sentence relations",
    "L10B_DEEP_SYNTAX": "Deep dependency syntax",
    "L11_I3RAB": "i3rab",
    "L11B_CAUSAL_I3RAB": "Causal i3rab reasoning",
    "L17_RULE_BASED_I3RAB": "Rule-based iʿrāb reasoner",
    "L12_SEMANTIC_RHETORICAL": "Semantic / rhetorical",
    "L12B_ANALOGICAL_REASONING": "Analogical reasoning",
    "L13_COGNITIVE_FUSION": "Cognitive fusion",
    "L13_VALIDATION": "Validation / hypothesis pruning",
    "L14_PRESENTATION": "Presentation / rendering",
}


class PlaceholderStage(BaseStage):
    """
    Placeholder stage: emits valid LayerOutput, no real analysis.
    status_default can be pass_through, partial, or missing.
    """

    def __init__(
        self,
        layer_id: str,
        stage_index: int,
        *,
        status_default: str = "pass_through",
        note: str = "Placeholder; adapter not connected.",
    ):
        name = STAGE_NAMES.get(layer_id, layer_id)
        super().__init__(layer_id, name, stage_index)
        self.status_default = status_default
        self.note = note

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        prev = get_previous_output(pipeline, self.stage_index)
        # L0 receives original_text as input
        if self.stage_index == 0:
            received = {"text": pipeline.get("original_text", "")}
            next_input = {"text": pipeline.get("original_text", "")}
        else:
            received = prev if prev else {"text": pipeline.get("original_text", "")}
            next_input = received  # pass-through
        warnings = [self.note] if self.note else []
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            self.status_default,
            received_input=received,
            transformation_result={"placeholder": True, "stage": self.layer_id},
            next_input=next_input,
            warnings=warnings,
        )


def make_l0_input_stage() -> BaseStage:
    """L0: input acquisition — captures raw text as success."""
    return PlaceholderStage("L0_INPUT", 0, status_default="success", note="Input captured; no adapter.")


def make_placeholder_stage(layer_id: str, stage_index: int, status: str = "pass_through") -> BaseStage:
    """Generic placeholder for any stage."""
    return PlaceholderStage(layer_id, stage_index, status_default=status)


def make_l11_i3rab_placeholder() -> BaseStage:
    """L11: i3rab — explicit independent layer; placeholder until adapter."""
    return PlaceholderStage(
        "L11_I3RAB",
        17,
        status_default="missing",
        note="L11 i3rab placeholder; adapter not connected.",
    )
