# -*- coding: utf-8 -*-
"""
Orchestrator types — Stage 2 contract alignment.

Fixed stage IDs and status values; no analyzer logic.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, TypedDict

# Fixed stage order (Stage 2 contract)
STAGE_ORDER: List[str] = [
    "L0_INPUT",
    "L1_NORMALIZATION",
    "L2_TOKENIZATION",
    "L3_SEGMENTATION",
    "L4_OPERATORS",
    "L5_WORD_TYPING",
    "L6_PHONOLOGY",
    "L7_SYLLABIFICATION",
    "L8_ROOT_EXTRACTION",
    "L8B_VERB_BAB_GOVERNANCE",
    "L9_WAZN_MATCHING",
    "L14_JAMID_MUSHTAQ",
    "L13_VERB_TRANSFORMATION",
    "L12_GENDER_NUMBER",
    "L10_SYNTAX",
    "L10B_DEEP_SYNTAX",
    "CLAUSE_ENGINE",
    "L11_I3RAB",
    "L11B_CAUSAL_I3RAB",
    "L17_RULE_BASED_I3RAB",
    "L12_SEMANTIC_RHETORICAL",
    "L12B_ANALOGICAL_REASONING",
    "L13_COGNITIVE_FUSION",
    "L13_VALIDATION",
    "L14_PRESENTATION",
]

LAYER_STATUSES = frozenset({
    "success", "partial", "skipped", "failed", "pass_through", "missing",
})


class ReusedModuleDict(TypedDict, total=False):
    file: str
    symbol: str
    mode: str  # direct | adapter | pass_through


class LayerOutputDict(TypedDict, total=False):
    layer_id: str
    layer_name: str
    stage_index: int
    status: str
    received_input: Dict[str, Any]
    reused_module: ReusedModuleDict
    rules_applied: List[str]
    gates_applied: List[Dict[str, Any]]
    transformation_result: Dict[str, Any]
    raw_module_output: Dict[str, Any]
    validation: Dict[str, Any]
    warnings: List[str]
    errors: List[str]
    next_input: Dict[str, Any]
    hypotheses: List[Dict[str, Any]]


class PipelineDict(TypedDict, total=False):
    pipeline_version: str
    request_id: str
    created_at: str
    source: Dict[str, Any]
    original_text: str
    normalized_text: Optional[str]
    metadata: Dict[str, Any]
    stage_order: List[str]
    layer_outputs: Dict[str, LayerOutputDict]
    final_validation: Dict[str, Any]
    rendered_output: Dict[str, Any]


def is_valid_layer_status(status: str) -> bool:
    return status in LAYER_STATUSES


def is_valid_stage_id(stage_id: str) -> bool:
    return stage_id in STAGE_ORDER
