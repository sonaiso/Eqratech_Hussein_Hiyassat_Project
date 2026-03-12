# -*- coding: utf-8 -*-
"""
Lightweight schema-aware checks — Stage 2 contract discipline.

Does not perform full JSON Schema validation; checks required keys and fixed stage IDs.
Full schema validation can be added later or deferred.
"""

from __future__ import annotations

from typing import Any, Dict, List, Tuple

from .types import LAYER_STATUSES, STAGE_ORDER

# Required top-level keys (pipeline.schema.json)
PIPELINE_REQUIRED_KEYS = frozenset({
    "pipeline_version", "request_id", "created_at", "original_text",
    "stage_order", "layer_outputs",
})

# Required keys per layer output (layer_output.schema.json)
LAYER_OUTPUT_REQUIRED_KEYS = frozenset({"layer_id", "layer_name", "stage_index", "status"})


def validate_pipeline_shape(pipeline: Dict[str, Any]) -> Tuple[bool, List[str]]:
    """
    Lightweight check: pipeline has required keys and layer_outputs has all fixed stage keys.
    Returns (ok, list of issue messages).
    """
    issues: List[str] = []
    for key in PIPELINE_REQUIRED_KEYS:
        if key not in pipeline:
            issues.append(f"pipeline missing required key: {key}")
    if "layer_outputs" in pipeline:
        lo = pipeline["layer_outputs"]
        if not isinstance(lo, dict):
            issues.append("layer_outputs must be an object")
        else:
            for sid in STAGE_ORDER:
                if sid not in lo:
                    issues.append(f"layer_outputs missing stage key: {sid}")
    if "stage_order" in pipeline:
        so = pipeline["stage_order"]
        if list(so) != list(STAGE_ORDER):
            issues.append("stage_order must match fixed STAGE_ORDER")
    return (len(issues) == 0, issues)


def validate_layer_output_shape(layer_output: Dict[str, Any]) -> Tuple[bool, List[str]]:
    """
    Lightweight check: layer output has required keys and valid status.
    Returns (ok, list of issue messages).
    """
    issues: List[str] = []
    for key in LAYER_OUTPUT_REQUIRED_KEYS:
        if key not in layer_output:
            issues.append(f"layer_output missing required key: {key}")
    if "status" in layer_output and layer_output["status"] not in LAYER_STATUSES:
        issues.append(f"invalid status: {layer_output['status']}")
    if "layer_id" in layer_output and layer_output["layer_id"] not in STAGE_ORDER:
        issues.append(f"invalid layer_id: {layer_output['layer_id']}")
    return (len(issues) == 0, issues)
