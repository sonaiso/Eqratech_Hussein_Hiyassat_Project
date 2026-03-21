# -*- coding: utf-8 -*-
"""
Pipeline and layer output builders — Stage 2 contract shape.

Schema-aware helpers to build pipeline object and LayerOutput dicts.
"""

from __future__ import annotations

import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional

from .types import LAYER_STATUSES, STAGE_ORDER, LayerOutputDict, PipelineDict


# Default pipeline version aligned with contract
PIPELINE_VERSION = "1.0.0"


def build_empty_pipeline(
    original_text: str,
    *,
    request_id: Optional[str] = None,
    source: Optional[Dict[str, Any]] = None,
    metadata: Optional[Dict[str, Any]] = None,
) -> PipelineDict:
    """
    Build a canonical empty pipeline object (Stage 2 contract).
    layer_outputs contains the full fixed STAGE_ORDER keys with empty dicts; caller will fill them.
    """
    now = datetime.now(timezone.utc).isoformat()
    rid = request_id or f"REQ_{uuid.uuid4().hex[:8].upper()}"
    pipeline: PipelineDict = {
        "pipeline_version": PIPELINE_VERSION,
        "request_id": rid,
        "created_at": now,
        "original_text": original_text,
        "normalized_text": None,
        "stage_order": list(STAGE_ORDER),
        "layer_outputs": {sid: {} for sid in STAGE_ORDER},
    }
    if source is not None:
        pipeline["source"] = source
    if metadata is not None:
        pipeline["metadata"] = metadata
    pipeline["final_validation"] = {}
    pipeline["rendered_output"] = {}
    return pipeline


def build_layer_output(
    layer_id: str,
    layer_name: str,
    stage_index: int,
    status: str,
    *,
    received_input: Optional[Dict[str, Any]] = None,
    reused_module: Optional[Dict[str, Any]] = None,
    transformation_result: Optional[Dict[str, Any]] = None,
    raw_module_output: Optional[Dict[str, Any]] = None,
    validation: Optional[Dict[str, Any]] = None,
    warnings: Optional[List[str]] = None,
    errors: Optional[List[str]] = None,
    next_input: Optional[Dict[str, Any]] = None,
    rules_applied: Optional[List[str]] = None,
    gates_applied: Optional[List[Dict[str, Any]]] = None,
    hypotheses: Optional[List[Dict[str, Any]]] = None,
) -> LayerOutputDict:
    """
    Build a canonical LayerOutput dict (Stage 2 contract).
    Required: layer_id, layer_name, stage_index, status.
    """
    if status not in LAYER_STATUSES:
        status = "missing"
    out: LayerOutputDict = {
        "layer_id": layer_id,
        "layer_name": layer_name,
        "stage_index": stage_index,
        "status": status,
    }
    if received_input is not None:
        out["received_input"] = received_input
    if reused_module is not None:
        out["reused_module"] = reused_module
    if transformation_result is not None:
        out["transformation_result"] = transformation_result
    if raw_module_output is not None:
        out["raw_module_output"] = raw_module_output
    if validation is not None:
        out["validation"] = validation
    if warnings is not None:
        out["warnings"] = warnings
    if errors is not None:
        out["errors"] = errors
    if next_input is not None:
        out["next_input"] = next_input
    if rules_applied is not None:
        out["rules_applied"] = rules_applied
    if gates_applied is not None:
        out["gates_applied"] = gates_applied
    if hypotheses is not None:
        out["hypotheses"] = hypotheses
    return out


def get_previous_output(pipeline: PipelineDict, stage_index: int) -> Dict[str, Any]:
    """Return transformation_result or next_input of the previous stage, or empty dict."""
    if stage_index <= 0:
        return {}
    prev_id = STAGE_ORDER[stage_index - 1]
    layer_outputs = pipeline.get("layer_outputs") or {}
    prev = layer_outputs.get(prev_id) or {}
    return prev.get("next_input") or prev.get("transformation_result") or {}
