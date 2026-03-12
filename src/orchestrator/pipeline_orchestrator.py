# -*- coding: utf-8 -*-
"""
Pipeline orchestrator — central entry point.

Accepts raw text, runs stages in order, returns canonical pipeline object.
Stage 4: runs FVAFK once and uses real adapters for L1–L12.
"""

from __future__ import annotations

import logging
from typing import Any, Dict, List, Optional

from .adapters.fvafk_runner import FVAFK_RESULT_KEY, run_fvafk_once
from .builders import build_empty_pipeline
from .errors import PipelineError, StageError
from .stage_registry import get_default_registry
from .stages.base_stage import BaseStage
from .types import LayerOutputDict, PipelineDict, STAGE_ORDER

logger = logging.getLogger(__name__)


def insert_layer_output(
    pipeline: PipelineDict,
    layer_id: str,
    layer_output: LayerOutputDict,
) -> None:
    """
    Insert or update one layer output under the fixed key.
    Does not overwrite unrelated layers.
    """
    outputs = pipeline.get("layer_outputs")
    if outputs is None:
        pipeline["layer_outputs"] = {sid: {} for sid in STAGE_ORDER}
        outputs = pipeline["layer_outputs"]
    if layer_id in STAGE_ORDER:
        outputs[layer_id] = dict(layer_output)


def run_pipeline(
    text: str,
    *,
    request_id: Optional[str] = None,
    source: Optional[Dict[str, Any]] = None,
    metadata: Optional[Dict[str, Any]] = None,
    run_mode: Optional[str] = None,
    render_mode: Optional[str] = None,
    stages: Optional[List[BaseStage]] = None,
) -> PipelineDict:
    """
    Run the pipeline on raw text. Returns the canonical pipeline object.

    - text: raw input (required)
    - request_id, source, metadata: optional pipeline metadata
    - run_mode: optional (e.g. "full", "skeleton"); currently unused, for future use
    - render_mode: optional (compact | detailed | debug); L14 uses this for presentation
    - stages: optional list of stages; if None, uses default registry
    """
    pipeline = build_empty_pipeline(
        text,
        request_id=request_id,
        source=source or ({"run_mode": run_mode} if run_mode else None),
        metadata=metadata,
    )
    if render_mode is not None:
        pipeline["_render_mode"] = render_mode  # type: ignore[typeddict-unknown-key]
    # Stage 4: run FVAFK once so real adapters can read from pipeline
    try:
        fvafk_result = run_fvafk_once(text)
        pipeline[FVAFK_RESULT_KEY] = fvafk_result  # type: ignore[typeddict-unknown-key]
        if not fvafk_result.get("success", True):
            logger.warning("fvafk_run returned success=False: %s", fvafk_result.get("error", ""))
    except Exception as e:
        logger.warning("fvafk_run failed: %s", e, exc_info=True)
        pipeline[FVAFK_RESULT_KEY] = {"success": False, "error": str(e)}  # type: ignore[typeddict-unknown-key]

    registry = stages if stages is not None else get_default_registry()

    for stage in registry:
        layer_id = stage.layer_id
        logger.info("stage_started layer_id=%s layer_name=%s index=%s", layer_id, stage.layer_name, stage.stage_index)
        try:
            layer_output = stage.run(pipeline)
            status = layer_output.get("status", "missing")
            warnings = layer_output.get("warnings") or []
            errors = layer_output.get("errors") or []
            reused = layer_output.get("reused_module")
            logger.info(
                "stage_finished layer_id=%s status=%s warnings=%s errors=%s reused=%s",
                layer_id,
                status,
                len(warnings),
                len(errors),
                reused.get("symbol") if isinstance(reused, dict) else None,
            )
            insert_layer_output(pipeline, layer_id, layer_output)
            if layer_id == "L13_VALIDATION":
                tr = layer_output.get("transformation_result") or {}
                pipeline["final_validation"] = {  # type: ignore[typeddict-unknown-key]
                    "global_validity": tr.get("global_validity"),
                    "issues": tr.get("issues", []),
                    "validated_layers_summary": tr.get("validated_layers_summary", {}),
                    "final_confidence": tr.get("final_confidence"),
                }
            if layer_id == "L14_PRESENTATION":
                tr = layer_output.get("transformation_result") or {}
                pipeline["rendered_output"] = {  # type: ignore[typeddict-unknown-key]
                    "mode": tr.get("mode"),
                    "summary": tr.get("summary"),
                    "sections": tr.get("sections", []),
                    "artifacts": tr.get("artifacts", {}),
                }
        except Exception as e:
            logger.warning("stage_failed layer_id=%s error=%s", layer_id, e, exc_info=True)
            failed_output: LayerOutputDict = {
                "layer_id": layer_id,
                "layer_name": stage.layer_name,
                "stage_index": stage.stage_index,
                "status": "failed",
                "errors": [str(e)],
                "received_input": {},
            }
            insert_layer_output(pipeline, layer_id, failed_output)

    # Remove internal keys so output matches Stage 2 contract
    pipeline.pop(FVAFK_RESULT_KEY, None)
    pipeline.pop("_render_mode", None)
    return pipeline


def run(
    text: str,
    *,
    request_id: Optional[str] = None,
    source: Optional[Dict[str, Any]] = None,
    metadata: Optional[Dict[str, Any]] = None,
    output_mode: Optional[str] = None,
    render_mode: Optional[str] = None,
) -> PipelineDict:
    """
    Convenience entry point: run_pipeline with output_mode and render_mode.
    """
    return run_pipeline(
        text,
        request_id=request_id,
        source=source,
        metadata=metadata,
        run_mode=output_mode,
        render_mode=render_mode,
    )
