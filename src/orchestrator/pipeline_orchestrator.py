# -*- coding: utf-8 -*-
"""
Pipeline orchestrator — central entry point.

READ docs/architecture/PIPELINE_MASTER_MEMORY.md BEFORE ANY MAJOR CHANGE.

Accepts raw text, runs stages in order, returns canonical pipeline object.
Stage 4: runs FVAFK once and uses real adapters for L1–L12.
"""

from __future__ import annotations

import logging
import time
from typing import Any, Dict, List, Optional

from .adapters.fvafk_runner import FVAFK_RESULT_KEY, run_fvafk_once
from .builders import build_empty_pipeline
from .errors import PipelineError, StageError
from .l14_presentation import augment_rendered_output_with_profiling
from .profiling import build_profiling_summary
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
    profile: bool = False,
    stages: Optional[List[BaseStage]] = None,
) -> PipelineDict:
    """
    Run the pipeline on raw text. Returns the canonical pipeline object.

    - text: raw input (required)
    - request_id, source, metadata: optional pipeline metadata
    - run_mode: optional (e.g. "full", "skeleton"); currently unused, for future use
    - render_mode: optional (compact | detailed | debug); L14 uses this for presentation
    - profile: if True, collect per-stage timing and set pipeline["profiling"]
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
    profile_records: List[Dict[str, Any]] = []

    for stage in registry:
        layer_id = stage.layer_id
        # Pre-Stage-13 audit: run before L13 Cognitive Fusion, set readiness and fusion mode
        if layer_id == "L13_COGNITIVE_FUSION":
            try:
                from .pre_stage13_audit import PreStage13ReadinessAudit
                audit = PreStage13ReadinessAudit().run_audit(pipeline)
                pipeline["pre_stage13_audit"] = audit  # type: ignore[typeddict-unknown-key]
                if "meta" not in pipeline:
                    pipeline["meta"] = {}  # type: ignore[typeddict-unknown-key]
                pipeline["meta"]["fusion_readiness"] = audit["readiness_band"]  # type: ignore[typeddict-unknown-key]
                if audit["readiness_band"] == "LOW":
                    pipeline["meta"]["conservative_fusion_mode"] = True  # type: ignore[typeddict-unknown-key]
            except Exception as e:
                logger.warning("pre_stage13_audit failed: %s", e, exc_info=True)
                pipeline["pre_stage13_audit"] = {  # type: ignore[typeddict-unknown-key]
                    "readiness_score": 0.0,
                    "readiness_band": "LOW",
                    "sources": [],
                    "blocking_issues": ["audit failed"],
                    "advisory_notes": [],
                }
                if "meta" not in pipeline:
                    pipeline["meta"] = {}  # type: ignore[typeddict-unknown-key]
                pipeline["meta"]["fusion_readiness"] = "LOW"  # type: ignore[typeddict-unknown-key]
                pipeline["meta"]["conservative_fusion_mode"] = True  # type: ignore[typeddict-unknown-key]
        t0 = time.perf_counter() if profile else None
        logger.info("stage_started layer_id=%s layer_name=%s index=%s", layer_id, stage.layer_name, stage.stage_index)
        try:
            layer_output = stage.run(pipeline)
            t1 = time.perf_counter() if profile else None
            status = layer_output.get("status", "missing")
            warnings_count = len(layer_output.get("warnings") or [])
            errors_count = len(layer_output.get("errors") or [])
            if profile and t0 is not None and t1 is not None:
                profile_records.append({
                    "layer_id": layer_id,
                    "elapsed_ms": (t1 - t0) * 1000,
                    "status": status,
                    "warnings_count": warnings_count,
                    "errors_count": errors_count,
                })
            reused = layer_output.get("reused_module")
            logger.info(
                "stage_finished layer_id=%s status=%s warnings=%s errors=%s reused=%s",
                layer_id,
                status,
                warnings_count,
                errors_count,
                reused.get("symbol") if isinstance(reused, dict) else None,
            )
            insert_layer_output(pipeline, layer_id, layer_output)
            # SEMANTIC_ROLE_PROJECTION: additive enrichment after L11B (read-only from L8B, L10B, L11B)
            if layer_id == "L11B_CAUSAL_I3RAB":
                try:
                    from .semantic_roles import project_semantic_roles
                    lo = pipeline.get("layer_outputs") or {}
                    result = project_semantic_roles(lo)
                    if result is not None:
                        lo["SEMANTIC_ROLE_PROJECTION"] = result
                except Exception as e:
                    logger.debug("semantic_role_projection skipped: %s", e)
            # DISCOURSE_FRAME_BUILDER: additive enrichment after L12B (connectives, L10B clause, L12/L12B)
            if layer_id == "L12B_ANALOGICAL_REASONING":
                try:
                    from .discourse_frame import build_discourse_frames
                    lo = pipeline.get("layer_outputs") or {}
                    result = build_discourse_frames(lo)
                    if result is not None:
                        lo["DISCOURSE_FRAME_BUILDER"] = result
                except Exception as e:
                    logger.debug("discourse_frame_builder skipped: %s", e)
            if layer_id == "L13_COGNITIVE_FUSION":
                tr = layer_output.get("transformation_result") or {}
                pipeline["cognitive_fusion"] = {  # type: ignore[typeddict-unknown-key]
                    "fusion_mode": tr.get("fusion_mode"),
                    "token_states": tr.get("token_states", []),
                    "global_confidence": tr.get("global_confidence"),
                    "tokens_high_confidence": tr.get("tokens_high_confidence", 0),
                    "tokens_low_confidence": tr.get("tokens_low_confidence", 0),
                    "unresolved_ambiguities": tr.get("unresolved_ambiguities", 0),
                }
                try:
                    from .post_stage13_audit import PostStage13FusionAudit
                    pipeline["post_stage13_audit"] = PostStage13FusionAudit().run_audit(pipeline)  # type: ignore[typeddict-unknown-key]
                except Exception as audit_err:
                    logger.warning("post_stage13_audit failed: %s", audit_err, exc_info=True)
                    pipeline["post_stage13_audit"] = {  # type: ignore[typeddict-unknown-key]
                        "fusion_consistency": "low",
                        "resolved_conflicts": 0,
                        "remaining_ambiguities": 0,
                        "issues": [{"code": "AUDIT_FAILED", "message": str(audit_err), "severity": "error"}],
                        "advisory_notes": ["Post-fusion audit crashed; result unavailable."],
                        "source_alignment": {"strong_sources_respected": False, "weak_source_overreach": True},
                    }
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
            t1 = time.perf_counter() if profile else None
            if profile and t0 is not None and t1 is not None:
                profile_records.append({
                    "layer_id": layer_id,
                    "elapsed_ms": (t1 - t0) * 1000,
                    "status": "failed",
                    "warnings_count": 0,
                    "errors_count": 1,
                })
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

    if profile and profile_records:
        pipeline["profiling"] = build_profiling_summary(profile_records)  # type: ignore[typeddict-unknown-key]
        augment_rendered_output_with_profiling(pipeline)

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
    profile: bool = False,
) -> PipelineDict:
    """
    Convenience entry point: run_pipeline with output_mode, render_mode, and profile.
    """
    return run_pipeline(
        text,
        request_id=request_id,
        source=source,
        metadata=metadata,
        run_mode=output_mode,
        render_mode=render_mode,
        profile=profile,
    )
