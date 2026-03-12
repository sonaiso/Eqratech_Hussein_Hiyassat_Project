# -*- coding: utf-8 -*-
"""
Orchestrator — central pipeline runner and stage registry.

Stage 3: skeleton only; real adapters are connected in Stage 4.
"""

from .pipeline_orchestrator import run, run_pipeline
from .stage_registry import get_default_registry, get_stage_order
from .types import STAGE_ORDER

__all__ = [
    "run",
    "run_pipeline",
    "get_default_registry",
    "get_stage_order",
    "STAGE_ORDER",
]
