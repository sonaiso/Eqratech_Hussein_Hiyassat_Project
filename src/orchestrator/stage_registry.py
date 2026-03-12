# -*- coding: utf-8 -*-
"""
Stage registry — all 15 fixed stages in deterministic order.

Stage 4: L1–L12 real adapters. Stage 6: L13 real validation. L0, L14 placeholder.
"""

from __future__ import annotations

from typing import List, Optional

from .l13_validation import RealL13Validation
from .stages.base_stage import BaseStage
from .stages.placeholders import (
    make_l0_input_stage,
    make_placeholder_stage,
)
from .stages.real_stages import get_real_stages_l1_l12
from .types import STAGE_ORDER


def get_default_registry() -> List[BaseStage]:
    """
    Return the list of stages in fixed order. Every stage ID appears exactly once.
    L0: placeholder. L1–L12: real adapters. L13: real validation. L14: placeholder.
    """
    stages: List[BaseStage] = []
    stages.append(make_l0_input_stage())
    stages.extend(get_real_stages_l1_l12())
    stages.append(RealL13Validation())
    stages.append(make_placeholder_stage("L14_PRESENTATION", 14, status="pass_through"))
    return stages


def get_stage_by_id(stage_id: str, registry: Optional[List[BaseStage]] = None) -> Optional[BaseStage]:
    """Return the stage with the given layer_id, or None."""
    reg = registry or get_default_registry()
    for s in reg:
        if s.layer_id == stage_id:
            return s
    return None


def get_stage_order() -> List[str]:
    """Return the fixed stage order (same as STAGE_ORDER)."""
    return list(STAGE_ORDER)
