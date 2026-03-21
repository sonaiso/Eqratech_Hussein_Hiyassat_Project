# -*- coding: utf-8 -*-
"""
Stage registry — fixed deterministic pipeline order.

L1–L12 real adapters also include L14_JAMID_MUSHTAQ and L13_VERB_TRANSFORMATION
before L12_GENDER_NUMBER. L13 cognitive fusion / validation and L14 presentation
remain separate real stages.
"""

from __future__ import annotations

from typing import List, Optional

from .l12b_analogical_reasoning import RealL12BAnalogicalReasoning
from .l13_cognitive_fusion import RealL13CognitiveFusion
from .l13_validation import RealL13Validation
from .l14_presentation import RealL14Presentation
from .stages.base_stage import BaseStage
from .stages.placeholders import make_l0_input_stage
from .stages.real_stages import get_real_stages_l1_l12
from .types import STAGE_ORDER


def get_default_registry() -> List[BaseStage]:
    """
    Return the list of stages in fixed order. Every stage ID appears exactly once.
    L0: placeholder. Morphology/syntax/i'rab stages use real adapters. L12B:
    analogical reasoning. L13: cognitive fusion + validation. L14: presentation.
    """
    stages: List[BaseStage] = []
    stages.append(make_l0_input_stage())
    stages.extend(get_real_stages_l1_l12())
    stages.append(RealL12BAnalogicalReasoning())
    stages.append(RealL13CognitiveFusion())
    stages.append(RealL13Validation())
    stages.append(RealL14Presentation())
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
