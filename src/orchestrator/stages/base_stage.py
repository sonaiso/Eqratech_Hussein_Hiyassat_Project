# -*- coding: utf-8 -*-
"""
Base stage interface — uniform contract for all pipeline stages.

Each stage: layer_id, layer_name, stage_index, run(pipeline) -> LayerOutput dict.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, Dict

from ..types import LayerOutputDict, PipelineDict, STAGE_ORDER


class BaseStage(ABC):
    """
    Uniform stage interface. Stages must not write outside their own key;
    they return a LayerOutput dict for the orchestrator to insert.
    """

    def __init__(self, layer_id: str, layer_name: str, stage_index: int):
        if layer_id not in STAGE_ORDER:
            raise ValueError(f"Invalid layer_id: {layer_id}")
        self.layer_id = layer_id
        self.layer_name = layer_name
        self.stage_index = stage_index

    @abstractmethod
    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        """
        Run this stage. Inspect pipeline (e.g. previous layer_outputs) as needed.
        Return a single LayerOutput dict; do not mutate pipeline.
        """
        pass

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.layer_id!r}, index={self.stage_index})"
