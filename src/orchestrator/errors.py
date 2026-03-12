# -*- coding: utf-8 -*-
"""
Orchestrator errors — minimal; no analyzer logic.
"""

from __future__ import annotations


class PipelineError(Exception):
    """Raised when pipeline-level execution fails."""
    pass


class StageError(Exception):
    """Raised when a stage fails (e.g. invalid input); carries stage_id."""
    def __init__(self, message: str, stage_id: str = ""):
        super().__init__(message)
        self.stage_id = stage_id
