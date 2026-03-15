# -*- coding: utf-8 -*-
"""
Discourse frame builder — additive layer.
Builds structurally grounded discourse frames from connectives, L10B clause hints, L12/L12B.
Does not modify syntax, i'rab, or validation. Non-blocking, heuristic, confidence-agnostic to pipeline core.
"""

from .builder import build_discourse_frames

__all__ = ["build_discourse_frames"]
