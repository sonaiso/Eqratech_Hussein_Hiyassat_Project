# -*- coding: utf-8 -*-
"""Rhetoric Signals V1 — data types."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List


@dataclass
class RhetoricSignal:
    """A single rhetoric signal detected in a sentence."""

    type: str
    label_ar: str
    trigger: str
    span: Dict[str, int]
    confidence: float
    evidence: List[str]
