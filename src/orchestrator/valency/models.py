# -*- coding: utf-8 -*-
"""
Valency frame data model for L8C — Valency Matrix Seed Layer.
Semantic governance metadata only; no syntax or iʿrāb.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

# Confidence policy
CONF_EXACT_KB = 0.90
CONF_WEAK_PATTERN = 0.55
CONF_UNKNOWN = 0.20


@dataclass(frozen=False)
class ValencyFrame:
    """Single valency frame from seed KB or unknown placeholder."""
    root: str
    valency_class: str
    required_roles: List[str]
    optional_roles: List[str]
    source: str
    confidence: float

    def to_dict(self) -> dict:
        return {
            "root": self.root,
            "valency_class": self.valency_class,
            "required_roles": list(self.required_roles),
            "optional_roles": list(self.optional_roles),
            "source": self.source,
            "confidence": self.confidence,
        }
