# -*- coding: utf-8 -*-
"""
Structured representation of gold iʿrāb prose (Batch 28.4).

Fact fields use status: ``resolved`` | ``candidate`` | ``absent``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Tuple


@dataclass(frozen=True)
class GoldStructuredI3rab:
    """Conservative parse of one gold CSV iʿrāb cell."""

    raw_text: str
    # Grammatical word-class (lexical/surface category)
    gram_family: Optional[str]  # verb | noun | particle | pronoun | None
    gram_family_status: str  # resolved | candidate | absent
    # Canonical syntactic role (internal key, not display Arabic)
    syntactic_role: Optional[str]
    syntactic_role_status: str
    # Case / mood bucket (same vocabulary as L17 inference)
    case_bucket: Optional[str]  # nominative | accusative | genitive | jussive | built | None
    case_status: str
    # Short marker label if recoverable
    marker: Optional[str]
    marker_status: str
    parser_confidence: float
    limitations: Tuple[str, ...] = field(default_factory=tuple)
