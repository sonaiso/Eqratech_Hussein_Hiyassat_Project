"""
GateWasl: validation / annotation only (no segment repair).

Authoritative ``cv`` / ``cv_advanced`` come from ``src/word-2-cv.py`` via
``word2cv_authority``; C2a must not rewrite those strings. This gate only flags
initial-cluster / initial-sukun situations that historically triggered segment
repairs, without mutating the segment stream.
"""

from __future__ import annotations

from typing import List

from ..gate_framework import GateResult, GateStatus, PhonologicalGate
from ..syllable import Segment, SegmentKind, VowelKind


class GateWasl(PhonologicalGate):
    def __init__(self) -> None:
        super().__init__(gate_id="G_WASL")

    def apply(self, segments: List[Segment]) -> GateResult:
        if len(segments) < 2:
            return GateResult(
                gate_id=self.gate_id,
                status=GateStatus.ACCEPT,
                output=list(segments),
                reason="wasl: too short",
                deltas=[],
            )

        first, second = segments[0], segments[1]
        if first.kind == SegmentKind.CONSONANT and second.kind == SegmentKind.VOWEL and second.vk == VowelKind.SUKUN:
            return GateResult(
                gate_id=self.gate_id,
                status=GateStatus.WARN,
                output=list(segments),
                reason="wasl: initial sukun noted (authoritative CV unchanged; see c1.cv_analysis)",
                deltas=["initial_sukun_noted:no_segment_repair"],
            )

        if first.kind == SegmentKind.CONSONANT and second.kind == SegmentKind.CONSONANT:
            return GateResult(
                gate_id=self.gate_id,
                status=GateStatus.WARN,
                output=list(segments),
                reason="wasl: initial consonant cluster noted (authoritative CV unchanged; see c1.cv_analysis)",
                deltas=["initial_cluster_noted:no_segment_repair"],
            )

        return GateResult(
            gate_id=self.gate_id,
            status=GateStatus.ACCEPT,
            output=list(segments),
            reason="wasl: ok",
            deltas=[],
        )
