from .syllable import Segment, SegmentKind, Syllable, SyllableType
from .gates import (
    GateDeletion,
    GateEpenthesis,
    GateHamza,
    GateIdgham,
    GateMadd,
    GateShadda,
    GateSukun,
    GateWaqf,
)
from .gate_framework import GateOrchestrator

GateFramework = GateOrchestrator

__all__ = [
    "Segment",
    "SegmentKind",
    "Syllable",
    "SyllableType",
    "GateDeletion",
    "GateEpenthesis",
    "GateHamza",
    "GateIdgham",
    "GateMadd",
    "GateShadda",
    "GateSukun",
    "GateWaqf",
    "GateFramework",
]
