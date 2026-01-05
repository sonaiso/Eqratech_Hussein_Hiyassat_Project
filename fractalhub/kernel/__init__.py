"""
Fractal Consciousness Kernel v1.1

A programmable kernel implementing C1-C2-C3 architecture with:
- C1: Signifier layer (form/phonemes/diacritics)
- C2: Trace layer (gate processing with evidence)
- C3: Signified layer (meaning graph)

Based on النبهاني's theory: reality + brain + sensing + prior_knowledge

Author: Eqratech Arabic Diana Project
Version: 1.1.0
License: MIT
"""

from .record import Record
from .codec import FormCodec, MeaningCodec
from .gates import Gate, GateRegistry
from .trace import TraceEntry, C2Trace
from .graph import SignifierGraph, SignifiedGraph
from .speech_acts import (
    SpeechAct, SpeechActType, SpeechActClassifier,
    KhabarSubtype, TalabSubtype, IstifhamSubtype,
    Ta3ajjubSubtype, TamanniSubtype, TarajjiSubtype
)

__version__ = "1.1.0"
__all__ = [
    "Record",
    "FormCodec",
    "MeaningCodec", 
    "Gate",
    "GateRegistry",
    "TraceEntry",
    "C2Trace",
    "SignifierGraph",
    "SignifiedGraph",
    "SpeechAct",
    "SpeechActType",
    "SpeechActClassifier",
    "KhabarSubtype",
    "TalabSubtype",
    "IstifhamSubtype",
    "Ta3ajjubSubtype",
    "TamanniSubtype",
    "TarajjiSubtype",
]
