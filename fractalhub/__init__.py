"""
FractalHub: Consciousness Kernel for Arabic NLP

A locked architecture preventing hallucination through:
- Four conditions verification (Reality/Brain/Sensing/Prior)
- Strict layer separation (C0→C1→C2→C3)
- Evidence-based reasoning with prior_ids
- Full provenance tracking
"""

__version__ = "1.2.0"
__architecture_version__ = "locked_v1"

from fractalhub.kernel import (
    Record,
    TraceEntry,
    TraceManager,
    Executor,
    Entity,
    Reasoner,
)

__all__ = [
    "Record",
    "TraceEntry",
    "TraceManager",
    "Executor",
    "Entity",
    "Reasoner",
]
