"""
Consciousness Kernel v1.2 - Core Components

Implements the locked architecture with:
- Record: Base data structure with version metadata
- TraceEntry: Enhanced trace with four conditions verification
- TraceManager: Trace chain management
- Executor: Gate execution with evidence logging
- Entity: Signified layer with provenance
- Reasoner: Evidence-based reasoning
"""

from fractalhub.kernel.record import Record
from fractalhub.kernel.trace import TraceEntry, TraceManager
from fractalhub.kernel.executor import Executor
from fractalhub.kernel.signified import Entity
from fractalhub.kernel.reasoning import Reasoner

__all__ = [
    "Record",
    "TraceEntry",
    "TraceManager",
    "Executor",
    "Entity",
    "Reasoner",
]
