"""
Gate Framework for C2a Phonological Layer

Enhanced for Sprint 2, Task 2.1.1: Canonical GateResult structure
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Tuple, Optional


class GateStatus(Enum):
    """Gate execution status"""
    ACCEPT = auto()
    REPAIR = auto()
    REJECT = auto()


@dataclass
class GateResult:
    """
    Canonical GateResult structure (Sprint 2, Task 2.1.1)
    
    Standardized with input/output for before/after comparison.
    All gates must use this structure.
    """
    status: GateStatus
    output: List
    reason: str
    deltas: List[str] = field(default_factory=list)
    latency_ms: float = 0.0
    input: Optional[List] = None  # NEW: for before/after comparison
    notes: Optional[str] = None  # NEW: additional info


class PhonologicalGate(ABC):
    """Base class for all phonological gates"""
    
    def __init__(self, gate_id: str):
        self.gate_id = gate_id
    
    @abstractmethod
    def apply(self, segments: List) -> GateResult:
        """Apply gate transformation"""
        pass


class GateOrchestrator:
    """Orchestrates execution of multiple gates"""
    
    def __init__(self, gates: List[PhonologicalGate]):
        self.gates = gates
    
    def run(self, segments: List) -> Tuple[List, List[GateResult]]:
        current = segments
        results: List[GateResult] = []
        for gate in self.gates:
            result = gate.apply(current)
            results.append(result)
            if result.status == GateStatus.REJECT:
                return current, results
            current = result.output
        return current, results
