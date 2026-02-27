from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from time import perf_counter
from typing import Any, Dict, List, Optional, Tuple


class GateStatus(Enum):
    """
    Status returned by a phonological gate after processing.
    
    Attributes:
        ACCEPT: Segments pass through unchanged (no violation detected)
        REPAIR: Segments were modified to fix a violation
        REJECT: Unrecoverable error, processing must stop
    """
    ACCEPT = auto()
    REPAIR = auto()
    REJECT = auto()


@dataclass
class GateDelta:
    """
    Structured diff between input and output.

    Conservative: we keep it very light so it doesn't force
    any gate to compute heavy diffs.
    """
    changed: bool = False
    added: List[str] = field(default_factory=list)
    removed: List[str] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)


@dataclass
class GateResult:
    """
    Result of applying a phonological gate to segment sequence.
    
    Attributes:
        status: GateStatus indicating ACCEPT, REPAIR, or REJECT
        output: Modified list of segments after gate processing
        reason: Human-readable explanation of what the gate did
        deltas: List of changes made (e.g., ['sukun→fatha at position 1'])
        latency_ms: Processing time in milliseconds
    
    Example:
        >>> result = GateResult(
        ...     status=GateStatus.REPAIR,
        ...     output=['ك', 'َ', 'ت', 'ْ', 'ب'],
        ...     reason='Double sukun repaired',
        ...     deltas=['sukun→fatha at position 1'],
        ...     latency_ms=0.05
        ... )
    """
    status: GateStatus
    input_units: List[str]
    output_units: List[str]

    delta: GateDelta = field(default_factory=GateDelta)
    time_ms: float = 0.0

    notes: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)
    
    def __init__(
        self,
        status: GateStatus,
        gate_id: str = "",
        input_units: Optional[List[str]] = None,
        output_units: Optional[List[str]] = None,
        delta: Optional[GateDelta] = None,
        time_ms: float = 0.0,
        notes: Optional[List[str]] = None,
        warnings: Optional[List[str]] = None,
        errors: Optional[List[str]] = None,
        # Backward compatibility kwargs
        output: Optional[List[str]] = None,
        reason: Optional[str] = None,
        deltas: Optional[List[str]] = None,
        latency_ms: Optional[float] = None,
    ):
        """Initialize with backward compatibility for old field names"""
        self.status = status
        self.gate_id = gate_id
        
        # Handle backward compatibility
        if output is not None:
            self.output_units = output
            self.input_units = input_units or output
        else:
            self.output_units = output_units or []
            self.input_units = input_units or []
        
        # Handle delta backward compatibility
        if deltas is not None:
            self.delta = GateDelta(changed=True, notes=deltas)
        else:
            self.delta = delta or GateDelta(changed=(self.input_units != self.output_units))
        
        # Handle time backward compatibility
        if latency_ms is not None:
            self.time_ms = latency_ms
        else:
            self.time_ms = time_ms
        
        # Handle notes backward compatibility
        if reason is not None:
            self.notes = [reason] + (notes or [])
        else:
            self.notes = notes or []
        
        self.warnings = warnings or []
        self.errors = errors or []

    # -------------------------
    # Backward-compat aliases
    # -------------------------
    @property
    def output(self) -> List[str]:
        return self.output_units

    @property
    def reason(self) -> str:
        # Old code expects a single string.
        # We map to the first note if present.
        return self.notes[0] if self.notes else ""

    @property
    def deltas(self) -> List[str]:
        return self.delta.notes

    @property
    def latency_ms(self) -> float:
        return self.time_ms


class PhonologicalGate(ABC):
    """
    Abstract base class for all phonological gates.
    
    Each gate implements Tajweed-based rules for Arabic phonological processing.
    Gates examine segments and return ACCEPT (pass through), REPAIR (modify),
    or REJECT (fail).
    
    Attributes:
        gate_id: Unique identifier for this gate
    
    Example:
        >>> class MyGate(PhonologicalGate):
        ...     def __init__(self):
        ...         super().__init__("my_gate")
        ...     
        ...     def apply(self, segments: List[str]) -> GateResult:
        ...         # Implement gate logic
        ...         return GateResult(
        ...             status=GateStatus.ACCEPT,
        ...             output=segments,
        ...             reason="No violation detected"
        ...         )
    """
    def __init__(self, gate_id: str):
        """
        Initialize phonological gate.
        
        Args:
            gate_id: Unique identifier for this gate (e.g., 'sukun', 'shadda')
        """
        self.gate_id = gate_id

    @abstractmethod
    def apply(self, segments: List[str]) -> GateResult:
        """
        Apply gate logic to segment sequence.
        
        Args:
            segments: List of Arabic segments (consonants, vowels, diacritics)
        
        Returns:
            GateResult with status, modified output, and explanation
        
        Raises:
            NotImplementedError: If subclass doesn't implement this method
        """
        pass


class GateOrchestrator:
    """
    Orchestrates sequential application of phonological gates.
    
    Gates are applied in order, with each gate receiving the output of the
    previous gate. If any gate returns REJECT status, processing stops
    immediately and the current state is returned.
    
    Attributes:
        gates: Ordered list of PhonologicalGate instances
    
    Example:
        >>> from fvafk.c2a.gates import GateSukun, GateShadda, GateTanwin
        >>> 
        >>> orchestrator = GateOrchestrator([
        ...     GateSukun(),
        ...     GateShadda(),
        ...     GateTanwin()
        ... ])
        >>> 
        >>> segments = ['ك', 'َ', 'ا', 'ت', 'ِ', 'ب', 'ٌ']
        >>> output, results = orchestrator.run(segments)
        >>> 
        >>> # GateTanwin will expand ٌ → ُ + ن
        >>> print(output)
        ['ك', 'َ', 'ا', 'ت', 'ِ', 'ب', 'ُ', 'ن']
    """
    def __init__(self, gates: List[PhonologicalGate]):
        """
        Initialize gate orchestrator.
        
        Args:
            gates: List of gates in processing order
        """
        self.gates = gates

    def run(self, segments: List[str]) -> Tuple[List[str], List[GateResult]]:
        """
        Run all gates sequentially on segment sequence.
        
        Gates are applied in order. If any gate returns REJECT status,
        processing stops immediately and returns the current state.
        
        Args:
            segments: Input segment list
        
        Returns:
            Tuple of (final_segments, gate_results) where:
                - final_segments: Final segment list after all gates
                - gate_results: List of GateResult for each gate applied
        
        Example:
            >>> orchestrator = GateOrchestrator([GateSukun(), GateTanwin()])
            >>> input_segs = ['ك', 'ْ', 'ت', 'ْ', 'ب', 'ٌ']
            >>> output_segs, results = orchestrator.run(input_segs)
            >>> 
            >>> # Check results
            >>> for i, result in enumerate(results):
            ...     gate_name = orchestrator.gates[i].gate_id
            ...     print(f"{gate_name}: {result.status.name}")
            sukun: REPAIR
            tanwin: REPAIR
        """
        current = segments
        results: List[GateResult] = []

        for gate in self.gates:
            t0 = perf_counter()
            result = gate.apply(current)
            result.time_ms = (perf_counter() - t0) * 1000.0

            results.append(result)

            if result.status == GateStatus.REJECT:
                return current, results

            current = result.output_units

        return current, results


# Legacy alias for backward compatibility
PhonologicalGate = BaseGate
