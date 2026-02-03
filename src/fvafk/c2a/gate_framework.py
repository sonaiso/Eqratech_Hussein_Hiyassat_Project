from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Tuple


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
    output: List[str]
    reason: str
    deltas: List[str] = field(default_factory=list)
    latency_ms: float = 0.0


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
            result = gate.apply(current)
            results.append(result)
            if result.status == GateStatus.REJECT:
                return current, results
            current = result.output
        return current, results
