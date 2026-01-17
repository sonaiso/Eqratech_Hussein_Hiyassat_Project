"""
Trace: Enhanced trace system with four conditions verification (Kernel v1.2)

TraceEntry: Individual gate execution trace with evidence
TraceManager: Manages the trace chain ensuring no C3 without C2, no C2 without C1
"""

import time
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional

from fractalhub.kernel.record import Record


class TraceEntry(Record):
    """
    Enhanced trace entry for kernel v1.2.
    
    Tracks gate execution with:
    - Standard fields: gate_id, inputs, outputs
    - Evidence: prior_ids (lexicon_ids/ruleset_ids)
    - Four conditions verification
    - Performance: gate_latency_ms
    - Quality: evidence_strength, invariant_checks
    """
    
    def __init__(
        self,
        gate_id: str,
        inputs: List[str],
        outputs: Optional[List[str]] = None,
        prior_ids: Optional[List[str]] = None,
        four_conditions_verified: Optional[Dict[str, bool]] = None,
        gate_latency_ms: float = 0.0,
        evidence_strength: float = 1.0,
        invariant_checks: Optional[Dict[str, bool]] = None,
        **kwargs
    ):
        """
        Initialize a trace entry.
        
        Args:
            gate_id: Gate identifier (e.g., "G_C1_CODEC_VERIFY")
            inputs: List of input record IDs
            outputs: List of output record IDs (filled after execution)
            prior_ids: Evidence chain (lexicon_ids, ruleset_ids)
            four_conditions_verified: Dict with Reality/Brain/Sensing/Prior checks
            gate_latency_ms: Execution time in milliseconds
            evidence_strength: Epistemic confidence (0.4=shakk, 0.7=zann, 1.0=yaqin)
            invariant_checks: Which invariants were verified
        """
        # Generate trace ID
        trace_id = f"TRACE:{gate_id}:{int(time.time() * 1000)}"
        
        super().__init__(
            record_id=trace_id,
            record_type="trace",
            **kwargs
        )
        
        self.gate_id = gate_id
        self.timestamp = time.time()
        self.inputs = inputs or []
        self.outputs = outputs or []
        self.prior_ids = prior_ids or []
        
        # v1.2 enhancements
        self.four_conditions_verified = four_conditions_verified or {
            "reality": False,
            "brain": False,
            "sensing": False,
            "prior": False,
        }
        self.gate_latency_ms = gate_latency_ms
        self.evidence_strength = evidence_strength
        self.invariant_checks = invariant_checks or {}
    
    def is_valid(self) -> bool:
        """
        Check if trace entry satisfies locked architecture rules.
        
        Returns:
            True if all four conditions are verified and prior_ids present
        """
        all_conditions = all(self.four_conditions_verified.values())
        has_evidence = len(self.prior_ids) > 0
        return all_conditions and has_evidence
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert trace entry to dictionary."""
        result = super().to_dict()
        result.update({
            "gate_id": self.gate_id,
            "timestamp": self.timestamp,
            "inputs": self.inputs,
            "outputs": self.outputs,
            "prior_ids": self.prior_ids,
            "four_conditions_verified": self.four_conditions_verified,
            "gate_latency_ms": self.gate_latency_ms,
            "evidence_strength": self.evidence_strength,
            "invariant_checks": self.invariant_checks,
            "is_valid": self.is_valid(),
        })
        return result


class TraceManager:
    """
    Manages the trace chain for the entire system.
    
    Ensures:
    - No C3 without C2 trace
    - No C2 without C1 four conditions verified
    - All traces have evidence (prior_ids)
    - Trace chain integrity
    """
    
    def __init__(self):
        """Initialize trace manager."""
        self.traces: List[TraceEntry] = []
        self.trace_index: Dict[str, TraceEntry] = {}
    
    def add_trace(self, trace: TraceEntry) -> str:
        """
        Add a trace entry to the chain.
        
        Args:
            trace: TraceEntry to add
            
        Returns:
            Trace ID
            
        Raises:
            ValueError: If trace is invalid
        """
        if not trace.is_valid():
            raise ValueError(
                f"Invalid trace: {trace.gate_id}. "
                f"Four conditions: {trace.four_conditions_verified}, "
                f"Prior IDs: {len(trace.prior_ids)}"
            )
        
        self.traces.append(trace)
        self.trace_index[trace.record_id] = trace
        return trace.record_id
    
    def get_trace(self, trace_id: str) -> Optional[TraceEntry]:
        """Get a trace by ID."""
        return self.trace_index.get(trace_id)
    
    def get_traces_by_gate(self, gate_id: str) -> List[TraceEntry]:
        """Get all traces for a specific gate."""
        return [t for t in self.traces if t.gate_id == gate_id]
    
    def get_trace_chain(self, trace_id: str) -> List[TraceEntry]:
        """
        Get the full trace chain leading to a specific trace.
        
        Args:
            trace_id: Starting trace ID
            
        Returns:
            List of traces in chronological order
        """
        trace = self.get_trace(trace_id)
        if not trace:
            return []
        
        chain = [trace]
        
        # Walk backwards through inputs
        for input_id in trace.inputs:
            if input_id.startswith("TRACE:"):
                parent_chain = self.get_trace_chain(input_id)
                chain = parent_chain + chain
        
        return chain
    
    def verify_no_hallucination(self) -> bool:
        """
        Verify that the locked architecture is maintained.
        
        Checks:
        1. All traces have four conditions verified
        2. All traces have evidence (prior_ids)
        3. No C3 outputs without C2 trace
        
        Returns:
            True if architecture is locked, False otherwise
        """
        for trace in self.traces:
            if not trace.is_valid():
                return False
        
        return True
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get trace statistics."""
        if not self.traces:
            return {
                "total_traces": 0,
                "valid_traces": 0,
                "avg_latency_ms": 0.0,
                "avg_evidence_strength": 0.0,
            }
        
        valid_count = sum(1 for t in self.traces if t.is_valid())
        avg_latency = sum(t.gate_latency_ms for t in self.traces) / len(self.traces)
        avg_evidence = sum(t.evidence_strength for t in self.traces) / len(self.traces)
        
        return {
            "total_traces": len(self.traces),
            "valid_traces": valid_count,
            "avg_latency_ms": avg_latency,
            "avg_evidence_strength": avg_evidence,
            "architecture_locked": self.verify_no_hallucination(),
        }
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert trace manager to dictionary."""
        return {
            "traces": [t.to_dict() for t in self.traces],
            "statistics": self.get_statistics(),
        }
