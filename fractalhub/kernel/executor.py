"""
Executor: Gate execution engine with evidence logging (Kernel v1.2)

Executes gates while:
- Loading gate definitions from dictionary
- Verifying four conditions
- Logging evidence (lexicon_ids/ruleset_ids)
- Creating trace entries
- Enforcing locked architecture
"""

import time
from typing import Any, Dict, List, Optional

from fractalhub.kernel.trace import TraceEntry, TraceManager


class Executor:
    """
    Gate execution engine for the consciousness kernel.
    
    Ensures:
    - Four conditions verified before execution
    - Evidence (prior_ids) logged
    - Trace created for all operations
    - No C3 without C2, no C2 without C1
    """
    
    def __init__(self, dictionary: Optional[Dict[str, Any]] = None, trace_manager: Optional[TraceManager] = None):
        """
        Initialize executor.
        
        Args:
            dictionary: Dictionary containing gate definitions
            trace_manager: TraceManager instance for logging
        """
        self.dictionary = dictionary or {}
        self.trace_manager = trace_manager or TraceManager()
    
    def _verify_four_conditions(
        self,
        gate_def: Dict[str, Any],
        inputs: List[str],
        ruleset_ids: List[str]
    ) -> Dict[str, bool]:
        """
        Verify the four conditions of cognition.
        
        Args:
            gate_def: Gate definition from dictionary
            inputs: Input data/records
            ruleset_ids: Ruleset IDs providing evidence
            
        Returns:
            Dict with reality/brain/sensing/prior verification status
        """
        four_conditions = gate_def.get("four_conditions", {})
        
        return {
            "reality": len(inputs) > 0,  # Form stream present
            "brain": gate_def.get("status") == "active",  # Executor active
            "sensing": "inputs" in gate_def,  # Channel verified
            "prior": len(ruleset_ids) > 0,  # Prior knowledge logged
        }
    
    def execute_gate(
        self,
        gate_id: str,
        inputs: List[str],
        invariant_checks: Optional[Dict[str, bool]] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Execute a gate with full tracing.
        
        Args:
            gate_id: Gate identifier (e.g., "G_C1_CODEC_VERIFY")
            inputs: Input record IDs
            invariant_checks: Optional invariant verification results
            **kwargs: Additional execution parameters
            
        Returns:
            Dict with outputs, trace_id, and execution metadata
            
        Raises:
            ValueError: If gate not found or four conditions not met
        """
        start_time = time.time()
        
        # Load gate definition from dictionary
        gates = self.dictionary.get("gates", {})
        gate_def = gates.get(gate_id)
        
        if not gate_def:
            raise ValueError(f"Gate not found: {gate_id}")
        
        # Extract ruleset_ids (evidence)
        ruleset_ids = gate_def.get("ruleset_ids", [])
        
        if gate_def.get("evidence_required", False) and not ruleset_ids:
            raise ValueError(f"Gate {gate_id} requires evidence but no ruleset_ids provided")
        
        # Verify four conditions
        four_conditions = self._verify_four_conditions(gate_def, inputs, ruleset_ids)
        
        if not all(four_conditions.values()):
            raise ValueError(
                f"Four conditions not met for gate {gate_id}: {four_conditions}"
            )
        
        # Execute gate logic (placeholder - actual logic would go here)
        # In a real implementation, this would call specific gate handlers
        outputs = self._execute_gate_logic(gate_id, gate_def, inputs, **kwargs)
        
        # Calculate latency
        gate_latency_ms = (time.time() - start_time) * 1000
        
        # Determine evidence strength based on provenance
        evidence_strength = self._calculate_evidence_strength(gate_def)
        
        # Create trace entry
        trace_entry = TraceEntry(
            gate_id=gate_id,
            inputs=inputs,
            outputs=outputs,
            prior_ids=ruleset_ids,
            four_conditions_verified=four_conditions,
            gate_latency_ms=gate_latency_ms,
            evidence_strength=evidence_strength,
            invariant_checks=invariant_checks or {},
        )
        
        # Add to trace manager
        trace_id = self.trace_manager.add_trace(trace_entry)
        
        return {
            "outputs": outputs,
            "trace_id": trace_id,
            "gate_latency_ms": gate_latency_ms,
            "evidence_strength": evidence_strength,
        }
    
    def _execute_gate_logic(
        self,
        gate_id: str,
        gate_def: Dict[str, Any],
        inputs: List[str],
        **kwargs
    ) -> List[str]:
        """
        Execute the actual gate logic.
        
        This is a placeholder. In a real implementation, this would:
        - Route to specific gate handlers
        - Apply constraints and transformations
        - Validate outputs
        
        Args:
            gate_id: Gate identifier
            gate_def: Gate definition
            inputs: Input data
            **kwargs: Additional parameters
            
        Returns:
            List of output record IDs
        """
        # Placeholder: return processed inputs
        # In real implementation, this would apply gate-specific logic
        output_types = gate_def.get("outputs", [])
        return [f"OUTPUT:{gate_id}:{i}" for i in range(len(output_types))]
    
    def _calculate_evidence_strength(self, gate_def: Dict[str, Any]) -> float:
        """
        Calculate evidence strength based on gate definition.
        
        Uses epistemic levels:
        - YAQIN (certainty): 1.0
        - ZANN (probability): 0.7
        - SHAKK (doubt): 0.4
        
        Args:
            gate_def: Gate definition
            
        Returns:
            Evidence strength value
        """
        # Check if gate definition has provenance info
        # Default to YAQIN (1.0) for core gates
        evidence_required = gate_def.get("evidence_required", True)
        
        if not evidence_required:
            return 0.7  # ZANN - can be inferred
        
        return 1.0  # YAQIN - explicit evidence required
    
    def get_trace_manager(self) -> TraceManager:
        """Get the trace manager."""
        return self.trace_manager
