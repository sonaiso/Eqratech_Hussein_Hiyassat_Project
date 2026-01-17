"""
Reasoning: Evidence-based reasoning with prior_ids enforcement (Kernel v1.2)

Reasoner: Implements reasoning modes with strict evidence requirements:
- Deductive: Logical inference from premises
- Inductive: Pattern generalization
- Abductive: Best explanation inference
- Inferential: General inference

Core principle: NO REASONING WITHOUT EVIDENCE
"""

from typing import Any, Dict, List, Optional

from fractalhub.kernel.trace import TraceEntry, TraceManager


class Reasoner:
    """
    Evidence-based reasoning engine.
    
    Enforces:
    - All premises must have prior_ids (evidence)
    - Reasoning mode must be specified
    - Epistemic strength tracked
    - Full reasoning trace created
    """
    
    # Epistemic strength by mode
    MODE_STRENGTH = {
        "deductive": 1.0,  # Certainty (if premises are certain)
        "inductive": 0.7,  # Probability
        "abductive": 0.7,  # Probability
        "inferential": 0.4,  # Doubt
    }
    
    def __init__(self, trace_manager: Optional[TraceManager] = None):
        """
        Initialize reasoner.
        
        Args:
            trace_manager: TraceManager for logging reasoning traces
        """
        self.trace_manager = trace_manager or TraceManager()
    
    def reason(
        self,
        premises: List[Dict[str, Any]],
        mode: str = "deductive",
        conclusion_template: Optional[Dict[str, Any]] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Perform reasoning with evidence tracking.
        
        Args:
            premises: List of premise dicts, each must have 'prior_ids'
            mode: Reasoning mode (deductive/inductive/abductive/inferential)
            conclusion_template: Optional template for expected conclusion
            **kwargs: Additional reasoning parameters
            
        Returns:
            Dict with conclusion, evidence_chain, epistemic_strength, trace_id
            
        Raises:
            ValueError: If premises lack evidence or mode is invalid
        """
        # Validate mode
        if mode not in self.MODE_STRENGTH:
            raise ValueError(
                f"Invalid reasoning mode: {mode}. "
                f"Must be one of: {list(self.MODE_STRENGTH.keys())}"
            )
        
        # CRITICAL: Verify all premises have evidence
        if not premises:
            raise ValueError("Cannot reason without premises")
        
        for i, premise in enumerate(premises):
            if "prior_ids" not in premise or not premise["prior_ids"]:
                raise ValueError(
                    f"Cannot reason without evidence. "
                    f"Premise {i} lacks prior_ids: {premise}"
                )
        
        # Collect all prior_ids for evidence chain
        all_prior_ids = []
        for premise in premises:
            all_prior_ids.extend(premise["prior_ids"])
        
        # Deduplicate while preserving order
        evidence_chain = list(dict.fromkeys(all_prior_ids))
        
        # Calculate epistemic strength
        base_strength = self.MODE_STRENGTH[mode]
        
        # Adjust based on premise strength
        if "epistemic_strength" in kwargs:
            premise_strength = kwargs["epistemic_strength"]
            epistemic_strength = min(base_strength, premise_strength)
        else:
            epistemic_strength = base_strength
        
        # Perform reasoning (placeholder - actual logic would go here)
        conclusion = self._apply_reasoning_logic(
            premises, mode, conclusion_template, **kwargs
        )
        
        # Create reasoning trace
        gate_id = f"G_REASONING_{mode.upper()}"
        
        trace_entry = TraceEntry(
            gate_id=gate_id,
            inputs=[p.get("id", f"PREMISE_{i}") for i, p in enumerate(premises)],
            outputs=[conclusion.get("id", "CONCLUSION")],
            prior_ids=evidence_chain,
            four_conditions_verified={
                "reality": True,  # Premises present
                "brain": True,  # Reasoner active
                "sensing": True,  # Logical channel verified
                "prior": len(evidence_chain) > 0,  # Evidence present
            },
            gate_latency_ms=0.0,  # Would be measured in real implementation
            evidence_strength=epistemic_strength,
            invariant_checks={},  # Would check logical invariants
        )
        
        # Add to trace manager
        trace_id = self.trace_manager.add_trace(trace_entry)
        
        return {
            "conclusion": conclusion,
            "evidence_chain": evidence_chain,
            "epistemic_strength": epistemic_strength,
            "reasoning_mode": mode,
            "trace_id": trace_id,
        }
    
    def _apply_reasoning_logic(
        self,
        premises: List[Dict[str, Any]],
        mode: str,
        conclusion_template: Optional[Dict[str, Any]],
        **kwargs
    ) -> Dict[str, Any]:
        """
        Apply reasoning logic based on mode.
        
        This is a placeholder. Real implementation would:
        - For deductive: Apply logical rules
        - For inductive: Generalize patterns
        - For abductive: Find best explanation
        - For inferential: General inference
        
        Args:
            premises: Input premises
            mode: Reasoning mode
            conclusion_template: Expected conclusion structure
            **kwargs: Additional parameters
            
        Returns:
            Conclusion dictionary
        """
        # Placeholder: combine premise content
        conclusion = {
            "id": "CONCLUSION",
            "mode": mode,
            "derived_from": [p.get("id", f"P{i}") for i, p in enumerate(premises)],
            "content": f"Conclusion from {len(premises)} premises via {mode} reasoning",
        }
        
        if conclusion_template:
            conclusion.update(conclusion_template)
        
        return conclusion
    
    def get_trace_manager(self) -> TraceManager:
        """Get the trace manager."""
        return self.trace_manager
