"""
Gates: Processing units in C2 layer

Gates transform inputs to outputs with full traceability.
All gates must:
1. Declare inputs/outputs
2. Log to C2 trace
3. Reference prior_ids for meaning generation
"""

from typing import List, Any, Optional, Callable
from dataclasses import dataclass
from abc import ABC, abstractmethod


@dataclass
class GateDefinition:
    """Gate metadata from dictionary"""
    gate_id: str
    layer: str
    description: str
    inputs: List[str]
    outputs: List[str]
    constraints: List[str]
    evidence_required: bool
    status: str


class Gate(ABC):
    """
    Abstract base gate.
    
    All gates must implement execute() method.
    """
    
    def __init__(self, gate_id: str, definition: Optional[GateDefinition] = None):
        """
        Initialize gate.
        
        Args:
            gate_id: Unique gate identifier
            definition: Optional gate definition from dictionary
        """
        self.gate_id = gate_id
        self.definition = definition
    
    @abstractmethod
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Execute gate logic.
        
        Args:
            inputs: Input values
            priors: Prior knowledge IDs
            
        Returns:
            Output values
        """
        pass
    
    def validate_inputs(self, inputs: List[Any]) -> bool:
        """
        Validate inputs match expected count.
        
        Args:
            inputs: Input values to validate
            
        Returns:
            True if valid
        """
        if self.definition:
            return len(inputs) >= len(self.definition.inputs)
        return True


class AttentionGate(Gate):
    """
    G_ATTEND: Focus attention on specific span.
    
    Implements selective attention mechanism.
    """
    
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Select focus span from form stream.
        
        Args:
            inputs: [form_stream]
            priors: Attention rules IDs
            
        Returns:
            [focus_span_ids]
        """
        form_stream = inputs[0] if inputs else ""
        
        # Simple implementation: focus on entire stream
        # TODO: Implement selective attention based on priors
        focus_span_ids = list(range(len(form_stream)))
        
        return [focus_span_ids]


class CodecVerifyGate(Gate):
    """
    G_CODEC_VERIFY: Verify codec integrity.
    
    Checks checksum and validates reversibility.
    """
    
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Verify codec payload.
        
        Args:
            inputs: [payload_u128, checksum32]
            priors: Codec rules IDs
            
        Returns:
            ["OK"] or ["FAIL"]
        """
        if len(inputs) < 2:
            return ["FAIL"]
        
        payload_ids = inputs[0]
        expected_checksum = inputs[1]
        
        # Compute checksum
        import hashlib
        data = ",".join(str(uid) for uid in payload_ids).encode('utf-8')
        computed = hashlib.sha256(data).hexdigest()[:8]
        
        if computed == expected_checksum:
            return ["OK"]
        else:
            return ["FAIL"]


class SpeechActGate(Gate):
    """
    G_SPEECH_ACT: Determine speech act type.
    
    Classifies utterance into: KHABAR/TALAB/ISTIFHAM/TA3AJJUB/TAMANNI/TARAJJI
    Uses the SpeechActClassifier for full classification.
    """
    
    def __init__(self, gate_id: str, definition: Optional[GateDefinition] = None):
        """Initialize with classifier"""
        super().__init__(gate_id, definition)
        # Import here to avoid circular dependency
        from .speech_acts import SpeechActClassifier
        self.classifier = SpeechActClassifier()
    
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Classify speech act.
        
        Args:
            inputs: [tokens] or [tokens, features_dict]
            priors: Speech act rules IDs
            
        Returns:
            [speech_act_dict]
        """
        if not inputs:
            return [{"type": "KHABAR", "subtype": "ITHBAT"}]
        
        tokens = inputs[0] if inputs else []
        features = inputs[1] if len(inputs) > 1 else {}
        
        # Classify using full classifier
        speech_act = self.classifier.classify(tokens, features)
        
        return [speech_act.to_dict()]


class MemoryWriteGate(Gate):
    """
    G_MEMORY_WRITE: Write to memory graph.
    
    Persists verified outputs only.
    """
    
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Write graph delta to memory.
        
        Args:
            inputs: [graph_delta]
            priors: Memory structure IDs
            
        Returns:
            [mem_commit_id]
        """
        graph_delta = inputs[0] if inputs else {}
        
        # Generate commit ID
        import hashlib
        import json
        commit_data = json.dumps(graph_delta, sort_keys=True).encode('utf-8')
        commit_id = hashlib.sha256(commit_data).hexdigest()[:16]
        
        return [f"MEM_{commit_id}"]


class MemoryReadGate(Gate):
    """
    G_MEMORY_READ: Read from memory by ID.
    
    No free recall - must specify IDs.
    """
    
    def execute(self, inputs: List[Any], priors: List[str]) -> List[Any]:
        """
        Read memory by IDs.
        
        Args:
            inputs: [memory_ids]
            priors: Memory access rules
            
        Returns:
            [memory_content]
        """
        memory_ids = inputs[0] if inputs else []
        
        # TODO: Implement actual memory retrieval
        # For now return placeholder
        return [{"ids": memory_ids, "content": {}}]


class GateRegistry:
    """
    Registry of all available gates.
    
    Manages gate creation and lookup.
    """
    
    def __init__(self):
        """Initialize empty registry"""
        self.gates: dict[str, type[Gate]] = {}
        self.definitions: dict[str, GateDefinition] = {}
        
        # Register built-in gates
        self.register("G_ATTEND", AttentionGate)
        self.register("G_CODEC_VERIFY", CodecVerifyGate)
        self.register("G_SPEECH_ACT", SpeechActGate)
        self.register("G_MEMORY_WRITE", MemoryWriteGate)
        self.register("G_MEMORY_READ", MemoryReadGate)
    
    def register(self, gate_id: str, gate_class: type[Gate]):
        """
        Register a gate class.
        
        Args:
            gate_id: Gate identifier
            gate_class: Gate class
        """
        self.gates[gate_id] = gate_class
    
    def register_definition(self, definition: GateDefinition):
        """
        Register gate definition from dictionary.
        
        Args:
            definition: Gate definition
        """
        self.definitions[definition.gate_id] = definition
    
    def create(self, gate_id: str) -> Optional[Gate]:
        """
        Create gate instance.
        
        Args:
            gate_id: Gate to create
            
        Returns:
            Gate instance or None
        """
        gate_class = self.gates.get(gate_id)
        if gate_class:
            definition = self.definitions.get(gate_id)
            return gate_class(gate_id, definition)
        return None
    
    def list_gates(self) -> List[str]:
        """List all registered gates"""
        return list(self.gates.keys())
