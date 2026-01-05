#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Consciousness Components Module

Implements the 4 consciousness components based on النبهاني's theory:
1. Attention (الانتباه): Selection and focus mechanism
2. Memory (الذاكرة): Storage and retrieval with provenance
3. Self-model (نموذج الذات): Perspective and epistemic stance
4. Affect/Value (القيمة والتأثير): Priority and importance

These components prevent "jumping" by enforcing control gates.
"""

from typing import Dict, List, Any, Optional, Set, Tuple
from dataclasses import dataclass, field
from enum import Enum
import hashlib


class AttentionScope(Enum):
    """Attention scope levels"""
    NARROW = "narrow"      # Focused on specific span
    MEDIUM = "medium"      # Context window
    WIDE = "wide"          # Full text
    EXPANDED = "expanded"  # Beyond current text


class EpistemicLevel(Enum):
    """Epistemic certainty levels (from dictionary v02)"""
    YAQIN = ("YAQIN", 1.0, "اليقين")      # Certainty
    ZANN = ("ZANN", 0.7, "الظن")          # Strong belief
    SHAKK = ("SHAKK", 0.4, "الشك")        # Doubt
    
    def __init__(self, code: str, certainty: float, arabic: str):
        self.code = code
        self.certainty = certainty
        self.arabic = arabic


class Perspective(Enum):
    """Discourse perspective"""
    FIRST = "first"       # متكلم (Speaker)
    SECOND = "second"     # مخاطب (Addressee)
    THIRD = "third"       # غائب (Absent/Third party)


class ValueDimension(Enum):
    """Value dimensions for affect/value state"""
    PRIORITY = "priority"       # أولوية
    THREAT = "threat"           # تهديد
    DESIRE = "desire"           # رغبة
    UTILITY = "utility"         # منفعة
    AROUSAL = "arousal"         # إثارة
    VALENCE = "valence"         # قيمة إيجابية/سلبية


@dataclass
class AttentionState:
    """
    Attention state tracking focus and scope.
    
    Implements الانتباه (Attention) as selection mechanism.
    Prevents processing outside focus without explicit expansion.
    """
    focus_span_ids: List[str] = field(default_factory=list)
    scope: AttentionScope = AttentionScope.NARROW
    history: List[Dict[str, Any]] = field(default_factory=list)
    
    def set_focus(self, span_ids: List[str], scope: AttentionScope = AttentionScope.NARROW):
        """
        Set attention focus on specific span.
        
        Args:
            span_ids: List of unit/token IDs to focus on
            scope: Scope level for attention
        """
        self.history.append({
            "previous_focus": self.focus_span_ids.copy(),
            "previous_scope": self.scope
        })
        self.focus_span_ids = span_ids
        self.scope = scope
    
    def expand_focus(self, additional_ids: List[str], new_scope: Optional[AttentionScope] = None):
        """
        Expand attention focus (must be recorded in trace).
        
        Args:
            additional_ids: Additional IDs to include
            new_scope: New scope level (optional)
        """
        self.history.append({
            "previous_focus": self.focus_span_ids.copy(),
            "previous_scope": self.scope,
            "expansion": additional_ids
        })
        self.focus_span_ids.extend(additional_ids)
        if new_scope:
            self.scope = new_scope
    
    def is_in_focus(self, unit_id: str) -> bool:
        """Check if unit is in current attention focus"""
        return unit_id in self.focus_span_ids
    
    def to_dict(self) -> Dict[str, Any]:
        """Export to dictionary"""
        return {
            "focus_span_ids": self.focus_span_ids,
            "scope": self.scope.value,
            "history_length": len(self.history)
        }


@dataclass
class MemoryEntry:
    """
    Memory entry with full provenance.
    
    Each entry must have:
    - content: The actual data
    - provenance: Source IDs (prior_ids)
    - commit_id: Unique identifier
    """
    commit_id: str
    content: Dict[str, Any]
    provenance: Dict[str, List[str]]  # prior_ids: lexicon_ids, ruleset_ids, etc.
    timestamp: str
    entry_type: str  # "graph_delta", "inference", "perception", etc.
    
    def to_dict(self) -> Dict[str, Any]:
        """Export to dictionary"""
        return {
            "commit_id": self.commit_id,
            "content": self.content,
            "provenance": self.provenance,
            "timestamp": self.timestamp,
            "entry_type": self.entry_type
        }


class MemoryStore:
    """
    Memory storage and retrieval system.
    
    Implements الذاكرة (Memory) as provenance-based storage.
    No free recall - all access must be by ID.
    """
    
    def __init__(self):
        self.entries: Dict[str, MemoryEntry] = {}
        self.index_by_type: Dict[str, List[str]] = {}
    
    def write(self, 
              content: Dict[str, Any],
              provenance: Dict[str, List[str]],
              entry_type: str,
              timestamp: str) -> str:
        """
        Write to memory with full provenance.
        
        Args:
            content: The data to store
            provenance: Source IDs proving legitimacy
            entry_type: Type of memory entry
            timestamp: ISO timestamp
            
        Returns:
            commit_id: Unique identifier for retrieval
        """
        # Generate commit ID from content hash
        content_str = str(sorted(content.items()))
        commit_id = hashlib.sha256(content_str.encode()).hexdigest()[:16]
        
        entry = MemoryEntry(
            commit_id=commit_id,
            content=content,
            provenance=provenance,
            timestamp=timestamp,
            entry_type=entry_type
        )
        
        self.entries[commit_id] = entry
        
        # Index by type
        if entry_type not in self.index_by_type:
            self.index_by_type[entry_type] = []
        self.index_by_type[entry_type].append(commit_id)
        
        return commit_id
    
    def read(self, commit_id: str) -> Optional[MemoryEntry]:
        """
        Read from memory by ID only.
        
        Args:
            commit_id: The commit ID to retrieve
            
        Returns:
            MemoryEntry if found, None otherwise
        """
        return self.entries.get(commit_id)
    
    def read_by_type(self, entry_type: str) -> List[MemoryEntry]:
        """
        Read all entries of a specific type.
        
        Args:
            entry_type: Type of entries to retrieve
            
        Returns:
            List of matching memory entries
        """
        commit_ids = self.index_by_type.get(entry_type, [])
        return [self.entries[cid] for cid in commit_ids if cid in self.entries]
    
    def to_dict(self) -> Dict[str, Any]:
        """Export to dictionary"""
        return {
            "entry_count": len(self.entries),
            "types": list(self.index_by_type.keys()),
            "entries": {cid: entry.to_dict() for cid, entry in self.entries.items()}
        }


@dataclass
class SelfState:
    """
    Self-model state tracking perspective and epistemic stance.
    
    Implements نموذج الذات (Self-model):
    - Who is the observer/agent?
    - What is the certainty level?
    - What are the responsibility boundaries?
    """
    perspective: Perspective = Perspective.THIRD
    epistemic_level: EpistemicLevel = EpistemicLevel.SHAKK
    responsibility_scope: Set[str] = field(default_factory=set)
    commitments: List[Dict[str, Any]] = field(default_factory=list)
    
    def set_perspective(self, perspective: Perspective):
        """Set discourse perspective"""
        self.perspective = perspective
    
    def set_epistemic_level(self, level: EpistemicLevel):
        """Set epistemic certainty level"""
        self.epistemic_level = level
    
    def add_commitment(self, commitment: Dict[str, Any]):
        """
        Add a commitment/responsibility.
        
        Args:
            commitment: Dict with keys like "type", "target", "condition"
        """
        self.commitments.append(commitment)
        if "target" in commitment:
            self.responsibility_scope.add(commitment["target"])
    
    def is_responsible_for(self, target_id: str) -> bool:
        """Check if self is responsible for target"""
        return target_id in self.responsibility_scope
    
    def to_dict(self) -> Dict[str, Any]:
        """Export to dictionary"""
        return {
            "perspective": self.perspective.value,
            "epistemic_level": self.epistemic_level.code,
            "certainty": self.epistemic_level.certainty,
            "responsibility_scope": list(self.responsibility_scope),
            "commitments_count": len(self.commitments)
        }


@dataclass
class ValueState:
    """
    Affect/Value state for priority and importance.
    
    Implements القيمة والتأثير (Affect/Value):
    - Priority levels
    - Threat assessment
    - Desire/utility values
    - Emotional arousal
    
    Controls:
    - Gate ordering
    - Evidence weighting
    - Disambiguation preferences
    """
    dimensions: Dict[ValueDimension, float] = field(default_factory=dict)
    priorities: List[Tuple[str, float]] = field(default_factory=list)
    
    def __post_init__(self):
        # Initialize all dimensions to neutral (0.5)
        if not self.dimensions:
            for dim in ValueDimension:
                self.dimensions[dim] = 0.5
    
    def set_value(self, dimension: ValueDimension, value: float):
        """
        Set value for a dimension (0.0 - 1.0).
        
        Args:
            dimension: The value dimension
            value: Value between 0.0 and 1.0
        """
        if not 0.0 <= value <= 1.0:
            raise ValueError(f"Value must be between 0.0 and 1.0, got {value}")
        self.dimensions[dimension] = value
    
    def get_value(self, dimension: ValueDimension) -> float:
        """Get value for a dimension"""
        return self.dimensions.get(dimension, 0.5)
    
    def add_priority(self, item_id: str, priority: float):
        """
        Add priority for an item.
        
        Args:
            item_id: Identifier for the item
            priority: Priority value (0.0 - 1.0)
        """
        if not 0.0 <= priority <= 1.0:
            raise ValueError(f"Priority must be between 0.0 and 1.0, got {priority}")
        self.priorities.append((item_id, priority))
        # Keep sorted by priority (descending)
        self.priorities.sort(key=lambda x: x[1], reverse=True)
    
    def get_priority(self, item_id: str) -> Optional[float]:
        """Get priority for an item"""
        for iid, priority in self.priorities:
            if iid == item_id:
                return priority
        return None
    
    def compute_overall_importance(self) -> float:
        """
        Compute overall importance score from all dimensions.
        
        Returns:
            Weighted importance score (0.0 - 1.0)
        """
        # Weighted combination
        weights = {
            ValueDimension.PRIORITY: 0.3,
            ValueDimension.THREAT: 0.25,
            ValueDimension.UTILITY: 0.2,
            ValueDimension.DESIRE: 0.15,
            ValueDimension.AROUSAL: 0.05,
            ValueDimension.VALENCE: 0.05
        }
        
        total = sum(
            self.dimensions.get(dim, 0.5) * weight
            for dim, weight in weights.items()
        )
        return total
    
    def to_dict(self) -> Dict[str, Any]:
        """Export to dictionary"""
        return {
            "dimensions": {dim.value: val for dim, val in self.dimensions.items()},
            "priorities": [{"item_id": iid, "priority": p} for iid, p in self.priorities],
            "overall_importance": self.compute_overall_importance()
        }


class ConsciousnessVector:
    """
    Complete consciousness state vector.
    
    Combines all 4 components:
    - Attention (selection)
    - Memory (storage)
    - Self (perspective)
    - Value (importance)
    """
    
    def __init__(self):
        self.attention = AttentionState()
        self.memory = MemoryStore()
        self.self_state = SelfState()
        self.value = ValueState()
    
    def to_dict(self) -> Dict[str, Any]:
        """Export full consciousness state"""
        return {
            "attention": self.attention.to_dict(),
            "memory": self.memory.to_dict(),
            "self": self.self_state.to_dict(),
            "value": self.value.to_dict()
        }


# Enhanced gate functions for consciousness components

def gate_attend(inputs: Dict[str, Any], 
                consciousness: ConsciousnessVector,
                **kwargs) -> Dict[str, Any]:
    """
    G_ATTEND: Set attention focus.
    
    Args:
        inputs: Must contain "form_stream" or "span_ids"
        consciousness: Consciousness vector to update
        **kwargs: Additional parameters (scope, etc.)
        
    Returns:
        Dict with focus_span_ids and scope
    """
    span_ids = inputs.get("span_ids", [])
    if not span_ids and "form_stream" in inputs:
        # Extract from form_stream if available
        span_ids = inputs["form_stream"].get("unit_ids", [])
    
    scope = kwargs.get("scope", AttentionScope.NARROW)
    consciousness.attention.set_focus(span_ids, scope)
    
    return {
        "focus_span_ids": consciousness.attention.focus_span_ids,
        "scope": consciousness.attention.scope.value,
        "success": True
    }


def gate_memory_write(inputs: Dict[str, Any],
                     consciousness: ConsciousnessVector,
                     timestamp: str,
                     **kwargs) -> Dict[str, Any]:
    """
    G_MEMORY_WRITE: Write to memory with provenance.
    
    Args:
        inputs: Must contain "content" and "provenance"
        consciousness: Consciousness vector to update
        timestamp: ISO timestamp
        **kwargs: Additional parameters (entry_type, etc.)
        
    Returns:
        Dict with commit_id
    """
    content = inputs.get("content", {})
    provenance = inputs.get("provenance", {})
    entry_type = kwargs.get("entry_type", "graph_delta")
    
    # Validate provenance exists
    if not provenance:
        return {
            "success": False,
            "error": "NO_PROVENANCE",
            "message": "Cannot write to memory without provenance (prior_ids)"
        }
    
    commit_id = consciousness.memory.write(
        content=content,
        provenance=provenance,
        entry_type=entry_type,
        timestamp=timestamp
    )
    
    return {
        "commit_id": commit_id,
        "success": True
    }


def gate_memory_read(inputs: Dict[str, Any],
                    consciousness: ConsciousnessVector,
                    **kwargs) -> Dict[str, Any]:
    """
    G_MEMORY_READ: Read from memory by ID only.
    
    Args:
        inputs: Must contain "commit_id" or "entry_type"
        consciousness: Consciousness vector to query
        **kwargs: Additional parameters
        
    Returns:
        Dict with memory entries
    """
    commit_id = inputs.get("commit_id")
    entry_type = inputs.get("entry_type")
    
    if commit_id:
        entry = consciousness.memory.read(commit_id)
        if entry:
            return {
                "entry": entry.to_dict(),
                "success": True
            }
        else:
            return {
                "success": False,
                "error": "NOT_FOUND"
            }
    elif entry_type:
        entries = consciousness.memory.read_by_type(entry_type)
        return {
            "entries": [e.to_dict() for e in entries],
            "count": len(entries),
            "success": True
        }
    else:
        return {
            "success": False,
            "error": "INVALID_INPUT",
            "message": "Must provide commit_id or entry_type"
        }
