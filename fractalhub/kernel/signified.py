"""
Signified: C3 layer entities with full provenance (Kernel v1.2)

Entity: Meaning-bearing units with:
- Signifier link (points to C1 form)
- Semantic content
- Provenance from dictionary
- Trace pointer for creation
"""

from typing import Any, Dict, Optional

from fractalhub.kernel.record import Record


class Entity(Record):
    """
    C3 signified entity with provenance tracking.
    
    Core principle: NO MEANING WITHOUT EVIDENCE
    
    Every entity must have:
    - signifier_link: Points to C1 form (no orphaned meaning)
    - meaning: Semantic content
    - provenance: Source and confidence information
    - lexicon_id: Dictionary reference
    - created_by_trace_id: Trace that created this entity
    """
    
    def __init__(
        self,
        entity_id: str,
        signifier_link: str,
        meaning: Dict[str, Any],
        provenance: Optional[Dict[str, Any]] = None,
        lexicon_id: Optional[str] = None,
        created_by_trace_id: Optional[str] = None,
        **kwargs
    ):
        """
        Initialize a signified entity.
        
        Args:
            entity_id: Unique entity identifier
            signifier_link: Link to C1 signifier unit (e.g., "U:DIACRITIC:FATHA")
            meaning: Semantic content dictionary
            provenance: Source metadata (confidence, references, etc.)
            lexicon_id: Dictionary entry ID
            created_by_trace_id: Trace ID that created this entity
            **kwargs: Additional fields
        """
        super().__init__(
            record_id=entity_id,
            record_type="entity",
            **kwargs
        )
        
        # Core fields
        self.entity_id = entity_id
        self.signifier_link = signifier_link
        self.meaning = meaning
        
        # Provenance (CRITICAL for preventing hallucination)
        self.provenance = provenance or {
            "source_type": "derived",
            "confidence": "shakk",  # Default to lowest confidence
            "attestation_count": 0,
            "references": [],
        }
        
        # Evidence chain
        self.lexicon_id = lexicon_id or signifier_link
        self.created_by_trace_id = created_by_trace_id
        
        # Validate entity
        self._validate()
    
    def _validate(self) -> None:
        """
        Validate entity satisfies locked architecture rules.
        
        Raises:
            ValueError: If validation fails
        """
        if not self.signifier_link:
            raise ValueError(
                f"Entity {self.entity_id} has no signifier_link. "
                "NO MEANING WITHOUT FORM."
            )
        
        if not self.meaning:
            raise ValueError(
                f"Entity {self.entity_id} has empty meaning."
            )
        
        if not self.created_by_trace_id:
            raise ValueError(
                f"Entity {self.entity_id} has no trace pointer. "
                "NO C3 WITHOUT C2 TRACE."
            )
    
    def get_confidence(self) -> float:
        """
        Get epistemic confidence level.
        
        Returns:
            Float value: 1.0 (yaqin), 0.7 (zann), 0.4 (shakk)
        """
        confidence_map = {
            "yaqin": 1.0,
            "zann": 0.7,
            "shakk": 0.4,
        }
        
        confidence_str = self.provenance.get("confidence", "shakk")
        return confidence_map.get(confidence_str, 0.4)
    
    def has_corpus_attestation(self) -> bool:
        """Check if entity has corpus evidence."""
        attestation_count = self.provenance.get("attestation_count", 0)
        return attestation_count > 0
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert entity to dictionary."""
        result = super().to_dict()
        result.update({
            "entity_id": self.entity_id,
            "signifier_link": self.signifier_link,
            "meaning": self.meaning,
            "provenance": self.provenance,
            "lexicon_id": self.lexicon_id,
            "created_by_trace_id": self.created_by_trace_id,
            "confidence": self.get_confidence(),
            "has_attestation": self.has_corpus_attestation(),
        })
        return result
    
    def __repr__(self) -> str:
        return (
            f"Entity(id={self.entity_id}, "
            f"signifier={self.signifier_link}, "
            f"confidence={self.get_confidence()})"
        )
