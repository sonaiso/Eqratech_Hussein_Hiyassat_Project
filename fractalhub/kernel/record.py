"""
Record: Base data structure with version metadata (Kernel v1.2)

All data structures inherit from Record to ensure:
- Version tracking (kernel_version, architecture_version)
- Timestamp metadata (created_at_iso)
- Consistent structure across the system
"""

from datetime import datetime, timezone
from typing import Any, Dict, Optional


class Record:
    """
    Base record with kernel v1.2 metadata.
    
    Every record in the system includes:
    - kernel_version: "1.2" for this release
    - architecture_version: "locked_v1" enforcing anti-hallucination
    - created_at_iso: ISO 8601 timestamp in UTC
    """
    
    def __init__(
        self,
        record_id: str,
        record_type: str,
        data: Optional[Dict[str, Any]] = None,
        **kwargs
    ):
        """
        Initialize a record with version metadata.
        
        Args:
            record_id: Unique identifier for this record
            record_type: Type of record (e.g., "unit", "gate", "entity")
            data: Optional data payload
            **kwargs: Additional fields
        """
        self.record_id = record_id
        self.record_type = record_type
        self.data = data or {}
        
        # Kernel v1.2 metadata
        self.kernel_version = "1.2"
        self.architecture_version = "locked_v1"
        self.created_at_iso = datetime.now(timezone.utc).isoformat()
        
        # Store additional fields
        for key, value in kwargs.items():
            setattr(self, key, value)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert record to dictionary representation."""
        result = {
            "record_id": self.record_id,
            "record_type": self.record_type,
            "kernel_version": self.kernel_version,
            "architecture_version": self.architecture_version,
            "created_at_iso": self.created_at_iso,
        }
        
        # Add data if present
        if self.data:
            result["data"] = self.data
        
        # Add any additional attributes
        for key, value in self.__dict__.items():
            if key not in result and not key.startswith("_"):
                result[key] = value
        
        return result
    
    def __repr__(self) -> str:
        return f"Record(id={self.record_id}, type={self.record_type}, v={self.kernel_version})"
