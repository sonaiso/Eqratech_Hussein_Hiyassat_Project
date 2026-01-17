"""
Dictionary Loader: Load and access FractalHub dictionaries

Supports:
- v01 (backward compatibility)
- v02 (current version with provenance)
"""

import os
from pathlib import Path
from typing import Any, Dict, Optional

try:
    import yaml
except ImportError:
    yaml = None


class DictionaryLoader:
    """
    Load and access FractalHub dictionary data.
    
    Supports both v01 and v02 dictionary formats.
    """
    
    def __init__(self, dictionary_path: Optional[str] = None, version: str = "v02"):
        """
        Initialize dictionary loader.
        
        Args:
            dictionary_path: Optional path to dictionary YAML file
            version: Dictionary version ("v01" or "v02")
        """
        self.version = version
        self.dictionary_path = dictionary_path
        self.data: Dict[str, Any] = {}
        
        if dictionary_path:
            self.load(dictionary_path)
        else:
            # Load from default location
            self.load_default(version)
    
    def load_default(self, version: str = "v02") -> None:
        """
        Load dictionary from default location.
        
        Args:
            version: Dictionary version ("v01" or "v02")
        """
        # Find the data directory
        current_file = Path(__file__).resolve()
        data_dir = current_file.parent
        
        filename = f"fractalhub_dictionary_{version}.yaml"
        default_path = data_dir / filename
        
        if default_path.exists():
            self.load(str(default_path))
        else:
            # Dictionary not yet created - initialize empty
            self.data = {
                "meta": {
                    "dict_version": 2 if version == "v02" else 1,
                    "codec_version": 1,
                    "schema_version": 1,
                },
                "units": {},
                "gates": {},
            }
    
    def load(self, path: str) -> None:
        """
        Load dictionary from file.
        
        Args:
            path: Path to YAML file
        """
        if yaml is None:
            raise ImportError("PyYAML is required to load dictionaries. Install with: pip install pyyaml")
        
        with open(path, "r", encoding="utf-8") as f:
            self.data = yaml.safe_load(f) or {}
        
        self.dictionary_path = path
    
    def get_unit(self, unit_id: str) -> Optional[Dict[str, Any]]:
        """
        Get a unit by ID.
        
        Args:
            unit_id: Unit identifier (e.g., "U:DIACRITIC:FATHA")
            
        Returns:
            Unit dictionary or None if not found
        """
        units = self.data.get("units", {})
        
        # v02 format: units are nested under their IDs
        if unit_id in units:
            return units[unit_id]
        
        # Search by lexicon_id field
        for unit_key, unit_data in units.items():
            if unit_data.get("lexicon_id") == unit_id:
                return unit_data
        
        return None
    
    def get_gate(self, gate_id: str) -> Optional[Dict[str, Any]]:
        """
        Get a gate by ID.
        
        Args:
            gate_id: Gate identifier (e.g., "G_C1_CODEC_VERIFY")
            
        Returns:
            Gate dictionary or None if not found
        """
        gates = self.data.get("gates", {})
        
        # v02 format: gates are nested under their IDs
        if gate_id in gates:
            return gates[gate_id]
        
        # Search by gate_id field
        for gate_key, gate_data in gates.items():
            if gate_data.get("gate_id") == gate_id:
                return gate_data
        
        return None
    
    def get_all_units(self) -> Dict[str, Any]:
        """Get all units."""
        return self.data.get("units", {})
    
    def get_all_gates(self) -> Dict[str, Any]:
        """Get all gates."""
        return self.data.get("gates", {})
    
    def get_meta(self) -> Dict[str, Any]:
        """Get dictionary metadata."""
        return self.data.get("meta", {})
    
    def get_version(self) -> int:
        """Get dictionary version number."""
        return self.get_meta().get("dict_version", 1)


def load_dictionary(version: str = "v02", path: Optional[str] = None) -> DictionaryLoader:
    """
    Load a FractalHub dictionary.
    
    Args:
        version: Dictionary version ("v01" or "v02")
        path: Optional custom path to dictionary file
        
    Returns:
        DictionaryLoader instance
        
    Example:
        >>> dict_v02 = load_dictionary(version="v02")
        >>> fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
    """
    return DictionaryLoader(dictionary_path=path, version=version)
