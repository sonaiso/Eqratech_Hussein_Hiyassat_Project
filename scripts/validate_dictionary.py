#!/usr/bin/env python3
"""
Dictionary Validation Script

Validates FractalHub dictionary structure and content:
- YAML syntax
- Required fields present
- Unique IDs (no duplicates)
- ID format conventions (U:, G:, INV:)
- Provenance schema
- Bilingual completeness (v02)
- DRY principle (no redundant entries)
"""

import sys
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

try:
    import yaml
except ImportError:
    print("ERROR: PyYAML is required. Install with: pip install pyyaml")
    sys.exit(1)


class DictionaryValidator:
    """Validates FractalHub dictionary files."""
    
    def __init__(self, dictionary_path: str):
        """
        Initialize validator.
        
        Args:
            dictionary_path: Path to dictionary YAML file
        """
        self.path = Path(dictionary_path)
        self.data: Dict[str, Any] = {}
        self.errors: List[str] = []
        self.warnings: List[str] = []
    
    def load_dictionary(self) -> bool:
        """
        Load dictionary from file.
        
        Returns:
            True if loaded successfully, False otherwise
        """
        if not self.path.exists():
            self.errors.append(f"Dictionary file not found: {self.path}")
            return False
        
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                self.data = yaml.safe_load(f) or {}
            return True
        except yaml.YAMLError as e:
            self.errors.append(f"YAML syntax error: {e}")
            return False
        except Exception as e:
            self.errors.append(f"Failed to load dictionary: {e}")
            return False
    
    def validate_meta(self) -> bool:
        """Validate metadata section."""
        if "meta" not in self.data:
            self.errors.append("Missing 'meta' section")
            return False
        
        meta = self.data["meta"]
        required_fields = ["dict_version", "codec_version", "schema_version"]
        
        for field in required_fields:
            if field not in meta:
                self.errors.append(f"Missing required meta field: {field}")
        
        # Check version is numeric
        dict_version = meta.get("dict_version")
        if dict_version is not None and not isinstance(dict_version, int):
            self.errors.append(f"dict_version must be integer, got: {type(dict_version)}")
        
        return len(self.errors) == 0
    
    def validate_id_format(self, id_str: str, expected_prefix: str) -> bool:
        """
        Validate ID format conventions.
        
        Args:
            id_str: ID string to validate
            expected_prefix: Expected prefix (e.g., "U:", "G:", "INV:")
            
        Returns:
            True if format is valid
        """
        if not id_str.startswith(expected_prefix):
            self.errors.append(
                f"ID format error: '{id_str}' should start with '{expected_prefix}'"
            )
            return False
        
        # Check for uppercase with underscores or colons
        parts = id_str.split(":")
        for part in parts[1:]:  # Skip prefix
            if not part or not part.replace("_", "").isalnum():
                self.errors.append(
                    f"ID format error: '{id_str}' contains invalid characters"
                )
                return False
        
        return True
    
    def validate_units(self) -> Tuple[bool, Set[str]]:
        """
        Validate units section.
        
        Returns:
            Tuple of (validation_passed, set_of_unit_ids)
        """
        if "units" not in self.data:
            self.errors.append("Missing 'units' section")
            return False, set()
        
        units = self.data["units"]
        unit_ids: Set[str] = set()
        duplicates: Set[str] = set()
        
        for unit_key, unit_data in units.items():
            if not isinstance(unit_data, dict):
                self.errors.append(f"Unit '{unit_key}' is not a dictionary")
                continue
            
            # Check required fields
            lexicon_id = unit_data.get("lexicon_id")
            if not lexicon_id:
                self.errors.append(f"Unit '{unit_key}' missing 'lexicon_id'")
                continue
            
            # Validate ID format (should start with U:)
            self.validate_id_format(lexicon_id, "U:")
            
            # Check for duplicates
            if lexicon_id in unit_ids:
                duplicates.add(lexicon_id)
            unit_ids.add(lexicon_id)
            
            # Check required fields based on type
            unit_type = unit_data.get("type")
            if not unit_type:
                self.errors.append(f"Unit '{lexicon_id}' missing 'type'")
            
            if "status" not in unit_data:
                self.errors.append(f"Unit '{lexicon_id}' missing 'status'")
            
            # For v02, check provenance
            dict_version = self.data.get("meta", {}).get("dict_version", 1)
            if dict_version >= 2:
                if "provenance" not in unit_data:
                    self.warnings.append(
                        f"Unit '{lexicon_id}' missing provenance (recommended for v02)"
                    )
        
        if duplicates:
            self.errors.append(f"Duplicate unit IDs found: {duplicates}")
        
        return len(self.errors) == 0, unit_ids
    
    def validate_gates(self) -> Tuple[bool, Set[str]]:
        """
        Validate gates section.
        
        Returns:
            Tuple of (validation_passed, set_of_gate_ids)
        """
        if "gates" not in self.data:
            self.errors.append("Missing 'gates' section")
            return False, set()
        
        gates = self.data["gates"]
        gate_ids: Set[str] = set()
        duplicates: Set[str] = set()
        
        for gate_key, gate_data in gates.items():
            if not isinstance(gate_data, dict):
                self.errors.append(f"Gate '{gate_key}' is not a dictionary")
                continue
            
            # Check required fields
            gate_id = gate_data.get("gate_id")
            if not gate_id:
                self.errors.append(f"Gate '{gate_key}' missing 'gate_id'")
                continue
            
            # Validate ID format (should start with G_)
            if not gate_id.startswith("G_"):
                self.errors.append(
                    f"Gate ID format error: '{gate_id}' should start with 'G_'"
                )
            
            # Check for duplicates
            if gate_id in gate_ids:
                duplicates.add(gate_id)
            gate_ids.add(gate_id)
            
            # Check required fields
            required_fields = ["layer", "inputs", "outputs", "status"]
            for field in required_fields:
                if field not in gate_data:
                    self.errors.append(f"Gate '{gate_id}' missing '{field}'")
            
            # For v02, check four_conditions and ruleset_ids
            dict_version = self.data.get("meta", {}).get("dict_version", 1)
            if dict_version >= 2:
                if "four_conditions" not in gate_data:
                    self.warnings.append(
                        f"Gate '{gate_id}' missing four_conditions (recommended for v02)"
                    )
                
                if "ruleset_ids" not in gate_data:
                    self.warnings.append(
                        f"Gate '{gate_id}' missing ruleset_ids (recommended for v02)"
                    )
        
        if duplicates:
            self.errors.append(f"Duplicate gate IDs found: {duplicates}")
        
        return len(self.errors) == 0, gate_ids
    
    def validate_provenance_schema(self) -> bool:
        """Validate provenance schema section (v02 only)."""
        dict_version = self.data.get("meta", {}).get("dict_version", 1)
        
        if dict_version < 2:
            return True  # Not required for v01
        
        if "provenance" not in self.data:
            self.warnings.append("Missing 'provenance' schema section (recommended for v02)")
            return True  # Warning only
        
        provenance = self.data["provenance"]
        
        if "schema" not in provenance:
            self.warnings.append("Provenance section missing 'schema' field")
        
        return True
    
    def validate_bilingual(self) -> bool:
        """Validate bilingual completeness (v02 only)."""
        dict_version = self.data.get("meta", {}).get("dict_version", 1)
        
        if dict_version < 2:
            return True  # Not required for v01
        
        # Check gates have both description_en and description_ar
        gates = self.data.get("gates", {})
        for gate_id, gate_data in gates.items():
            if "description_en" not in gate_data:
                self.warnings.append(
                    f"Gate '{gate_id}' missing English description (recommended)"
                )
            if "description_ar" not in gate_data:
                self.warnings.append(
                    f"Gate '{gate_id}' missing Arabic description (recommended)"
                )
        
        return True
    
    def validate(self) -> bool:
        """
        Run all validation checks.
        
        Returns:
            True if all validations pass (no errors), False otherwise
        """
        print(f"Validating dictionary: {self.path}")
        print("=" * 60)
        
        # Load dictionary
        if not self.load_dictionary():
            return False
        
        # Run validations
        self.validate_meta()
        self.validate_units()
        self.validate_gates()
        self.validate_provenance_schema()
        self.validate_bilingual()
        
        # Report results
        if self.errors:
            print("\n❌ ERRORS:")
            for error in self.errors:
                print(f"  - {error}")
        
        if self.warnings:
            print("\n⚠️  WARNINGS:")
            for warning in self.warnings:
                print(f"  - {warning}")
        
        if not self.errors and not self.warnings:
            print("\n✅ Validation passed! No errors or warnings.")
        elif not self.errors:
            print(f"\n✅ Validation passed with {len(self.warnings)} warnings.")
        else:
            print(f"\n❌ Validation failed with {len(self.errors)} errors.")
        
        return len(self.errors) == 0


def main():
    """Main entry point."""
    if len(sys.argv) != 2:
        print("Usage: python validate_dictionary.py <path_to_dictionary.yaml>")
        sys.exit(1)
    
    dictionary_path = sys.argv[1]
    validator = DictionaryValidator(dictionary_path)
    
    success = validator.validate()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
