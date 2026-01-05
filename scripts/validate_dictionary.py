#!/usr/bin/env python3
"""
FractalHub Dictionary Validator

A comprehensive validation tool for FractalHub dictionary YAML files.
Validates structure, metadata, units, gates, invariants, and ensures
compliance with naming conventions and required fields.

Usage:
    python validate_dictionary.py <path_to_dictionary.yaml>
    ./validate_dictionary.py <path_to_dictionary.yaml>

Example:
    python validate_dictionary.py fractalhub/data/fractalhub_dictionary_v02.yaml

Exit Codes:
    0: All validations passed
    1: Validation errors found

Author: Eqratech Arabic Diana Project
Version: 1.0.0
License: MIT
"""

import sys
import yaml
from pathlib import Path
from typing import Dict, List, Set, Any
from datetime import datetime


class DictionaryValidator:
    """
    Validates FractalHub dictionary YAML files against defined schema.
    
    This validator checks:
    - Top-level structure and required sections
    - Metadata fields (version, timestamps, compatibility)
    - Unit definitions (IDs, types, required fields)
    - Gate definitions (IDs, layers, inputs/outputs)
    - Invariant definitions (IDs, scopes, patterns)
    - ID format compliance (U:, G:, INV: prefixes)
    - Duplicate detection
    - Version consistency
    
    Attributes:
        REQUIRED_TOP_KEYS (list): Required top-level dictionary keys
        REQUIRED_META_KEYS (list): Required metadata fields
        REQUIRED_UNIT_KEYS (list): Required unit fields
        REQUIRED_GATE_KEYS (list): Required gate fields
        REQUIRED_INVARIANT_KEYS (list): Required invariant fields
        
        yaml_path (Path): Path to the YAML dictionary file
        errors (list): Collected validation errors
        warnings (list): Collected validation warnings
        data (dict): Loaded dictionary data
    
    Example:
        >>> validator = DictionaryValidator("dictionary.yaml")
        >>> success = validator.run_all_validations()
        >>> validator.report()
        >>> sys.exit(0 if success else 1)
    """
    
    REQUIRED_TOP_KEYS = ['meta', 'units', 'gates', 'evidence', 'invariants', 'tags', 'mappings']
    REQUIRED_META_KEYS = ['dict_version', 'schema_version', 'generated_at']
    REQUIRED_UNIT_KEYS = ['unit_id', 'kind', 'status']
    REQUIRED_GATE_KEYS = ['gate_id', 'layer', 'inputs', 'outputs', 'status']
    REQUIRED_INVARIANT_KEYS = ['inv_id', 'scope', 'pattern', 'status']
    
    def __init__(self, yaml_path: str):
        """
        Initialize the validator with a dictionary file path.
        
        Args:
            yaml_path (str): Path to the YAML dictionary file to validate
        """
        self.yaml_path = Path(yaml_path)
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.data: Dict[str, Any] = {}
    
    def load_yaml(self) -> bool:
        """
        Load and parse the YAML dictionary file.
        
        Returns:
            bool: True if loading succeeded, False otherwise
            
        Side Effects:
            - Populates self.data with parsed YAML content
            - Adds error to self.errors if loading fails
        """
        try:
            with open(self.yaml_path, 'r', encoding='utf-8') as f:
                self.data = yaml.safe_load(f)
            return True
        except Exception as e:
            self.errors.append(f"Failed to load YAML: {e}")
            return False
    
    def validate_structure(self) -> bool:
        """
        Validate top-level dictionary structure.
        
        Checks that all required top-level keys are present:
        - meta, units, gates, evidence, invariants, tags, mappings
        
        Returns:
            bool: True if all required keys are present, False otherwise
            
        Side Effects:
            Adds errors to self.errors for missing keys
        """
        for key in self.REQUIRED_TOP_KEYS:
            if key not in self.data:
                self.errors.append(f"Missing required top-level key: {key}")
        
        return len([e for e in self.errors if 'top-level' in e]) == 0
    
    def validate_meta(self) -> bool:
        """
        Validate metadata section.
        
        Checks:
        - Required fields: dict_version, schema_version, generated_at
        - Version format (must be integer >= 1)
        - Timestamp format (ISO 8601)
        
        Returns:
            bool: True if metadata is valid, False otherwise
            
        Side Effects:
            Adds errors/warnings to self.errors/self.warnings
        """
        meta = self.data.get('meta', {})
        
        for key in self.REQUIRED_META_KEYS:
            if key not in meta:
                self.errors.append(f"Missing required meta key: {key}")
        
        # Validate version format
        if 'dict_version' in meta:
            try:
                version = int(meta['dict_version'])
                if version < 1:
                    self.errors.append("dict_version must be >= 1")
            except (ValueError, TypeError):
                self.errors.append("dict_version must be an integer")
        
        # Validate timestamp
        if 'generated_at' in meta:
            try:
                datetime.fromisoformat(meta['generated_at'].replace('Z', '+00:00'))
            except (ValueError, AttributeError):
                self.warnings.append("generated_at is not a valid ISO timestamp")
        
        return len([e for e in self.errors if 'meta' in e]) == 0
    
    def validate_units(self) -> bool:
        """
        Validate units section.
        
        Checks:
        - Required fields: unit_id, kind, status
        - unit_id matches dictionary key
        - No duplicate unit_ids
        - ID format (should start with 'U:')
        
        Returns:
            bool: True if all units are valid, False otherwise
            
        Side Effects:
            Adds errors/warnings to self.errors/self.warnings
        """
        units = self.data.get('units', {})
        unit_ids: Set[str] = set()
        
        for unit_key, unit_data in units.items():
            # Check required fields
            for key in self.REQUIRED_UNIT_KEYS:
                if key not in unit_data:
                    self.errors.append(f"Unit {unit_key}: missing required key {key}")
            
            # Check unit_id matches key
            if 'unit_id' in unit_data:
                if unit_data['unit_id'] != unit_key:
                    self.errors.append(
                        f"Unit {unit_key}: unit_id mismatch ({unit_data['unit_id']})"
                    )
                
                # Check for duplicates
                if unit_data['unit_id'] in unit_ids:
                    self.errors.append(f"Duplicate unit_id: {unit_data['unit_id']}")
                unit_ids.add(unit_data['unit_id'])
            
            # Validate ID format
            if not unit_key.startswith('U:'):
                self.warnings.append(f"Unit {unit_key}: ID should start with 'U:'")
        
        return len([e for e in self.errors if 'Unit' in e]) == 0
    
    def validate_gates(self) -> bool:
        """
        Validate gates section.
        
        Checks:
        - Required fields: gate_id, layer, inputs, outputs, status
        - gate_id matches dictionary key
        - No duplicate gate_ids
        - Valid layer (C1, C2, C3, P1, P2, P3, M1, M2)
        - ID format (should start with 'G:')
        
        Returns:
            bool: True if all gates are valid, False otherwise
            
        Side Effects:
            Adds errors/warnings to self.errors/self.warnings
        """
        gates = self.data.get('gates', {})
        gate_ids: Set[str] = set()
        valid_layers = ['C1', 'C2', 'C3', 'P1', 'P2', 'P3', 'M1', 'M2']
        
        for gate_key, gate_data in gates.items():
            # Check required fields
            for key in self.REQUIRED_GATE_KEYS:
                if key not in gate_data:
                    self.errors.append(f"Gate {gate_key}: missing required key {key}")
            
            # Check gate_id matches key
            if 'gate_id' in gate_data:
                if gate_data['gate_id'] != gate_key:
                    self.errors.append(
                        f"Gate {gate_key}: gate_id mismatch ({gate_data['gate_id']})"
                    )
                
                # Check for duplicates
                if gate_data['gate_id'] in gate_ids:
                    self.errors.append(f"Duplicate gate_id: {gate_data['gate_id']}")
                gate_ids.add(gate_data['gate_id'])
            
            # Validate layer
            if 'layer' in gate_data:
                if gate_data['layer'] not in valid_layers:
                    self.warnings.append(
                        f"Gate {gate_key}: unknown layer {gate_data['layer']}"
                    )
            
            # Validate ID format
            if not gate_key.startswith('G:'):
                self.warnings.append(f"Gate {gate_key}: ID should start with 'G:'")
        
        return len([e for e in self.errors if 'Gate' in e]) == 0
    
    def validate_invariants(self) -> bool:
        """
        Validate invariants section.
        
        Checks:
        - Required fields: inv_id, scope, pattern, status
        - inv_id matches dictionary key
        - No duplicate inv_ids
        - Valid scope (C1, C2, C3, derived, global)
        - ID format (should start with 'INV:')
        
        Returns:
            bool: True if all invariants are valid, False otherwise
            
        Side Effects:
            Adds errors/warnings to self.errors/self.warnings
        """
        invariants = self.data.get('invariants', {})
        inv_ids: Set[str] = set()
        valid_scopes = ['C1', 'C2', 'C3', 'derived', 'global']
        
        for inv_key, inv_data in invariants.items():
            # Check required fields
            for key in self.REQUIRED_INVARIANT_KEYS:
                if key not in inv_data:
                    self.errors.append(
                        f"Invariant {inv_key}: missing required key {key}"
                    )
            
            # Check inv_id matches key
            if 'inv_id' in inv_data:
                if inv_data['inv_id'] != inv_key:
                    self.errors.append(
                        f"Invariant {inv_key}: inv_id mismatch ({inv_data['inv_id']})"
                    )
                
                # Check for duplicates
                if inv_data['inv_id'] in inv_ids:
                    self.errors.append(f"Duplicate inv_id: {inv_data['inv_id']}")
                inv_ids.add(inv_data['inv_id'])
            
            # Validate scope
            if 'scope' in inv_data:
                if inv_data['scope'] not in valid_scopes:
                    self.warnings.append(
                        f"Invariant {inv_key}: unknown scope {inv_data['scope']}"
                    )
            
            # Validate ID format
            if not inv_key.startswith('INV:'):
                self.warnings.append(f"Invariant {inv_key}: ID should start with 'INV:'")
        
        return len([e for e in self.errors if 'Invariant' in e]) == 0
    
    def validate_version_consistency(self) -> bool:
        """
        Validate version consistency and metadata.
        
        For v02:
        - Should have compatibility metadata
        - Should have changelog
        
        Returns:
            bool: True (warnings only, never fails)
            
        Side Effects:
            Adds warnings to self.warnings if recommended fields are missing
        """
        meta = self.data.get('meta', {})
        dict_version = meta.get('dict_version')
        
        if dict_version == 2:
            # v02 should have compatibility info
            if 'compatibility' not in meta:
                self.warnings.append("v02 should have compatibility metadata")
            
            # v02 should have changelog
            if 'changelog' not in meta:
                self.warnings.append("v02 should have changelog")
        
        return True
    
    def run_all_validations(self) -> bool:
        """
        Run all validation checks.
        
        Executes all validation methods in sequence:
        1. Load YAML
        2. Validate structure
        3. Validate metadata
        4. Validate units
        5. Validate gates
        6. Validate invariants
        7. Validate version consistency
        
        Returns:
            bool: True if all validations pass (no errors), False otherwise
            
        Note:
            Warnings do not cause validation to fail
        """
        if not self.load_yaml():
            return False
        
        validations = [
            self.validate_structure(),
            self.validate_meta(),
            self.validate_units(),
            self.validate_gates(),
            self.validate_invariants(),
            self.validate_version_consistency()
        ]
        
        return all(validations)
    
    def report(self):
        """
        Print a formatted validation report.
        
        Displays:
        - File path
        - Errors (if any)
        - Warnings (if any)
        - Overall status
        
        Side Effects:
            Prints report to stdout with colored indicators:
            - ❌ for errors
            - ⚠️ for warnings
            - ✅ for success
        """
        print(f"\n{'='*60}")
        print(f"FractalHub Dictionary Validation Report")
        print(f"File: {self.yaml_path}")
        print(f"{'='*60}\n")
        
        if self.errors:
            print(f"❌ ERRORS ({len(self.errors)}):")
            for error in self.errors:
                print(f"  - {error}")
            print()
        
        if self.warnings:
            print(f"⚠️  WARNINGS ({len(self.warnings)}):")
            for warning in self.warnings:
                print(f"  - {warning}")
            print()
        
        if not self.errors and not self.warnings:
            print("✅ All validations passed!")
        elif not self.errors:
            print("✅ No errors found (warnings only)")
        else:
            print("❌ Validation failed")
        
        print(f"\n{'='*60}\n")


def main():
    """
    Main entry point for the validator script.
    
    Usage:
        python validate_dictionary.py <dictionary.yaml>
    
    Exit Codes:
        0: Validation passed (no errors)
        1: Validation failed (errors found) or usage error
    """
    if len(sys.argv) < 2:
        print("Usage: python validate_dictionary.py <dictionary.yaml>")
        sys.exit(1)
    
    yaml_path = sys.argv[1]
    
    validator = DictionaryValidator(yaml_path)
    success = validator.run_all_validations()
    validator.report()
    
    sys.exit(0 if success and not validator.errors else 1)


if __name__ == "__main__":
    main()
