"""
FractalHub Dictionary Loading and Compatibility Tests

Comprehensive test suite for validating the FractalHub dictionary structure,
content, backward compatibility, and data integrity.

Test Categories:
    - TestDictionaryV01: Tests for v01 dictionary (skipped if not present)
    - TestDictionaryV02: Tests for v02 dictionary structure and content
    - TestBackwardCompatibility: Tests for v01/v02 compatibility
    - TestDictionaryStructure: Tests for ID formats and required fields
    - TestDictionaryContent: Tests for content consistency and validation

Usage:
    pytest tests/test_dictionary_load.py -v
    pytest tests/test_dictionary_load.py::TestDictionaryV02 -v
    
Coverage:
    - 26 total test cases
    - Tests load, structure, IDs, compatibility, content
    
Author: Eqratech Arabic Diana Project
Version: 1.0.0
License: MIT
"""

import pytest
import yaml
from pathlib import Path


DICT_DIR = Path(__file__).parent.parent / "fractalhub" / "data"
V01_PATH = DICT_DIR / "fractalhub_dictionary_v01.yaml"
V02_PATH = DICT_DIR / "fractalhub_dictionary_v02.yaml"


def load_dictionary(path: Path):
    """
    Load dictionary YAML file.
    
    Args:
        path (Path): Path to the dictionary YAML file
        
    Returns:
        dict: Parsed dictionary data
        
    Raises:
        FileNotFoundError: If dictionary file doesn't exist
        yaml.YAMLError: If YAML parsing fails
    """
    with open(path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f)


@pytest.fixture
def dict_v01():
    """
    Fixture: Load v01 dictionary.
    
    Yields:
        dict: v01 dictionary data
        
    Skips:
        Test if v01 dictionary file doesn't exist
    """
    if not V01_PATH.exists():
        pytest.skip("v01 dictionary not found")
    return load_dictionary(V01_PATH)


@pytest.fixture
def dict_v02():
    """
    Fixture: Load v02 dictionary.
    
    Yields:
        dict: v02 dictionary data
        
    Skips:
        Test if v02 dictionary file doesn't exist
    """
    if not V02_PATH.exists():
        pytest.skip("v02 dictionary not found")
    return load_dictionary(V02_PATH)


class TestDictionaryV01:
    """
    Tests for v01 dictionary (legacy version).
    
    These tests validate the basic structure and requirements
    for v01 dictionary files. Tests will be skipped if v01
    dictionary doesn't exist.
    """
    
    def test_v01_loads(self, dict_v01):
        """Test that v01 loads successfully"""
        assert dict_v01 is not None
        assert isinstance(dict_v01, dict)
    
    def test_v01_has_required_keys(self, dict_v01):
        """Test that v01 has required top-level keys"""
        required = ['meta', 'units']
        for key in required:
            assert key in dict_v01, f"Missing required key: {key}"


class TestDictionaryV02:
    """
    Tests for v02 dictionary (current version).
    
    Validates:
    - Loading and basic structure
    - Version metadata
    - Required sections presence
    - Diacritics and prosody units
    - Multi-layer gates (C1-C3, P1-P3)
    - Epistemic evidence levels
    - Repair operations
    """
    
    def test_v02_loads(self, dict_v02):
        """Test that v02 loads successfully"""
        assert dict_v02 is not None
        assert isinstance(dict_v02, dict)
    
    def test_v02_version(self, dict_v02):
        """Test that v02 has correct version number"""
        assert 'meta' in dict_v02
        assert 'dict_version' in dict_v02['meta']
        assert dict_v02['meta']['dict_version'] == 2
    
    def test_v02_has_all_sections(self, dict_v02):
        """Test that v02 has all required sections"""
        required = ['meta', 'units', 'gates', 'evidence', 'invariants', 'tags', 'mappings', 'repair_operations']
        for key in required:
            assert key in dict_v02, f"Missing required section: {key}"
    
    def test_v02_has_versioning_metadata(self, dict_v02):
        """Test that v02 has proper versioning metadata"""
        meta = dict_v02['meta']
        assert 'dict_version' in meta
        assert 'schema_version' in meta
        assert 'generated_at' in meta
        assert 'compatibility' in meta
        assert 'changelog' in meta
    
    def test_v02_backward_compatible(self, dict_v02):
        """Test that v02 declares backward compatibility"""
        compat = dict_v02['meta'].get('compatibility', {})
        assert compat.get('v01_supported') is True
    
    def test_v02_has_diacritics(self, dict_v02):
        """Test that v02 includes diacritic units"""
        units = dict_v02.get('units', {})
        diacritic_units = [uid for uid in units.keys() if 'DIACRITIC' in uid]
        assert len(diacritic_units) >= 8, "Should have at least 8 diacritic units"
    
    def test_v02_has_prosody(self, dict_v02):
        """Test that v02 includes prosody units"""
        units = dict_v02.get('units', {})
        prosody_units = [uid for uid in units.keys() if 'PROSODY' in uid]
        assert len(prosody_units) >= 4, "Should have at least 4 prosody units"
    
    def test_v02_has_gates_layers(self, dict_v02):
        """Test that v02 has gates for C1/C2/C3/P layers"""
        gates = dict_v02.get('gates', {})
        layers_found = set()
        for gate_data in gates.values():
            if 'layer' in gate_data:
                layers_found.add(gate_data['layer'])
        
        expected_layers = {'C1', 'C2', 'C3', 'P1', 'P2', 'P3'}
        assert expected_layers.issubset(layers_found), f"Missing layers. Found: {layers_found}"
    
    def test_v02_has_evidence_levels(self, dict_v02):
        """Test that v02 has epistemic evidence levels"""
        evidence = dict_v02.get('evidence', {})
        epistemic = evidence.get('epistemic_levels', {})
        assert 'YAQIN' in epistemic, "Should have YAQIN level"
        assert 'ZANN' in epistemic, "Should have ZANN level"
        assert 'SHAKK' in epistemic, "Should have SHAKK level"
    
    def test_v02_has_repair_operations(self, dict_v02):
        """Test that v02 has repair operation definitions"""
        assert 'repair_operations' in dict_v02
        repair_ops = dict_v02['repair_operations']
        assert 'REPLACE' in repair_ops
        assert 'INSERT_VIRTUAL' in repair_ops
        assert 'DELETE_VIRTUAL' in repair_ops


class TestBackwardCompatibility:
    """
    Tests for backward compatibility between v01 and v02.
    
    Ensures:
    - All v01 unit IDs exist in v02 or are properly mapped
    - No breaking changes declared
    - Smooth migration path from v01 to v02
    """
    
    def test_v01_unit_ids_exist_in_v02(self, dict_v01, dict_v02):
        """Test that all v01 unit IDs exist in v02 or are mapped"""
        if 'units' not in dict_v01:
            pytest.skip("v01 has no units section")
        
        v01_unit_ids = set(dict_v01['units'].keys())
        v02_unit_ids = set(dict_v02['units'].keys())
        mappings = dict_v02.get('mappings', {})
        renames = mappings.get('renames', {})
        
        for unit_id in v01_unit_ids:
            # Either exists in v02 directly or is mapped
            assert (
                unit_id in v02_unit_ids or 
                unit_id in renames
            ), f"Unit {unit_id} from v01 not found in v02 and not mapped"
    
    def test_no_breaking_changes(self, dict_v02):
        """Test that v02 declares no breaking changes"""
        compat = dict_v02['meta'].get('compatibility', {})
        assert compat.get('breaking_changes', True) is False


class TestDictionaryStructure:
    """
    Tests for dictionary structure and ID formats.
    
    Validates:
    - ID format compliance (U:, G:, INV: prefixes)
    - No duplicate IDs across all sections
    - Required fields presence in all entries
    """
    
    def test_unit_ids_format(self, dict_v02):
        """Test that all unit IDs follow U: prefix convention"""
        units = dict_v02.get('units', {})
        for unit_id in units.keys():
            assert unit_id.startswith('U:'), f"Unit ID {unit_id} should start with 'U:'"
    
    def test_gate_ids_format(self, dict_v02):
        """Test that all gate IDs follow G: prefix convention"""
        gates = dict_v02.get('gates', {})
        for gate_id in gates.keys():
            assert gate_id.startswith('G:'), f"Gate ID {gate_id} should start with 'G:'"
    
    def test_invariant_ids_format(self, dict_v02):
        """Test that all invariant IDs follow INV: prefix convention"""
        invariants = dict_v02.get('invariants', {})
        for inv_id in invariants.keys():
            assert inv_id.startswith('INV:'), f"Invariant ID {inv_id} should start with 'INV:'"
    
    def test_no_duplicate_unit_ids(self, dict_v02):
        """Test that there are no duplicate unit IDs"""
        units = dict_v02.get('units', {})
        unit_ids = [unit.get('unit_id') for unit in units.values() if 'unit_id' in unit]
        assert len(unit_ids) == len(set(unit_ids)), "Duplicate unit IDs found"
    
    def test_no_duplicate_gate_ids(self, dict_v02):
        """Test that there are no duplicate gate IDs"""
        gates = dict_v02.get('gates', {})
        gate_ids = [gate.get('gate_id') for gate in gates.values() if 'gate_id' in gate]
        assert len(gate_ids) == len(set(gate_ids)), "Duplicate gate IDs found"
    
    def test_units_have_required_fields(self, dict_v02):
        """Test that all units have required fields"""
        units = dict_v02.get('units', {})
        required_fields = ['unit_id', 'kind', 'status']
        
        for unit_id, unit_data in units.items():
            for field in required_fields:
                assert field in unit_data, f"Unit {unit_id}: missing required field {field}"
    
    def test_gates_have_required_fields(self, dict_v02):
        """Test that all gates have required fields"""
        gates = dict_v02.get('gates', {})
        required_fields = ['gate_id', 'layer', 'inputs', 'outputs', 'status']
        
        for gate_id, gate_data in gates.items():
            for field in required_fields:
                assert field in gate_data, f"Gate {gate_id}: missing required field {field}"
    
    def test_invariants_have_required_fields(self, dict_v02):
        """Test that all invariants have required fields"""
        invariants = dict_v02.get('invariants', {})
        required_fields = ['inv_id', 'scope', 'pattern', 'status']
        
        for inv_id, inv_data in invariants.items():
            for field in required_fields:
                assert field in inv_data, f"Invariant {inv_id}: missing required field {field}"


class TestDictionaryContent:
    """
    Tests for dictionary content and semantics.
    
    Validates:
    - ID consistency (key matches embedded ID field)
    - Valid status values
    - Data integrity and correctness
    """
    
    def test_unit_id_matches_key(self, dict_v02):
        """Test that unit_id field matches the dictionary key"""
        units = dict_v02.get('units', {})
        for key, unit_data in units.items():
            assert unit_data['unit_id'] == key, f"Unit key {key} doesn't match unit_id {unit_data['unit_id']}"
    
    def test_gate_id_matches_key(self, dict_v02):
        """Test that gate_id field matches the dictionary key"""
        gates = dict_v02.get('gates', {})
        for key, gate_data in gates.items():
            assert gate_data['gate_id'] == key, f"Gate key {key} doesn't match gate_id {gate_data['gate_id']}"
    
    def test_invariant_id_matches_key(self, dict_v02):
        """Test that inv_id field matches the dictionary key"""
        invariants = dict_v02.get('invariants', {})
        for key, inv_data in invariants.items():
            assert inv_data['inv_id'] == key, f"Invariant key {key} doesn't match inv_id {inv_data['inv_id']}"
    
    def test_all_units_have_active_status(self, dict_v02):
        """Test that unit statuses are valid"""
        units = dict_v02.get('units', {})
        valid_statuses = ['active', 'deprecated', 'experimental']
        
        for unit_id, unit_data in units.items():
            status = unit_data.get('status')
            assert status in valid_statuses, f"Unit {unit_id}: invalid status {status}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
