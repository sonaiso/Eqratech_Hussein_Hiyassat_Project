"""
Tests for FractalHub Dictionary Loading

Tests:
- v01 dictionary loads
- v02 dictionary loads  
- v02 has dict_version=2
- All v01 unit_ids exist in v02 or are mapped
- Backward compatibility flags
- No duplicate IDs
- ID format conventions
- Provenance schema valid
- Gate definitions have ruleset_ids
- Signifier/signified type distinction
"""

import pytest
from pathlib import Path

from fractalhub.data import load_dictionary, DictionaryLoader


class TestDictionaryV01:
    """Test v01 dictionary loading."""
    
    def test_load_v01(self):
        """Test loading v01 dictionary."""
        dict_v01 = load_dictionary(version="v01")
        
        assert dict_v01 is not None
        assert dict_v01.get_version() == 1
    
    def test_v01_has_units(self):
        """Test v01 has units section."""
        dict_v01 = load_dictionary(version="v01")
        
        units = dict_v01.get_all_units()
        assert units is not None
        assert len(units) > 0
    
    def test_v01_get_unit(self):
        """Test getting unit from v01."""
        dict_v01 = load_dictionary(version="v01")
        
        fatha = dict_v01.get_unit("U:DIACRITIC:FATHA")
        assert fatha is not None
        assert fatha.get("status") == "active"


class TestDictionaryV02:
    """Test v02 dictionary loading."""
    
    def test_load_v02(self):
        """Test loading v02 dictionary."""
        dict_v02 = load_dictionary(version="v02")
        
        assert dict_v02 is not None
        assert dict_v02.get_version() == 2
    
    def test_v02_has_meta(self):
        """Test v02 has proper metadata."""
        dict_v02 = load_dictionary(version="v02")
        
        meta = dict_v02.get_meta()
        assert meta is not None
        assert meta["dict_version"] == 2
        assert "codec_version" in meta
        assert "schema_version" in meta
        assert "compatibility" in meta
    
    def test_v02_has_changelog(self):
        """Test v02 has changelog."""
        dict_v02 = load_dictionary(version="v02")
        
        meta = dict_v02.get_meta()
        assert "changelog" in meta
        assert len(meta["changelog"]) > 0
    
    def test_v02_has_provenance_schema(self):
        """Test v02 has provenance schema."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "provenance" in data
        assert "schema" in data["provenance"]
    
    def test_v02_has_lexicon_types(self):
        """Test v02 defines lexicon types."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "lexicon_types" in data
        assert "signifier_only" in data["lexicon_types"]
        assert "signified_entity" in data["lexicon_types"]


class TestDictionaryUnits:
    """Test dictionary units."""
    
    def test_v02_has_diacritics(self):
        """Test v02 has diacritic units."""
        dict_v02 = load_dictionary(version="v02")
        
        fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
        damma = dict_v02.get_unit("U:DIACRITIC:DAMMA")
        kasra = dict_v02.get_unit("U:DIACRITIC:KASRA")
        sukun = dict_v02.get_unit("U:DIACRITIC:SUKUN")
        shadda = dict_v02.get_unit("U:DIACRITIC:SHADDA")
        
        assert fatha is not None
        assert damma is not None
        assert kasra is not None
        assert sukun is not None
        assert shadda is not None
    
    def test_v02_units_have_provenance(self):
        """Test v02 units have provenance."""
        dict_v02 = load_dictionary(version="v02")
        
        fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
        
        assert "provenance" in fatha
        assert "source_type" in fatha["provenance"]
        assert "confidence" in fatha["provenance"]
    
    def test_v02_units_have_bilingual_names(self):
        """Test v02 units have Arabic and English names."""
        dict_v02 = load_dictionary(version="v02")
        
        fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
        
        assert "form" in fatha
        form = fatha["form"]
        # At least one of the bilingual fields should be present
        has_bilingual = (
            "name_ar" in form or 
            "name_en" in form or
            "description_ar" in form or
            "description_en" in form
        )
        assert has_bilingual
    
    def test_v02_has_prosody_markers(self):
        """Test v02 has prosody markers."""
        dict_v02 = load_dictionary(version="v02")
        
        wasl = dict_v02.get_unit("U:PROSODY:WASL")
        waqf = dict_v02.get_unit("U:PROSODY:WAQF")
        
        assert wasl is not None
        assert waqf is not None
        assert wasl["layer"] == "C0"
        assert waqf["layer"] == "C0"
    
    def test_units_are_signifier_only(self):
        """Test phonological units are signifier_only type."""
        dict_v02 = load_dictionary(version="v02")
        
        fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
        
        assert fatha["type"] == "signifier_only"
        assert fatha["layer"] == "C1"
    
    def test_no_duplicate_unit_ids(self):
        """Test no duplicate unit IDs."""
        dict_v02 = load_dictionary(version="v02")
        
        units = dict_v02.get_all_units()
        lexicon_ids = []
        
        for unit_key, unit_data in units.items():
            lexicon_id = unit_data.get("lexicon_id")
            if lexicon_id:
                lexicon_ids.append(lexicon_id)
        
        # Check for duplicates
        assert len(lexicon_ids) == len(set(lexicon_ids))


class TestDictionaryGates:
    """Test dictionary gates."""
    
    def test_v02_has_gates(self):
        """Test v02 has gate definitions."""
        dict_v02 = load_dictionary(version="v02")
        
        gates = dict_v02.get_all_gates()
        assert len(gates) > 0
    
    def test_gates_have_four_conditions(self):
        """Test gates have four conditions defined."""
        dict_v02 = load_dictionary(version="v02")
        
        gate = dict_v02.get_gate("G_C1_CODEC_VERIFY")
        
        assert gate is not None
        assert "four_conditions" in gate
        four_cond = gate["four_conditions"]
        assert "reality" in four_cond
        assert "brain" in four_cond
        assert "sensing" in four_cond
        assert "prior" in four_cond
    
    def test_gates_have_ruleset_ids(self):
        """Test gates have ruleset_ids for evidence."""
        dict_v02 = load_dictionary(version="v02")
        
        gate = dict_v02.get_gate("G_C1_CODEC_VERIFY")
        
        assert "ruleset_ids" in gate
        assert len(gate["ruleset_ids"]) > 0
    
    def test_gates_have_bilingual_descriptions(self):
        """Test gates have Arabic and English descriptions."""
        dict_v02 = load_dictionary(version="v02")
        
        gate = dict_v02.get_gate("G_C1_CODEC_VERIFY")
        
        assert "description_en" in gate
        assert "description_ar" in gate
    
    def test_gates_have_layer(self):
        """Test gates have layer assignment."""
        dict_v02 = load_dictionary(version="v02")
        
        gates = dict_v02.get_all_gates()
        
        for gate_key, gate_data in gates.items():
            assert "layer" in gate_data
            # Layer should be C0, C1, C2, C3, or P1, P2, P3
            layer = gate_data["layer"]
            assert layer in ["C0", "C1", "C2", "C3", "P1", "P2", "P3"]
    
    def test_gate_id_format(self):
        """Test gate IDs follow G_ convention."""
        dict_v02 = load_dictionary(version="v02")
        
        gates = dict_v02.get_all_gates()
        
        for gate_key, gate_data in gates.items():
            gate_id = gate_data.get("gate_id")
            assert gate_id.startswith("G_")
    
    def test_no_duplicate_gate_ids(self):
        """Test no duplicate gate IDs."""
        dict_v02 = load_dictionary(version="v02")
        
        gates = dict_v02.get_all_gates()
        gate_ids = [g.get("gate_id") for g in gates.values()]
        
        # Check for duplicates
        assert len(gate_ids) == len(set(gate_ids))


class TestBackwardCompatibility:
    """Test backward compatibility between v01 and v02."""
    
    def test_v01_units_exist_in_v02(self):
        """Test all v01 units exist in v02."""
        dict_v01 = load_dictionary(version="v01")
        dict_v02 = load_dictionary(version="v02")
        
        v01_units = dict_v01.get_all_units()
        
        for unit_key in v01_units.keys():
            # Try to find in v02 by key or ID
            v02_unit = dict_v02.get_unit(unit_key)
            
            # Should exist (or be mapped)
            assert v02_unit is not None, f"Unit {unit_key} from v01 not found in v02"
    
    def test_compatibility_flag_present(self):
        """Test v02 has compatibility flag."""
        dict_v02 = load_dictionary(version="v02")
        
        meta = dict_v02.get_meta()
        assert "compatibility" in meta
        assert "v01_supported" in meta["compatibility"]
        assert meta["compatibility"]["v01_supported"] is True
    
    def test_no_breaking_changes(self):
        """Test v02 declares no breaking changes."""
        dict_v02 = load_dictionary(version="v02")
        
        meta = dict_v02.get_meta()
        assert meta["compatibility"]["breaking_changes"] is False


class TestIDFormats:
    """Test ID format conventions."""
    
    def test_unit_id_format(self):
        """Test unit IDs follow U: convention."""
        dict_v02 = load_dictionary(version="v02")
        
        units = dict_v02.get_all_units()
        
        for unit_key, unit_data in units.items():
            lexicon_id = unit_data.get("lexicon_id")
            assert lexicon_id.startswith("U:")
    
    def test_gate_id_format(self):
        """Test gate IDs follow G_ convention."""
        dict_v02 = load_dictionary(version="v02")
        
        gates = dict_v02.get_all_gates()
        
        for gate_key, gate_data in gates.items():
            gate_id = gate_data.get("gate_id")
            assert gate_id.startswith("G_")


class TestEpistemicEvidence:
    """Test epistemic evidence levels."""
    
    def test_evidence_levels_defined(self):
        """Test evidence levels are defined."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "evidence" in data
        assert "epistemic_levels" in data["evidence"]
        
        levels = data["evidence"]["epistemic_levels"]
        assert "YAQIN" in levels
        assert "ZANN" in levels
        assert "SHAKK" in levels
    
    def test_evidence_certainty_values(self):
        """Test evidence certainty values."""
        dict_v02 = load_dictionary(version="v02")
        
        levels = dict_v02.data["evidence"]["epistemic_levels"]
        
        assert levels["YAQIN"]["certainty"] == 1.0
        assert levels["ZANN"]["certainty"] == 0.7
        assert levels["SHAKK"]["certainty"] == 0.4
    
    def test_no_meaning_without_evidence_rule(self):
        """Test NO_MEANING_WITHOUT_EVIDENCE rule exists."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "evidence" in data
        assert "anchor_rules" in data["evidence"]
        
        rules = data["evidence"]["anchor_rules"]
        assert "NO_MEANING_WITHOUT_EVIDENCE" in rules
        
        rule = rules["NO_MEANING_WITHOUT_EVIDENCE"]
        assert rule["enforcement"] == "strict"


class TestRepairOperations:
    """Test repair operations schema."""
    
    def test_repair_operations_defined(self):
        """Test repair operations are defined."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "repair_operations" in data
    
    def test_replace_operation(self):
        """Test REPLACE operation exists."""
        dict_v02 = load_dictionary(version="v02")
        
        ops = dict_v02.data["repair_operations"]
        assert "REPLACE" in ops
        
        replace_op = ops["REPLACE"]
        assert replace_op["requires_evidence"] is True


class TestTags:
    """Test tags and categorization."""
    
    def test_tags_defined(self):
        """Test tags are defined."""
        dict_v02 = load_dictionary(version="v02")
        
        data = dict_v02.data
        assert "tags" in data
    
    def test_layer_tags(self):
        """Test layer tags include C0-C3."""
        dict_v02 = load_dictionary(version="v02")
        
        layers = dict_v02.data["tags"]["layers"]
        assert "C0" in layers
        assert "C1" in layers
        assert "C2" in layers
        assert "C3" in layers
