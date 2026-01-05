#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Consciousness Components

Tests the 4 consciousness components:
1. Attention (الانتباه)
2. Memory (الذاكرة)
3. Self-model (نموذج الذات)
4. Affect/Value (القيمة والتأثير)
"""

import unittest
from datetime import datetime

from fractalhub.kernel.consciousness import (
    AttentionState, AttentionScope,
    MemoryStore, MemoryEntry,
    SelfState, Perspective, EpistemicLevel,
    ValueState, ValueDimension,
    ConsciousnessVector,
    gate_attend, gate_memory_write, gate_memory_read
)


class TestAttentionState(unittest.TestCase):
    """Test Attention component"""
    
    def setUp(self):
        self.attention = AttentionState()
    
    def test_set_focus(self):
        """Test setting attention focus"""
        span_ids = ["U:TOKEN:001", "U:TOKEN:002", "U:TOKEN:003"]
        self.attention.set_focus(span_ids, AttentionScope.NARROW)
        
        self.assertEqual(self.attention.focus_span_ids, span_ids)
        self.assertEqual(self.attention.scope, AttentionScope.NARROW)
        self.assertEqual(len(self.attention.history), 1)
    
    def test_expand_focus(self):
        """Test expanding attention focus"""
        initial_ids = ["U:TOKEN:001"]
        self.attention.set_focus(initial_ids)
        
        additional_ids = ["U:TOKEN:002", "U:TOKEN:003"]
        self.attention.expand_focus(additional_ids, AttentionScope.MEDIUM)
        
        self.assertEqual(len(self.attention.focus_span_ids), 3)
        self.assertEqual(self.attention.scope, AttentionScope.MEDIUM)
        self.assertEqual(len(self.attention.history), 2)
    
    def test_is_in_focus(self):
        """Test checking if unit is in focus"""
        span_ids = ["U:TOKEN:001", "U:TOKEN:002"]
        self.attention.set_focus(span_ids)
        
        self.assertTrue(self.attention.is_in_focus("U:TOKEN:001"))
        self.assertTrue(self.attention.is_in_focus("U:TOKEN:002"))
        self.assertFalse(self.attention.is_in_focus("U:TOKEN:003"))
    
    def test_attention_history(self):
        """Test attention history tracking"""
        self.attention.set_focus(["U:TOKEN:001"])
        self.attention.set_focus(["U:TOKEN:002"])
        self.attention.expand_focus(["U:TOKEN:003"])
        
        self.assertEqual(len(self.attention.history), 3)
        self.assertIn("previous_focus", self.attention.history[0])
    
    def test_to_dict(self):
        """Test exporting attention state to dict"""
        self.attention.set_focus(["U:TOKEN:001"], AttentionScope.WIDE)
        result = self.attention.to_dict()
        
        self.assertIn("focus_span_ids", result)
        self.assertIn("scope", result)
        self.assertEqual(result["scope"], "wide")


class TestMemoryStore(unittest.TestCase):
    """Test Memory component"""
    
    def setUp(self):
        self.memory = MemoryStore()
        self.timestamp = datetime.now().isoformat()
    
    def test_write_and_read(self):
        """Test writing and reading from memory"""
        content = {"type": "inference", "conclusion": "test"}
        provenance = {"lexicon_ids": ["LEX:001"], "ruleset_ids": ["RULE:001"]}
        
        commit_id = self.memory.write(
            content=content,
            provenance=provenance,
            entry_type="inference",
            timestamp=self.timestamp
        )
        
        self.assertIsNotNone(commit_id)
        self.assertEqual(len(commit_id), 16)  # SHA256 truncated
        
        entry = self.memory.read(commit_id)
        self.assertIsNotNone(entry)
        self.assertEqual(entry.content, content)
        self.assertEqual(entry.provenance, provenance)
    
    def test_read_nonexistent(self):
        """Test reading non-existent entry"""
        entry = self.memory.read("NONEXISTENT")
        self.assertIsNone(entry)
    
    def test_read_by_type(self):
        """Test reading entries by type"""
        # Write multiple entries
        for i in range(3):
            self.memory.write(
                content={"value": i},
                provenance={"lexicon_ids": [f"LEX:{i}"]},
                entry_type="graph_delta",
                timestamp=self.timestamp
            )
        
        self.memory.write(
            content={"value": 999},
            provenance={"lexicon_ids": ["LEX:999"]},
            entry_type="perception",
            timestamp=self.timestamp
        )
        
        graph_entries = self.memory.read_by_type("graph_delta")
        self.assertEqual(len(graph_entries), 3)
        
        perception_entries = self.memory.read_by_type("perception")
        self.assertEqual(len(perception_entries), 1)
    
    def test_memory_provenance_required(self):
        """Test that provenance is required (enforced by gate)"""
        # Memory store itself doesn't enforce, but gate does
        # This is tested in gate tests
        pass
    
    def test_to_dict(self):
        """Test exporting memory to dict"""
        self.memory.write(
            content={"test": "data"},
            provenance={"lexicon_ids": ["LEX:001"]},
            entry_type="test",
            timestamp=self.timestamp
        )
        
        result = self.memory.to_dict()
        self.assertIn("entry_count", result)
        self.assertIn("types", result)
        self.assertIn("entries", result)
        self.assertEqual(result["entry_count"], 1)


class TestSelfState(unittest.TestCase):
    """Test Self-model component"""
    
    def setUp(self):
        self.self_state = SelfState()
    
    def test_default_state(self):
        """Test default self state"""
        self.assertEqual(self.self_state.perspective, Perspective.THIRD)
        self.assertEqual(self.self_state.epistemic_level, EpistemicLevel.SHAKK)
        self.assertEqual(len(self.self_state.responsibility_scope), 0)
    
    def test_set_perspective(self):
        """Test setting perspective"""
        self.self_state.set_perspective(Perspective.FIRST)
        self.assertEqual(self.self_state.perspective, Perspective.FIRST)
        
        self.self_state.set_perspective(Perspective.SECOND)
        self.assertEqual(self.self_state.perspective, Perspective.SECOND)
    
    def test_set_epistemic_level(self):
        """Test setting epistemic certainty"""
        self.self_state.set_epistemic_level(EpistemicLevel.YAQIN)
        self.assertEqual(self.self_state.epistemic_level, EpistemicLevel.YAQIN)
        self.assertEqual(self.self_state.epistemic_level.certainty, 1.0)
        
        self.self_state.set_epistemic_level(EpistemicLevel.ZANN)
        self.assertEqual(self.self_state.epistemic_level.certainty, 0.7)
    
    def test_add_commitment(self):
        """Test adding commitments"""
        commitment = {
            "type": "assertion",
            "target": "PROP:001",
            "condition": "unconditional"
        }
        
        self.self_state.add_commitment(commitment)
        self.assertEqual(len(self.self_state.commitments), 1)
        self.assertIn("PROP:001", self.self_state.responsibility_scope)
    
    def test_is_responsible_for(self):
        """Test responsibility checking"""
        self.self_state.add_commitment({
            "type": "promise",
            "target": "ACTION:001"
        })
        
        self.assertTrue(self.self_state.is_responsible_for("ACTION:001"))
        self.assertFalse(self.self_state.is_responsible_for("ACTION:002"))
    
    def test_to_dict(self):
        """Test exporting self state to dict"""
        self.self_state.set_perspective(Perspective.FIRST)
        self.self_state.set_epistemic_level(EpistemicLevel.YAQIN)
        
        result = self.self_state.to_dict()
        self.assertEqual(result["perspective"], "first")
        self.assertEqual(result["epistemic_level"], "YAQIN")
        self.assertEqual(result["certainty"], 1.0)


class TestValueState(unittest.TestCase):
    """Test Affect/Value component"""
    
    def setUp(self):
        self.value = ValueState()
    
    def test_default_values(self):
        """Test default value state"""
        for dim in ValueDimension:
            self.assertEqual(self.value.get_value(dim), 0.5)
    
    def test_set_get_value(self):
        """Test setting and getting values"""
        self.value.set_value(ValueDimension.PRIORITY, 0.9)
        self.assertEqual(self.value.get_value(ValueDimension.PRIORITY), 0.9)
        
        self.value.set_value(ValueDimension.THREAT, 0.2)
        self.assertEqual(self.value.get_value(ValueDimension.THREAT), 0.2)
    
    def test_value_bounds(self):
        """Test value bounds validation"""
        with self.assertRaises(ValueError):
            self.value.set_value(ValueDimension.PRIORITY, 1.5)
        
        with self.assertRaises(ValueError):
            self.value.set_value(ValueDimension.THREAT, -0.1)
    
    def test_add_priority(self):
        """Test adding priority for items"""
        self.value.add_priority("ITEM:001", 0.9)
        self.value.add_priority("ITEM:002", 0.7)
        self.value.add_priority("ITEM:003", 0.95)
        
        # Should be sorted by priority
        self.assertEqual(self.value.priorities[0][0], "ITEM:003")
        self.assertEqual(self.value.priorities[0][1], 0.95)
    
    def test_get_priority(self):
        """Test getting priority for item"""
        self.value.add_priority("ITEM:001", 0.8)
        
        priority = self.value.get_priority("ITEM:001")
        self.assertEqual(priority, 0.8)
        
        priority = self.value.get_priority("NONEXISTENT")
        self.assertIsNone(priority)
    
    def test_compute_overall_importance(self):
        """Test computing overall importance"""
        # Set all to 0.5 (default)
        importance = self.value.compute_overall_importance()
        self.assertAlmostEqual(importance, 0.5, places=2)
        
        # Set high priority and threat
        self.value.set_value(ValueDimension.PRIORITY, 1.0)
        self.value.set_value(ValueDimension.THREAT, 1.0)
        importance = self.value.compute_overall_importance()
        self.assertGreater(importance, 0.6)
    
    def test_to_dict(self):
        """Test exporting value state to dict"""
        self.value.set_value(ValueDimension.PRIORITY, 0.8)
        self.value.add_priority("ITEM:001", 0.9)
        
        result = self.value.to_dict()
        self.assertIn("dimensions", result)
        self.assertIn("priorities", result)
        self.assertIn("overall_importance", result)


class TestConsciousnessVector(unittest.TestCase):
    """Test complete consciousness vector"""
    
    def setUp(self):
        self.consciousness = ConsciousnessVector()
    
    def test_initialization(self):
        """Test consciousness vector initialization"""
        self.assertIsNotNone(self.consciousness.attention)
        self.assertIsNotNone(self.consciousness.memory)
        self.assertIsNotNone(self.consciousness.self_state)
        self.assertIsNotNone(self.consciousness.value)
    
    def test_integrated_components(self):
        """Test all components working together"""
        # Set attention
        self.consciousness.attention.set_focus(["U:TOKEN:001"])
        
        # Set self state
        self.consciousness.self_state.set_perspective(Perspective.FIRST)
        self.consciousness.self_state.set_epistemic_level(EpistemicLevel.YAQIN)
        
        # Set value
        self.consciousness.value.set_value(ValueDimension.PRIORITY, 0.9)
        
        # Write to memory
        timestamp = datetime.now().isoformat()
        commit_id = self.consciousness.memory.write(
            content={"test": "integrated"},
            provenance={"lexicon_ids": ["LEX:001"]},
            entry_type="test",
            timestamp=timestamp
        )
        
        # Verify all components
        self.assertTrue(self.consciousness.attention.is_in_focus("U:TOKEN:001"))
        self.assertEqual(self.consciousness.self_state.perspective, Perspective.FIRST)
        self.assertEqual(self.consciousness.value.get_value(ValueDimension.PRIORITY), 0.9)
        self.assertIsNotNone(self.consciousness.memory.read(commit_id))
    
    def test_to_dict(self):
        """Test exporting consciousness vector to dict"""
        result = self.consciousness.to_dict()
        
        self.assertIn("attention", result)
        self.assertIn("memory", result)
        self.assertIn("self", result)
        self.assertIn("value", result)


class TestConsciousnessGates(unittest.TestCase):
    """Test consciousness gates"""
    
    def setUp(self):
        self.consciousness = ConsciousnessVector()
        self.timestamp = datetime.now().isoformat()
    
    def test_gate_attend(self):
        """Test G_ATTEND gate"""
        inputs = {"span_ids": ["U:TOKEN:001", "U:TOKEN:002"]}
        result = gate_attend(inputs, self.consciousness)
        
        self.assertTrue(result["success"])
        self.assertIn("focus_span_ids", result)
        self.assertEqual(len(result["focus_span_ids"]), 2)
        self.assertTrue(self.consciousness.attention.is_in_focus("U:TOKEN:001"))
    
    def test_gate_attend_with_form_stream(self):
        """Test G_ATTEND with form_stream input"""
        inputs = {
            "form_stream": {
                "unit_ids": ["U:TOKEN:003", "U:TOKEN:004"]
            }
        }
        result = gate_attend(inputs, self.consciousness, scope=AttentionScope.WIDE)
        
        self.assertTrue(result["success"])
        self.assertEqual(result["scope"], "wide")
    
    def test_gate_memory_write(self):
        """Test G_MEMORY_WRITE gate"""
        inputs = {
            "content": {"type": "test", "value": 42},
            "provenance": {"lexicon_ids": ["LEX:001"], "ruleset_ids": ["RULE:001"]}
        }
        result = gate_memory_write(inputs, self.consciousness, self.timestamp)
        
        self.assertTrue(result["success"])
        self.assertIn("commit_id", result)
        
        # Verify it was written
        entry = self.consciousness.memory.read(result["commit_id"])
        self.assertIsNotNone(entry)
    
    def test_gate_memory_write_no_provenance(self):
        """Test G_MEMORY_WRITE fails without provenance"""
        inputs = {
            "content": {"type": "test", "value": 42},
            "provenance": {}  # Empty provenance
        }
        result = gate_memory_write(inputs, self.consciousness, self.timestamp)
        
        self.assertFalse(result["success"])
        self.assertEqual(result["error"], "NO_PROVENANCE")
    
    def test_gate_memory_read_by_id(self):
        """Test G_MEMORY_READ by commit_id"""
        # First write something
        write_inputs = {
            "content": {"test": "read_test"},
            "provenance": {"lexicon_ids": ["LEX:001"]}
        }
        write_result = gate_memory_write(write_inputs, self.consciousness, self.timestamp)
        commit_id = write_result["commit_id"]
        
        # Now read it
        read_inputs = {"commit_id": commit_id}
        result = gate_memory_read(read_inputs, self.consciousness)
        
        self.assertTrue(result["success"])
        self.assertIn("entry", result)
        self.assertEqual(result["entry"]["content"]["test"], "read_test")
    
    def test_gate_memory_read_by_type(self):
        """Test G_MEMORY_READ by entry_type"""
        # Write multiple entries
        for i in range(3):
            gate_memory_write(
                {
                    "content": {"value": i},
                    "provenance": {"lexicon_ids": [f"LEX:{i}"]}
                },
                self.consciousness,
                self.timestamp,
                entry_type="test_type"
            )
        
        # Read by type
        read_inputs = {"entry_type": "test_type"}
        result = gate_memory_read(read_inputs, self.consciousness)
        
        self.assertTrue(result["success"])
        self.assertEqual(result["count"], 3)
        self.assertIn("entries", result)
    
    def test_gate_memory_read_invalid_input(self):
        """Test G_MEMORY_READ with invalid input"""
        result = gate_memory_read({}, self.consciousness)
        
        self.assertFalse(result["success"])
        self.assertEqual(result["error"], "INVALID_INPUT")


class TestEpistemicLevels(unittest.TestCase):
    """Test epistemic level enum"""
    
    def test_epistemic_levels(self):
        """Test epistemic level properties"""
        self.assertEqual(EpistemicLevel.YAQIN.certainty, 1.0)
        self.assertEqual(EpistemicLevel.YAQIN.arabic, "اليقين")
        
        self.assertEqual(EpistemicLevel.ZANN.certainty, 0.7)
        self.assertEqual(EpistemicLevel.ZANN.arabic, "الظن")
        
        self.assertEqual(EpistemicLevel.SHAKK.certainty, 0.4)
        self.assertEqual(EpistemicLevel.SHAKK.arabic, "الشك")


if __name__ == "__main__":
    unittest.main()
