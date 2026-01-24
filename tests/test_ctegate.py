"""
Unit Tests for Constrained Textual Epistemology (CTE) Gate
===========================================================

Tests for the Textual Certainty Gate implementation.
"""

import pytest
from xai_engine.ctegate import (
    TextualCertaintyGate,
    GateLevel,
    GateCondition,
    GateResult,
    ConditionViolation,
    evaluate_textual_certainty,
)


class TestTextualCertaintyGate:
    """Test suite for TextualCertaintyGate"""
    
    def test_gate_initialization(self):
        """Test gate initializes correctly"""
        gate = TextualCertaintyGate()
        assert gate.enabled is True
        assert gate.version == "1.0.0"
        assert len(gate.gate5_conditions) == 5
        assert len(gate.gate10_conditions) == 10
    
    def test_gate_disabled_returns_certain(self):
        """Test that disabled gate returns CERTAIN"""
        gate = TextualCertaintyGate(feature_flag=False)
        result = gate.evaluate({})
        
        assert result.gate_level == GateLevel.CERTAIN
        assert result.gate_score == 1.0
        assert "CTE Gate disabled" in result.trace.get("note", "")
    
    def test_simple_text_passes_gate10(self):
        """Test that simple unambiguous text passes all gates"""
        gate = TextualCertaintyGate()
        
        # Simple text with no ambiguity
        text_analysis = {
            "semantic_candidates": [
                {"form": "محمد", "candidates": [{"meaning": "Muhammad"}], "token_id": "1"}
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        assert result.gate_level == GateLevel.CERTAIN
        assert result.gate_score == 1.0
        assert len(result.violations) == 0
        assert len(result.passed_conditions) == 10
    
    def test_homonymy_fails_gate5(self):
        """Test that homonymy (multiple meanings) fails Gate5"""
        gate = TextualCertaintyGate()
        
        # Text with homonymy (multiple meanings)
        text_analysis = {
            "semantic_candidates": [
                {
                    "form": "عين",
                    "candidates": [
                        {"meaning": "eye"},
                        {"meaning": "spring"},
                        {"meaning": "spy"}
                    ],
                    "token_id": "1"
                }
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should fail Gate5 due to homonymy
        assert result.gate_level in [GateLevel.POSSIBLE, GateLevel.PROBABLE]
        assert result.gate_score < 1.0
        assert len(result.violations) > 0
        
        # Check homonymy violation
        homonymy_violations = [v for v in result.violations 
                               if v.condition == GateCondition.NO_HOMONYMY]
        assert len(homonymy_violations) == 1
        assert homonymy_violations[0].severity == "HIGH"
    
    def test_metaphor_fails_gate5(self):
        """Test that metaphor fails Gate5"""
        gate = TextualCertaintyGate()
        
        # Text with metaphor indicator
        text_analysis = {
            "semantic_candidates": [
                {
                    "form": "أسد",
                    "candidates": [{"meaning": "brave_man"}],
                    "concept_types": ["metaphorical"],
                    "token_id": "1"
                }
            ],
            "relations": {"has_metaphor": True},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should fail Gate5 due to metaphor
        assert result.gate_level != GateLevel.CERTAIN
        assert len(result.violations) > 0
        
        # Check metaphor violation
        metaphor_violations = [v for v in result.violations 
                              if v.condition == GateCondition.NO_METAPHOR]
        assert len(metaphor_violations) >= 1
        assert metaphor_violations[0].severity == "HIGH"
    
    def test_ellipsis_fails_gate5(self):
        """Test that ellipsis (hidden elements) fails Gate5"""
        gate = TextualCertaintyGate()
        
        # Text with ellipsis
        text_analysis = {
            "semantic_candidates": [],
            "relations": {
                "has_ellipsis": True,
                "implicit_elements": ["subject", "verb"]
            },
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should fail Gate5 due to ellipsis
        assert result.gate_level != GateLevel.CERTAIN
        
        ellipsis_violations = [v for v in result.violations 
                              if v.condition == GateCondition.NO_ELLIPSIS]
        assert len(ellipsis_violations) == 1
        assert ellipsis_violations[0].severity == "HIGH"
        assert "2 implicit element(s)" in ellipsis_violations[0].evidence
    
    def test_case_shift_fails_gate10_not_gate5(self):
        """Test that case ambiguity fails Gate10 but may pass Gate5"""
        gate = TextualCertaintyGate()
        
        # Text with case ambiguity (affects Gate10, not Gate5)
        text_analysis = {
            "semantic_candidates": [
                {"form": "الرجل", "candidates": [{"meaning": "the man"}], "token_id": "1"}
            ],
            "relations": {},
            "operators": [
                {"name": "operator_x", "case_dependent": True}
            ],
            "morphology": {"case_ambiguity": True},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should fail Gate10 but potentially pass Gate5
        assert result.gate_level in [GateLevel.PROBABLE, GateLevel.POSSIBLE]
        
        case_violations = [v for v in result.violations 
                          if v.condition == GateCondition.NO_CASE_SHIFT]
        assert len(case_violations) >= 1
        assert case_violations[0].severity == "MEDIUM"
    
    def test_rational_contradiction_rejects(self):
        """Test that rational contradiction results in REJECTED"""
        gate = TextualCertaintyGate()
        
        # Text with logical contradiction
        text_analysis = {
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {},
            "logical_conflict": True,
            "judgment": {"has_contradiction": True}
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should be REJECTED due to contradiction
        assert result.gate_level == GateLevel.REJECTED
        
        contradiction_violations = [v for v in result.violations 
                                   if v.condition == GateCondition.NO_RATIONAL_CONTRADICTION]
        assert len(contradiction_violations) >= 1
        assert contradiction_violations[0].severity == "HIGH"
    
    def test_gate_score_calculation(self):
        """Test that gate score is calculated correctly"""
        gate = TextualCertaintyGate()
        
        # Text with one HIGH severity violation
        text_analysis = {
            "semantic_candidates": [
                {"form": "عين", "candidates": [{"meaning": "eye"}, {"meaning": "spring"}], "token_id": "1"}
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Score should be reduced due to violation
        assert 0.0 <= result.gate_score <= 1.0
        assert result.gate_score < 1.0  # At least one violation
        
        # Score should reflect 9/10 conditions passed minus penalty
        # Expected: 0.9 (9/10) - 0.15 (HIGH penalty) = 0.75
        assert result.gate_score <= 0.9
    
    def test_multiple_violations_accumulate(self):
        """Test that multiple violations accumulate"""
        gate = TextualCertaintyGate()
        
        # Text with multiple violations
        text_analysis = {
            "semantic_candidates": [
                {
                    "form": "عين",
                    "candidates": [{"meaning": "eye"}, {"meaning": "spring"}],
                    "concept_types": ["metaphorical"],
                    "token_id": "1"
                }
            ],
            "relations": {"has_ellipsis": True, "implicit_elements": ["verb"]},
            "operators": [],
            "morphology": {"case_ambiguity": True},
        }
        
        result = gate.evaluate(text_analysis)
        
        # Should have multiple violations
        assert len(result.violations) >= 3
        assert result.gate_level in [GateLevel.POSSIBLE, GateLevel.REJECTED]
        assert result.gate_score < 0.7
    
    def test_human_readable_output(self):
        """Test that human-readable output is generated correctly"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [
                {"form": "test", "candidates": [{"meaning": "test1"}, {"meaning": "test2"}], "token_id": "1"}
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        readable = result.to_human_readable()
        
        # Check output format
        assert "Textual Certainty Gate Result" in readable
        assert "نتيجة بوابة اليقين النصي" in readable
        assert "Gate Level" in readable
        assert "Gate Score" in readable
        assert "Violations" in readable
    
    def test_convenience_function(self):
        """Test convenience function works correctly"""
        text_analysis = {
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = evaluate_textual_certainty(text_analysis)
        
        assert isinstance(result, GateResult)
        assert result.gate_level == GateLevel.CERTAIN
    
    def test_convenience_function_with_feature_flag(self):
        """Test convenience function respects feature flag"""
        text_analysis = {}
        
        # Disabled
        result = evaluate_textual_certainty(text_analysis, feature_flag=False)
        assert result.gate_level == GateLevel.CERTAIN
        assert "disabled" in result.trace.get("note", "")
        
        # Enabled
        result = evaluate_textual_certainty(text_analysis, feature_flag=True)
        assert result.gate_level == GateLevel.CERTAIN
    
    def test_result_to_dict(self):
        """Test GateResult serialization to dict"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        result_dict = result.to_dict()
        
        # Check structure
        assert "gate_level" in result_dict
        assert "gate_score" in result_dict
        assert "violations" in result_dict
        assert "passed_conditions" in result_dict
        assert "timestamp" in result_dict
        assert "trace" in result_dict
        
        # Check types
        assert isinstance(result_dict["gate_score"], float)
        assert isinstance(result_dict["violations"], list)
        assert isinstance(result_dict["passed_conditions"], list)
    
    def test_transfer_detection(self):
        """Test semantic transfer (نقل) detection"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [
                {
                    "form": "word",
                    "candidates": [{"meaning": "transferred"}],
                    "denotation_types": {"transfer": True},
                    "token_id": "1"
                }
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        transfer_violations = [v for v in result.violations 
                              if v.condition == GateCondition.NO_TRANSFER]
        assert len(transfer_violations) == 1
        assert transfer_violations[0].severity == "HIGH"
    
    def test_specification_detection(self):
        """Test specification (تخصيص) detection"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [
                {"form": "all", "candidates": [{"meaning": "all"}], "is_specified": True, "token_id": "1"}
            ],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        spec_violations = [v for v in result.violations 
                          if v.condition == GateCondition.NO_SPECIFICATION]
        assert len(spec_violations) == 1
        assert spec_violations[0].severity == "HIGH"
    
    def test_reordering_detection(self):
        """Test reordering (تقديم وتأخير) detection"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [],
            "relations": {"has_reordering": True, "marked_order": True},
            "operators": [],
            "morphology": {},
        }
        
        result = gate.evaluate(text_analysis)
        
        reorder_violations = [v for v in result.violations 
                             if v.condition == GateCondition.NO_REORDER]
        assert len(reorder_violations) == 1
        assert reorder_violations[0].severity == "MEDIUM"
    
    def test_abrogation_detection(self):
        """Test abrogation (نسخ) detection"""
        gate = TextualCertaintyGate()
        
        text_analysis = {
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {},
        }
        context = {"has_abrogation": True}
        
        result = gate.evaluate(text_analysis, context)
        
        abrogation_violations = [v for v in result.violations 
                                if v.condition == GateCondition.NO_ABROGATION]
        assert len(abrogation_violations) == 1
        assert abrogation_violations[0].severity == "MEDIUM"


class TestConditionViolation:
    """Test ConditionViolation dataclass"""
    
    def test_violation_creation(self):
        """Test creating a violation"""
        violation = ConditionViolation(
            condition=GateCondition.NO_HOMONYMY,
            severity="HIGH",
            evidence="Multiple meanings found",
            location="token_1",
            impact="Reduces certainty"
        )
        
        assert violation.condition == GateCondition.NO_HOMONYMY
        assert violation.severity == "HIGH"
        assert violation.evidence == "Multiple meanings found"
        assert violation.location == "token_1"
        assert violation.impact == "Reduces certainty"
    
    def test_violation_to_dict(self):
        """Test violation serialization"""
        violation = ConditionViolation(
            condition=GateCondition.NO_METAPHOR,
            severity="HIGH",
            evidence="Metaphor detected"
        )
        
        violation_dict = violation.to_dict()
        
        assert violation_dict["condition"] == "no_metaphor"
        assert violation_dict["severity"] == "HIGH"
        assert violation_dict["evidence"] == "Metaphor detected"


class TestGateLevel:
    """Test GateLevel enum"""
    
    def test_gate_levels_exist(self):
        """Test all gate levels are defined"""
        assert GateLevel.CERTAIN.value == "certain"
        assert GateLevel.PROBABLE.value == "probable"
        assert GateLevel.POSSIBLE.value == "possible"
        assert GateLevel.REJECTED.value == "rejected"


class TestGateCondition:
    """Test GateCondition enum"""
    
    def test_all_conditions_defined(self):
        """Test all 10 conditions are defined"""
        conditions = list(GateCondition)
        assert len(conditions) == 10
        
        # Check Gate5 conditions
        assert GateCondition.NO_HOMONYMY in conditions
        assert GateCondition.NO_TRANSFER in conditions
        assert GateCondition.NO_METAPHOR in conditions
        assert GateCondition.NO_ELLIPSIS in conditions
        assert GateCondition.NO_SPECIFICATION in conditions
        
        # Check additional Gate10 conditions
        assert GateCondition.NO_ABROGATION in conditions
        assert GateCondition.NO_REORDER in conditions
        assert GateCondition.NO_CASE_SHIFT in conditions
        assert GateCondition.NO_MORPH_SHIFT in conditions
        assert GateCondition.NO_RATIONAL_CONTRADICTION in conditions


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
