"""
Tests for Domain-Specific CTE Gate Extensions
============================================

Tests domain-specific conditions for:
- Language Domain (4 conditions)
- Physics Domain (5 conditions)
- Mathematics Domain (5 conditions)
- Chemistry Domain (5 conditions)
"""

import pytest
from xai_engine.ctegate_domains import (
    Domain, DomainCondition, DomainViolation,
    DomainSpecificGate, evaluate_with_domain
)
from xai_engine.ctegate import GateLevel


class TestLanguageDomain:
    """Test language-specific conditions (L1-L4)"""
    
    def test_no_dialect_variation_pass(self):
        """Test L1: NO_DIALECT_VARIATION passes with standard Arabic"""
        gate = DomainSpecificGate(domain=Domain.LANGUAGE)
        result = gate.evaluate({
            "has_dialect_variation": False,
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert not any(v.domain_condition == DomainCondition.NO_DIALECT_VARIATION 
                      for v in domain_viols)
    
    def test_no_dialect_variation_fail(self):
        """Test L1: Detects dialectal variation"""
        gate = DomainSpecificGate(domain=Domain.LANGUAGE)
        result = gate.evaluate({
            "has_dialect_variation": True,
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_DIALECT_VARIATION 
                  for v in domain_viols)
    
    def test_no_pragmatic_inference_fail(self):
        """Test L3: Detects pragmatic inference requirement"""
        gate = DomainSpecificGate(domain=Domain.LANGUAGE)
        result = gate.evaluate({
            "pragmatic_indicators": ["implicature", "presupposition"],
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_PRAGMATIC_INFERENCE 
                  for v in domain_viols)
        assert result.gate_level in [GateLevel.PROBABLE, GateLevel.POSSIBLE]


class TestPhysicsDomain:
    """Test physics-specific conditions (P1-P5)"""
    
    def test_no_measurement_error_pass(self):
        """Test P1: Passes with low measurement error"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "measurement": {"error_margin": 0.02},  # 2% error
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert not any(v.domain_condition == DomainCondition.NO_MEASUREMENT_ERROR 
                      for v in domain_viols)
    
    def test_no_measurement_error_fail(self):
        """Test P1: Detects high measurement error"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "measurement": {"error_margin": 0.15},  # 15% error
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        error_viol = next((v for v in domain_viols 
                          if v.domain_condition == DomainCondition.NO_MEASUREMENT_ERROR), None)
        assert error_viol is not None
        assert error_viol.severity == "HIGH"
        assert error_viol.quantitative_impact == 0.15
    
    def test_no_unit_ambiguity_fail(self):
        """Test P2: Detects unit ambiguity"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "measurement": {"unit_ambiguity": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_UNIT_AMBIGUITY 
                  for v in domain_viols)
    
    def test_no_experimental_contradiction_fail(self):
        """Test P3: Detects experimental contradiction"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "experimental_conflict": True,
            "measurement": {},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_EXPERIMENTAL_CONTRADICTION 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED
    
    def test_no_observer_dependence_fail(self):
        """Test P4: Detects observer frame dependence"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "measurement": {"observer_dependent": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_OBSERVER_DEPENDENCE 
                  for v in domain_viols)
    
    def test_no_scale_violation_fail(self):
        """Test P5: Detects scale violation"""
        gate = DomainSpecificGate(domain=Domain.PHYSICS)
        result = gate.evaluate({
            "measurement": {"scale_validity": False},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_SCALE_VIOLATION 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED


class TestMathematicsDomain:
    """Test mathematics-specific conditions (M1-M5)"""
    
    def test_no_axiom_violation_pass(self):
        """Test M1: Passes without axiom violation"""
        gate = DomainSpecificGate(domain=Domain.MATHEMATICS)
        result = gate.evaluate({
            "proof": {"axiom_violation": False},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert not any(v.domain_condition == DomainCondition.NO_AXIOM_VIOLATION 
                      for v in domain_viols)
    
    def test_no_axiom_violation_fail(self):
        """Test M1: Detects axiom violation"""
        gate = DomainSpecificGate(domain=Domain.MATHEMATICS)
        result = gate.evaluate({
            "proof": {"axiom_violation": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_AXIOM_VIOLATION 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED
    
    def test_no_proof_gap_complete(self):
        """Test M2: Passes with complete proof"""
        gate = DomainSpecificGate(domain=Domain.MATHEMATICS)
        result = gate.evaluate({
            "proof": {"completeness": 1.0},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert not any(v.domain_condition == DomainCondition.NO_PROOF_GAP 
                      for v in domain_viols)
    
    def test_no_proof_gap_incomplete(self):
        """Test M2: Detects proof gap"""
        gate = DomainSpecificGate(domain=Domain.MATHEMATICS)
        result = gate.evaluate({
            "proof": {"completeness": 0.6},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        gap_viol = next((v for v in domain_viols 
                        if v.domain_condition == DomainCondition.NO_PROOF_GAP), None)
        assert gap_viol is not None
        assert gap_viol.severity == "HIGH"
        assert gap_viol.quantitative_impact == 0.4
    
    def test_no_computational_error_fail(self):
        """Test M5: Detects computational error"""
        gate = DomainSpecificGate(domain=Domain.MATHEMATICS)
        result = gate.evaluate({
            "proof": {"computational_error": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_COMPUTATIONAL_ERROR 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED


class TestChemistryDomain:
    """Test chemistry-specific conditions (C1-C5)"""
    
    def test_no_stoichiometry_error_pass(self):
        """Test C1: Passes with balanced equation"""
        gate = DomainSpecificGate(domain=Domain.CHEMISTRY)
        result = gate.evaluate({
            "reaction": {"balanced": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert not any(v.domain_condition == DomainCondition.NO_STOICHIOMETRY_ERROR 
                      for v in domain_viols)
    
    def test_no_stoichiometry_error_fail(self):
        """Test C1: Detects unbalanced equation"""
        gate = DomainSpecificGate(domain=Domain.CHEMISTRY)
        result = gate.evaluate({
            "reaction": {"balanced": False},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_STOICHIOMETRY_ERROR 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED
    
    def test_no_condition_violation_fail(self):
        """Test C2: Detects missing reaction conditions"""
        gate = DomainSpecificGate(domain=Domain.CHEMISTRY)
        result = gate.evaluate({
            "reaction": {"conditions_specified": False},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_CONDITION_VIOLATION 
                  for v in domain_viols)
    
    def test_no_thermodynamic_impossibility_fail(self):
        """Test C3: Detects thermodynamically impossible reaction"""
        gate = DomainSpecificGate(domain=Domain.CHEMISTRY)
        result = gate.evaluate({
            "reaction": {"thermodynamically_impossible": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        })
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_THERMODYNAMIC_IMPOSSIBILITY 
                  for v in domain_viols)
        assert result.gate_level == GateLevel.REJECTED


class TestDomainSpecificIntegration:
    """Test integration of domain-specific gates"""
    
    def test_language_domain_full_pass(self):
        """Test full pass for language domain"""
        result = evaluate_with_domain({
            "has_dialect_variation": False,
            "has_historical_shift": False,
            "pragmatic_indicators": [],
            "prosodic_ambiguity": False,
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.LANGUAGE)
        
        assert result.gate_level == GateLevel.CERTAIN
        assert result.domain == "language"
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert len(domain_viols) == 0
    
    def test_physics_domain_with_error(self):
        """Test physics domain with measurement error"""
        result = evaluate_with_domain({
            "measurement": {
                "error_margin": 0.08,  # 8% error
                "unit_ambiguity": False
            },
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.PHYSICS)
        
        assert result.gate_level in [GateLevel.PROBABLE, GateLevel.POSSIBLE]
        assert result.domain == "physics"
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_MEASUREMENT_ERROR 
                  for v in domain_viols)
    
    def test_mathematics_domain_incomplete_proof(self):
        """Test mathematics domain with incomplete proof"""
        result = evaluate_with_domain({
            "proof": {
                "completeness": 0.85,
                "axiom_violation": False
            },
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.MATHEMATICS)
        
        assert result.gate_level in [GateLevel.PROBABLE, GateLevel.POSSIBLE]
        assert result.domain == "mathematics"
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_PROOF_GAP 
                  for v in domain_viols)
    
    def test_chemistry_domain_unbalanced(self):
        """Test chemistry domain with unbalanced equation"""
        result = evaluate_with_domain({
            "reaction": {
                "balanced": False,
                "thermodynamically_impossible": False
            },
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.CHEMISTRY)
        
        assert result.gate_level == GateLevel.REJECTED
        assert result.domain == "chemistry"
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert any(v.domain_condition == DomainCondition.NO_STOICHIOMETRY_ERROR 
                  for v in domain_viols)
    
    def test_feature_flag_disabled(self):
        """Test domain checks can be disabled"""
        result = evaluate_with_domain({
            "has_dialect_variation": True,
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.LANGUAGE, feature_flag=False)
        
        # Should use base gate only (no domain checks)
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert len(domain_viols) == 0
    
    def test_score_adjustment_with_domain_violations(self):
        """Test that domain violations adjust score appropriately"""
        # High severity violation
        result_high = evaluate_with_domain({
            "experimental_conflict": True,
            "measurement": {},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.PHYSICS)
        
        # Medium severity violation
        result_medium = evaluate_with_domain({
            "measurement": {"observer_dependent": True},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.PHYSICS)
        
        assert result_high.gate_score < result_medium.gate_score
        assert result_high.gate_level == GateLevel.REJECTED


class TestDomainViolationDetails:
    """Test domain violation details and tracking"""
    
    def test_violation_has_domain_info(self):
        """Test violations include domain information"""
        result = evaluate_with_domain({
            "measurement": {"error_margin": 0.12},
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.PHYSICS)
        
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert len(domain_viols) > 0
        
        viol = domain_viols[0]
        assert viol.domain == Domain.PHYSICS
        assert viol.domain_condition is not None
        assert viol.quantitative_impact is not None
    
    def test_multiple_domain_violations(self):
        """Test handling of multiple domain violations"""
        result = evaluate_with_domain({
            "measurement": {
                "error_margin": 0.10,
                "unit_ambiguity": True,
                "observer_dependent": True
            },
            "semantic_candidates": [],
            "relations": {},
            "operators": [],
            "morphology": {}
        }, domain=Domain.PHYSICS)
        
        domain_viols = [v for v in result.violations if hasattr(v, 'domain_condition')]
        assert len(domain_viols) >= 2  # Multiple physics violations
        
        # Check different conditions detected
        conditions = {v.domain_condition for v in domain_viols}
        assert DomainCondition.NO_MEASUREMENT_ERROR in conditions
        assert DomainCondition.NO_UNIT_AMBIGUITY in conditions


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
