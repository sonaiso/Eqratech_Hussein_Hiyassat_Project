"""
Domain-Specific Extensions for CTE Gate
========================================

Extends the Textual Certainty Gate with domain-specific conditions for:
- Language Domain (لغوي): Enhanced Arabic linguistic validation
- Physics Domain (فيزيائي): Measurement and experimental validation
- Mathematics Domain (رياضي): Logical proof and axiom validation
- Chemistry Domain (كيميائي): Reaction and stoichiometry validation

Each domain adds specialized conditions on top of the core 10 conditions.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from enum import Enum

from .ctegate import (
    GateLevel, GateCondition, ConditionViolation, 
    GateResult, TextualCertaintyGate
)


class Domain(Enum):
    """
    Supported domains for domain-specific validation
    """
    LANGUAGE = "language"  # لغوي
    PHYSICS = "physics"    # فيزيائي
    MATHEMATICS = "mathematics"  # رياضي
    CHEMISTRY = "chemistry"  # كيميائي


class DomainCondition(Enum):
    """
    Domain-specific gate conditions extending the core 10
    
    Language Domain (لغوي):
    ---------------------
    L1. NO_DIALECT_VARIATION - No dialectal variation affecting meaning
    L2. NO_HISTORICAL_SHIFT - No historical semantic shift
    L3. NO_PRAGMATIC_INFERENCE - No context-dependent pragmatic meaning
    L4. NO_PROSODIC_AMBIGUITY - No intonation-dependent meaning
    
    Physics Domain (فيزيائي):
    ------------------------
    P1. NO_MEASUREMENT_ERROR - Measurement within acceptable error bounds
    P2. NO_UNIT_AMBIGUITY - Clear and consistent units
    P3. NO_EXPERIMENTAL_CONTRADICTION - No conflicting experimental evidence
    P4. NO_OBSERVER_DEPENDENCE - Not observer-frame dependent
    P5. NO_SCALE_VIOLATION - Appropriate scale/regime of validity
    
    Mathematics Domain (رياضي):
    --------------------------
    M1. NO_AXIOM_VIOLATION - No violation of axiomatic system
    M2. NO_PROOF_GAP - Complete logical chain from premises to conclusion
    M3. NO_DOMAIN_RESTRICTION - Valid across entire domain of definition
    M4. NO_NOTATION_AMBIGUITY - Clear mathematical notation
    M5. NO_COMPUTATIONAL_ERROR - Verified computation
    
    Chemistry Domain (كيميائي):
    --------------------------
    C1. NO_STOICHIOMETRY_ERROR - Balanced chemical equations
    C2. NO_CONDITION_VIOLATION - Reaction conditions clearly specified
    C3. NO_THERMODYNAMIC_IMPOSSIBILITY - Thermodynamically feasible
    C4. NO_MECHANISM_AMBIGUITY - Clear reaction mechanism
    C5. NO_PHASE_AMBIGUITY - Clear phase specifications
    """
    # Language Domain (L1-L4)
    NO_DIALECT_VARIATION = "no_dialect_variation"
    NO_HISTORICAL_SHIFT = "no_historical_shift"
    NO_PRAGMATIC_INFERENCE = "no_pragmatic_inference"
    NO_PROSODIC_AMBIGUITY = "no_prosodic_ambiguity"
    
    # Physics Domain (P1-P5)
    NO_MEASUREMENT_ERROR = "no_measurement_error"
    NO_UNIT_AMBIGUITY = "no_unit_ambiguity"
    NO_EXPERIMENTAL_CONTRADICTION = "no_experimental_contradiction"
    NO_OBSERVER_DEPENDENCE = "no_observer_dependence"
    NO_SCALE_VIOLATION = "no_scale_violation"
    
    # Mathematics Domain (M1-M5)
    NO_AXIOM_VIOLATION = "no_axiom_violation"
    NO_PROOF_GAP = "no_proof_gap"
    NO_DOMAIN_RESTRICTION = "no_domain_restriction"
    NO_NOTATION_AMBIGUITY = "no_notation_ambiguity"
    NO_COMPUTATIONAL_ERROR = "no_computational_error"
    
    # Chemistry Domain (C1-C5)
    NO_STOICHIOMETRY_ERROR = "no_stoichiometry_error"
    NO_CONDITION_VIOLATION = "no_condition_violation"
    NO_THERMODYNAMIC_IMPOSSIBILITY = "no_thermodynamic_impossibility"
    NO_MECHANISM_AMBIGUITY = "no_mechanism_ambiguity"
    NO_PHASE_AMBIGUITY = "no_phase_ambiguity"


@dataclass
class DomainViolation(ConditionViolation):
    """
    Extended violation record for domain-specific conditions
    
    Adds domain context and specialized evidence tracking
    """
    domain: Domain = None
    domain_condition: Optional[DomainCondition] = None
    quantitative_impact: Optional[float] = None  # Numeric impact (error %, deviation, etc.)
    

class DomainSpecificGate:
    """
    Domain-Specific CTE Gate
    
    Extends TextualCertaintyGate with domain-specific validation conditions.
    Maintains backward compatibility while adding specialized checks.
    
    Usage:
        >>> gate = DomainSpecificGate(domain=Domain.PHYSICS)
        >>> result = gate.evaluate(text_analysis)
        >>> print(result.gate_level)
        >>> print(result.domain_violations)
    """
    
    def __init__(self, domain: Domain, feature_flag: bool = True):
        """
        Initialize domain-specific gate
        
        Args:
            domain: Target domain for specialized validation
            feature_flag: Enable domain-specific checks (default: True)
        """
        self.domain = domain
        self.feature_flag = feature_flag
        self.base_gate = TextualCertaintyGate(feature_flag=feature_flag)
        
    def evaluate(self, text_analysis: Dict[str, Any]) -> GateResult:
        """
        Evaluate text with both core and domain-specific conditions
        
        Args:
            text_analysis: Analysis result from XAI Engine with domain field
            
        Returns:
            GateResult with both core and domain-specific violations
        """
        # First, run base gate evaluation
        base_result = self.base_gate.evaluate(text_analysis)
        
        # If feature flag disabled, return base result
        if not self.feature_flag:
            return base_result
        
        # Add domain-specific checks
        domain_violations = self._check_domain_specific(text_analysis)
        
        # Combine violations
        all_violations = base_result.violations + domain_violations
        
        # Recalculate score with domain penalties
        adjusted_score = self._calculate_domain_adjusted_score(
            base_result.gate_score, 
            domain_violations
        )
        
        # Determine final gate level
        final_level = self._determine_level_with_domain(
            base_result.gate_level,
            domain_violations,
            adjusted_score
        )
        
        # Create enhanced result with domain information added to trace
        result = GateResult(
            gate_level=final_level,
            gate_score=adjusted_score,
            violations=all_violations,
            passed_conditions=base_result.passed_conditions,
            timestamp=base_result.timestamp,
            trace={
                **base_result.trace,
                "domain": self.domain.value,
                "domain_violations": len(domain_violations),
                "domain_specific_checks": True
            }
        )
        
        # Add domain-specific attributes dynamically
        result.domain = self.domain.value
        result.domain_violations = domain_violations
        
        return result
    
    def _check_domain_specific(self, text_analysis: Dict[str, Any]) -> List[DomainViolation]:
        """Check domain-specific conditions"""
        violations = []
        
        if self.domain == Domain.LANGUAGE:
            violations.extend(self._check_language_domain(text_analysis))
        elif self.domain == Domain.PHYSICS:
            violations.extend(self._check_physics_domain(text_analysis))
        elif self.domain == Domain.MATHEMATICS:
            violations.extend(self._check_mathematics_domain(text_analysis))
        elif self.domain == Domain.CHEMISTRY:
            violations.extend(self._check_chemistry_domain(text_analysis))
        
        return violations
    
    # ===== Language Domain Checks =====
    
    def _check_language_domain(self, analysis: Dict[str, Any]) -> List[DomainViolation]:
        """Check language-specific conditions (L1-L4)"""
        violations = []
        
        # L1: NO_DIALECT_VARIATION
        if analysis.get("has_dialect_variation", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_DIALECT_VARIATION,
                severity="MEDIUM",
                evidence="Dialectal variation detected",
                domain=Domain.LANGUAGE,
                impact="ظن → احتمال: Dialectal forms may have different meanings"
            ))
        
        # L2: NO_HISTORICAL_SHIFT
        if analysis.get("has_historical_shift", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_HISTORICAL_SHIFT,
                severity="MEDIUM",
                evidence="Historical semantic shift detected",
                domain=Domain.LANGUAGE,
                impact="ظن → احتمال: Meaning changed over time"
            ))
        
        # L3: NO_PRAGMATIC_INFERENCE
        pragmatic_indicators = analysis.get("pragmatic_indicators", [])
        if pragmatic_indicators:
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_PRAGMATIC_INFERENCE,
                severity="HIGH",
                evidence=f"Pragmatic inference required: {', '.join(pragmatic_indicators)}",
                domain=Domain.LANGUAGE,
                impact="يقين → ظن: Context-dependent pragmatic meaning"
            ))
        
        # L4: NO_PROSODIC_AMBIGUITY
        if analysis.get("prosodic_ambiguity", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_PROSODIC_AMBIGUITY,
                severity="MEDIUM",
                evidence="Intonation-dependent meaning detected",
                domain=Domain.LANGUAGE,
                impact="ظن → احتمال: Meaning depends on prosody"
            ))
        
        return violations
    
    # ===== Physics Domain Checks =====
    
    def _check_physics_domain(self, analysis: Dict[str, Any]) -> List[DomainViolation]:
        """Check physics-specific conditions (P1-P5)"""
        violations = []
        measurement = analysis.get("measurement", {})
        
        # P1: NO_MEASUREMENT_ERROR
        error_margin = measurement.get("error_margin", 0)
        if error_margin > 0.05:  # >5% error
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_MEASUREMENT_ERROR,
                severity="HIGH" if error_margin > 0.10 else "MEDIUM",
                evidence=f"Measurement error: {error_margin*100:.1f}%",
                domain=Domain.PHYSICS,
                quantitative_impact=error_margin,
                impact=f"يقين → ظن: High measurement uncertainty ({error_margin*100:.1f}%)"
            ))
        
        # P2: NO_UNIT_AMBIGUITY
        if measurement.get("unit_ambiguity", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_UNIT_AMBIGUITY,
                severity="HIGH",
                evidence="Unit system ambiguity detected",
                domain=Domain.PHYSICS,
                impact="يقين → ظن: Unclear measurement units"
            ))
        
        # P3: NO_EXPERIMENTAL_CONTRADICTION
        if analysis.get("experimental_conflict", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_EXPERIMENTAL_CONTRADICTION,
                severity="HIGH",
                evidence="Contradicts established experimental results",
                domain=Domain.PHYSICS,
                impact="مرفوض: Conflicts with experimental evidence"
            ))
        
        # P4: NO_OBSERVER_DEPENDENCE
        if measurement.get("observer_dependent", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_OBSERVER_DEPENDENCE,
                severity="MEDIUM",
                evidence="Observable depends on reference frame",
                domain=Domain.PHYSICS,
                impact="ظن → احتمال: Observer-frame dependent quantity"
            ))
        
        # P5: NO_SCALE_VIOLATION
        scale_validity = measurement.get("scale_validity", True)
        if not scale_validity:
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_SCALE_VIOLATION,
                severity="HIGH",
                evidence="Applied outside valid scale/regime",
                domain=Domain.PHYSICS,
                impact="مرفوض: Invalid in this scale regime"
            ))
        
        return violations
    
    # ===== Mathematics Domain Checks =====
    
    def _check_mathematics_domain(self, analysis: Dict[str, Any]) -> List[DomainViolation]:
        """Check mathematics-specific conditions (M1-M5)"""
        violations = []
        proof = analysis.get("proof", {})
        
        # M1: NO_AXIOM_VIOLATION
        if proof.get("axiom_violation", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_AXIOM_VIOLATION,
                severity="HIGH",
                evidence="Violates axiomatic system",
                domain=Domain.MATHEMATICS,
                impact="مرفوض: Contradicts axioms"
            ))
        
        # M2: NO_PROOF_GAP
        proof_completeness = proof.get("completeness", 1.0)
        if proof_completeness < 1.0:
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_PROOF_GAP,
                severity="HIGH" if proof_completeness < 0.7 else "MEDIUM",
                evidence=f"Proof completeness: {proof_completeness*100:.0f}%",
                domain=Domain.MATHEMATICS,
                quantitative_impact=1.0 - proof_completeness,
                impact=f"يقين → ظن: Incomplete proof ({proof_completeness*100:.0f}%)"
            ))
        
        # M3: NO_DOMAIN_RESTRICTION
        if proof.get("domain_restricted", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_DOMAIN_RESTRICTION,
                severity="MEDIUM",
                evidence="Valid only in restricted domain",
                domain=Domain.MATHEMATICS,
                impact="ظن → احتمال: Limited domain of validity"
            ))
        
        # M4: NO_NOTATION_AMBIGUITY
        if analysis.get("notation_ambiguity", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_NOTATION_AMBIGUITY,
                severity="MEDIUM",
                evidence="Mathematical notation ambiguous",
                domain=Domain.MATHEMATICS,
                impact="ظن → احتمال: Notation requires clarification"
            ))
        
        # M5: NO_COMPUTATIONAL_ERROR
        if proof.get("computational_error", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_COMPUTATIONAL_ERROR,
                severity="HIGH",
                evidence="Computational error detected",
                domain=Domain.MATHEMATICS,
                impact="مرفوض: Incorrect calculation"
            ))
        
        return violations
    
    # ===== Chemistry Domain Checks =====
    
    def _check_chemistry_domain(self, analysis: Dict[str, Any]) -> List[DomainViolation]:
        """Check chemistry-specific conditions (C1-C5)"""
        violations = []
        reaction = analysis.get("reaction", {})
        
        # C1: NO_STOICHIOMETRY_ERROR
        if not reaction.get("balanced", True):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_STOICHIOMETRY_ERROR,
                severity="HIGH",
                evidence="Unbalanced chemical equation",
                domain=Domain.CHEMISTRY,
                impact="مرفوض: Violates conservation laws"
            ))
        
        # C2: NO_CONDITION_VIOLATION
        conditions_specified = reaction.get("conditions_specified", True)
        if not conditions_specified:
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_CONDITION_VIOLATION,
                severity="MEDIUM",
                evidence="Reaction conditions not fully specified",
                domain=Domain.CHEMISTRY,
                impact="ظن → احتمال: Conditions affect outcome"
            ))
        
        # C3: NO_THERMODYNAMIC_IMPOSSIBILITY
        if reaction.get("thermodynamically_impossible", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_THERMODYNAMIC_IMPOSSIBILITY,
                severity="HIGH",
                evidence="Violates thermodynamic principles",
                domain=Domain.CHEMISTRY,
                impact="مرفوض: Thermodynamically forbidden"
            ))
        
        # C4: NO_MECHANISM_AMBIGUITY
        if reaction.get("mechanism_ambiguous", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_MECHANISM_AMBIGUITY,
                severity="MEDIUM",
                evidence="Reaction mechanism unclear",
                domain=Domain.CHEMISTRY,
                impact="ظن → احتمال: Multiple pathways possible"
            ))
        
        # C5: NO_PHASE_AMBIGUITY
        if reaction.get("phase_ambiguous", False):
            violations.append(DomainViolation(
                condition=None,
                domain_condition=DomainCondition.NO_PHASE_AMBIGUITY,
                severity="MEDIUM",
                evidence="Phase specifications unclear",
                domain=Domain.CHEMISTRY,
                impact="ظن → احتمال: Phase state affects reaction"
            ))
        
        return violations
    
    def _calculate_domain_adjusted_score(
        self, 
        base_score: float, 
        domain_violations: List[DomainViolation]
    ) -> float:
        """
        Calculate adjusted score with domain-specific penalties
        
        Penalties:
        - HIGH severity: -0.15 per violation
        - MEDIUM severity: -0.08 per violation  
        - LOW severity: -0.03 per violation
        """
        adjusted_score = base_score
        
        for violation in domain_violations:
            if violation.severity == "HIGH":
                adjusted_score -= 0.15
            elif violation.severity == "MEDIUM":
                adjusted_score -= 0.08
            else:  # LOW
                adjusted_score -= 0.03
        
        return max(0.0, min(1.0, adjusted_score))
    
    def _determine_level_with_domain(
        self,
        base_level: GateLevel,
        domain_violations: List[DomainViolation],
        adjusted_score: float
    ) -> GateLevel:
        """
        Determine final epistemic level considering domain violations
        """
        # Check for critical domain violations
        has_high_severity = any(v.severity == "HIGH" for v in domain_violations)
        
        # If base level already low, maintain it
        if base_level in [GateLevel.REJECTED, GateLevel.POSSIBLE]:
            if has_high_severity:
                return GateLevel.REJECTED
            return base_level
        
        # Downgrade based on score
        if adjusted_score >= 0.95:
            return GateLevel.CERTAIN
        elif adjusted_score >= 0.70:
            return GateLevel.PROBABLE
        elif adjusted_score >= 0.40:
            return GateLevel.POSSIBLE
        else:
            return GateLevel.REJECTED


def evaluate_with_domain(
    text_analysis: Dict[str, Any],
    domain: Domain = Domain.LANGUAGE,
    feature_flag: bool = True
) -> GateResult:
    """
    Convenience function for domain-specific evaluation
    
    Args:
        text_analysis: Analysis result from XAI Engine
        domain: Target domain (default: LANGUAGE)
        feature_flag: Enable domain checks (default: True)
        
    Returns:
        GateResult with domain-specific validation
        
    Example:
        >>> result = evaluate_with_domain(analysis, domain=Domain.PHYSICS)
        >>> print(f"Level: {result.gate_level.value}")
        >>> print(f"Domain: {result.domain}")
        >>> print(f"Domain violations: {len(result.domain_violations)}")
    """
    gate = DomainSpecificGate(domain=domain, feature_flag=feature_flag)
    return gate.evaluate(text_analysis)
