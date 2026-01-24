"""
Constrained Textual Epistemology (CTE) Gate
============================================

Textual Certainty Gate (TCG) implementation for epistemic validation
of textual claims following the CTE framework.

This module implements the 10-condition certainty gate (Gate10) and
the 5-condition probability gate (Gate5) for validating textual knowledge
claims according to Arabic linguistic epistemology.

Theory:
-------
CTE distinguishes between:
- Textual Knowledge (داخل النص): Extractable from utterance structure
- Extra-Textual Knowledge (خارج النص): Requires external evidence

Gate10 ensures يقين (certainty) by checking 10 conditions.
Gate5 ensures ظن (probability) by checking 5 essential conditions.

Usage:
------
    >>> gate = TextualCertaintyGate()
    >>> result = gate.evaluate(text_analysis)
    >>> print(result.gate_level)  # CERTAIN, PROBABLE, or POSSIBLE
    >>> print(result.violations)  # List of violated conditions
"""

from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from enum import Enum
from datetime import datetime


class GateLevel(Enum):
    """
    Epistemic levels enforced by the gate
    
    - CERTAIN (يقين): All 10 conditions passed
    - PROBABLE (ظن): Core 5 conditions passed  
    - POSSIBLE (احتمال): Some conditions passed
    - REJECTED (مرفوض): Critical conditions failed
    """
    CERTAIN = "certain"  # يقين - All Gate10 conditions met
    PROBABLE = "probable"  # ظن - Gate5 conditions met
    POSSIBLE = "possible"  # احتمال - Partial conditions met
    REJECTED = "rejected"  # مرفوض - Critical failures


class GateCondition(Enum):
    """
    10 Gate Conditions for Textual Certainty
    
    Gate5 (Essential):
    ------------------
    1. NO_HOMONYMY - No shared meanings (لا اشتراك)
    2. NO_TRANSFER - No metaphorical transfer (لا نقل)
    3. NO_METAPHOR - No figurative language (لا مجاز)
    4. NO_ELLIPSIS - No hidden elements (لا إضمار)
    5. NO_SPECIFICATION - No restriction of general (لا تخصيص)
    
    Gate10 (Additional 5):
    ----------------------
    6. NO_ABROGATION - No canceled meaning (لا نسخ)
    7. NO_REORDER - No reordering affects meaning (لا تقديم وتأخير)
    8. NO_CASE_SHIFT - No grammatical case change (لا تغيير إعراب)
    9. NO_MORPH_SHIFT - No morphological change (لا تصريف)
    10. NO_RATIONAL_CONTRADICTION - No logical conflict (لا معارض عقلي)
    """
    # Gate5: Essential conditions
    NO_HOMONYMY = "no_homonymy"
    NO_TRANSFER = "no_transfer"
    NO_METAPHOR = "no_metaphor"
    NO_ELLIPSIS = "no_ellipsis"
    NO_SPECIFICATION = "no_specification"
    
    # Gate10: Additional conditions
    NO_ABROGATION = "no_abrogation"
    NO_REORDER = "no_reorder"
    NO_CASE_SHIFT = "no_case_shift"
    NO_MORPH_SHIFT = "no_morph_shift"
    NO_RATIONAL_CONTRADICTION = "no_rational_contradiction"


@dataclass
class ConditionViolation:
    """
    Record of a gate condition violation
    
    Attributes:
        condition: Which condition was violated
        severity: HIGH (blocks Gate5), MEDIUM (blocks Gate10), LOW (reduces score)
        evidence: What triggered the violation
        location: Where in the text
        impact: How it affects epistemic status
    """
    condition: GateCondition
    severity: str  # HIGH, MEDIUM, LOW
    evidence: str
    location: Optional[str] = None
    impact: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "condition": self.condition.value,
            "severity": self.severity,
            "evidence": self.evidence,
            "location": self.location,
            "impact": self.impact,
        }


@dataclass
class GateResult:
    """
    Result of gate evaluation
    
    Attributes:
        gate_level: Final epistemic level (CERTAIN/PROBABLE/POSSIBLE/REJECTED)
        gate_score: Numeric score 0.0-1.0
        violations: List of condition violations
        passed_conditions: Conditions that passed
        timestamp: When evaluation occurred
        trace: Detailed evaluation trace
    """
    gate_level: GateLevel
    gate_score: float  # 0.0 to 1.0
    violations: List[ConditionViolation] = field(default_factory=list)
    passed_conditions: List[GateCondition] = field(default_factory=list)
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    trace: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "gate_level": self.gate_level.value,
            "gate_score": self.gate_score,
            "violations": [v.to_dict() for v in self.violations],
            "passed_conditions": [c.value for c in self.passed_conditions],
            "timestamp": self.timestamp,
            "trace": self.trace,
        }
    
    def to_human_readable(self) -> str:
        """Generate human-readable report (Arabic/English)"""
        arabic_levels = {
            GateLevel.CERTAIN: "يقين",
            GateLevel.PROBABLE: "ظن",
            GateLevel.POSSIBLE: "احتمال",
            GateLevel.REJECTED: "مرفوض",
        }
        
        lines = [
            f"=== Textual Certainty Gate Result / نتيجة بوابة اليقين النصي ===",
            f"",
            f"Gate Level / المستوى: {self.gate_level.value.upper()} ({arabic_levels[self.gate_level]})",
            f"Gate Score / النقاط: {self.gate_score:.2f} / 1.00",
            f"",
            f"Passed Conditions / الشروط المستوفاة: {len(self.passed_conditions)}/10",
            f"Violations / المخالفات: {len(self.violations)}",
        ]
        
        if self.violations:
            lines.append(f"\nViolations Details / تفاصيل المخالفات:")
            for i, v in enumerate(self.violations, 1):
                lines.append(f"  {i}. [{v.severity}] {v.condition.value}")
                lines.append(f"     Evidence / الدليل: {v.evidence}")
                if v.impact:
                    lines.append(f"     Impact / الأثر: {v.impact}")
        
        return "\n".join(lines)


class TextualCertaintyGate:
    """
    Textual Certainty Gate (TCG)
    
    Validates textual claims through 10 epistemic conditions following
    Arabic linguistic epistemology and CTE framework.
    
    Gate Hierarchy:
    ---------------
    - Gate10: All 10 conditions → CERTAIN (يقين)
    - Gate5: First 5 conditions → PROBABLE (ظن)
    - Partial: Some conditions → POSSIBLE (احتمال)
    - Failed: Critical violations → REJECTED (مرفوض)
    
    Usage:
    ------
        gate = TextualCertaintyGate()
        result = gate.evaluate(text_analysis)
        
        if result.gate_level == GateLevel.CERTAIN:
            # Proceed with يقين (certainty)
            pass
        elif result.gate_level == GateLevel.PROBABLE:
            # Proceed with ظن (probability)
            pass
        else:
            # Abstain or reduce confidence
            pass
    """
    
    def __init__(self, feature_flag: bool = True):
        """
        Initialize Textual Certainty Gate
        
        Args:
            feature_flag: Enable/disable CTE mode (default: True)
        """
        self.enabled = feature_flag
        self.version = "1.0.0"
        self.gate5_conditions = [
            GateCondition.NO_HOMONYMY,
            GateCondition.NO_TRANSFER,
            GateCondition.NO_METAPHOR,
            GateCondition.NO_ELLIPSIS,
            GateCondition.NO_SPECIFICATION,
        ]
        self.gate10_conditions = list(GateCondition)
    
    def evaluate(
        self,
        text_analysis: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None
    ) -> GateResult:
        """
        Evaluate text against gate conditions
        
        Args:
            text_analysis: Analysis output from XAI layers containing:
                - tokens: Token analysis
                - semantic_candidates: Meaning candidates
                - relations: Syntactic relations
                - operators: Grammatical operators
                - form: Morphological forms
            context: Optional additional context
            
        Returns:
            GateResult with epistemic level and violations
        """
        if not self.enabled:
            # Feature disabled - return CERTAIN with note
            return GateResult(
                gate_level=GateLevel.CERTAIN,
                gate_score=1.0,
                trace={"note": "CTE Gate disabled"}
            )
        
        violations: List[ConditionViolation] = []
        passed: List[GateCondition] = []
        
        # Check each condition
        for condition in self.gate10_conditions:
            violation = self._check_condition(condition, text_analysis, context)
            if violation:
                violations.append(violation)
            else:
                passed.append(condition)
        
        # Determine gate level
        gate_level = self._determine_gate_level(violations, passed)
        gate_score = self._calculate_score(violations, passed)
        
        return GateResult(
            gate_level=gate_level,
            gate_score=gate_score,
            violations=violations,
            passed_conditions=passed,
            trace={
                "total_conditions": len(self.gate10_conditions),
                "gate5_passed": all(c in passed for c in self.gate5_conditions),
                "gate10_passed": len(violations) == 0,
            }
        )
    
    def _check_condition(
        self,
        condition: GateCondition,
        text_analysis: Dict[str, Any],
        context: Optional[Dict[str, Any]]
    ) -> Optional[ConditionViolation]:
        """
        Check a single gate condition
        
        Returns:
            ConditionViolation if condition failed, None if passed
        """
        # Extract relevant data
        semantic = text_analysis.get("semantic_candidates", [])
        relations = text_analysis.get("relations", {})
        operators = text_analysis.get("operators", [])
        morphology = text_analysis.get("morphology", {})
        
        # Check condition-specific logic
        if condition == GateCondition.NO_HOMONYMY:
            return self._check_no_homonymy(semantic)
        
        elif condition == GateCondition.NO_TRANSFER:
            return self._check_no_transfer(semantic, context)
        
        elif condition == GateCondition.NO_METAPHOR:
            return self._check_no_metaphor(semantic, relations)
        
        elif condition == GateCondition.NO_ELLIPSIS:
            return self._check_no_ellipsis(relations, operators)
        
        elif condition == GateCondition.NO_SPECIFICATION:
            return self._check_no_specification(semantic, context)
        
        elif condition == GateCondition.NO_ABROGATION:
            return self._check_no_abrogation(context)
        
        elif condition == GateCondition.NO_REORDER:
            return self._check_no_reorder(relations)
        
        elif condition == GateCondition.NO_CASE_SHIFT:
            return self._check_no_case_shift(morphology, operators)
        
        elif condition == GateCondition.NO_MORPH_SHIFT:
            return self._check_no_morph_shift(morphology)
        
        elif condition == GateCondition.NO_RATIONAL_CONTRADICTION:
            return self._check_no_rational_contradiction(text_analysis)
        
        return None
    
    # Individual condition checkers
    
    def _check_no_homonymy(self, semantic: List[Any]) -> Optional[ConditionViolation]:
        """Check for homonymy (اشتراك) - multiple unresolved meanings"""
        for item in semantic:
            if isinstance(item, dict):
                candidates = item.get("candidates", [])
                if len(candidates) > 1:
                    # Multiple meanings found
                    return ConditionViolation(
                        condition=GateCondition.NO_HOMONYMY,
                        severity="HIGH",
                        evidence=f"Token '{item.get('form', '')}' has {len(candidates)} meaning candidates",
                        location=item.get("token_id"),
                        impact="يقين → ظن: Multiple meanings require disambiguation"
                    )
        return None
    
    def _check_no_transfer(self, semantic: List[Any], context: Optional[Dict]) -> Optional[ConditionViolation]:
        """Check for semantic transfer (نقل) - word used in non-original sense"""
        for item in semantic:
            if isinstance(item, dict):
                denotation_types = item.get("denotation_types", {})
                if "transfer" in denotation_types or "metaphorical_transfer" in str(denotation_types):
                    return ConditionViolation(
                        condition=GateCondition.NO_TRANSFER,
                        severity="HIGH",
                        evidence=f"Semantic transfer detected in '{item.get('form', '')}'",
                        impact="يقين → ظن: Transferred meaning reduces certainty"
                    )
        return None
    
    def _check_no_metaphor(self, semantic: List[Any], relations: Dict) -> Optional[ConditionViolation]:
        """Check for metaphor (مجاز) - figurative language"""
        # Check for metaphor markers in semantic analysis
        for item in semantic:
            if isinstance(item, dict):
                concept_types = item.get("concept_types", [])
                if "metaphorical" in concept_types or "figurative" in concept_types:
                    return ConditionViolation(
                        condition=GateCondition.NO_METAPHOR,
                        severity="HIGH",
                        evidence=f"Metaphor detected in '{item.get('form', '')}'",
                        impact="يقين → ظن: Metaphorical interpretation reduces certainty"
                    )
        
        # Check relations for metaphorical markers
        if relations.get("has_metaphor", False) or relations.get("istiara_detected", False):
            return ConditionViolation(
                condition=GateCondition.NO_METAPHOR,
                severity="HIGH",
                evidence="Metaphorical relation structure detected",
                impact="يقين → ظن: Metaphorical structure requires interpretation"
            )
        
        return None
    
    def _check_no_ellipsis(self, relations: Dict, operators: List[Any]) -> Optional[ConditionViolation]:
        """Check for ellipsis (إضمار) - hidden/omitted elements"""
        # Check for ellipsis markers
        if relations.get("has_ellipsis", False) or relations.get("implicit_elements", []):
            implicit_count = len(relations.get("implicit_elements", []))
            return ConditionViolation(
                condition=GateCondition.NO_ELLIPSIS,
                severity="HIGH",
                evidence=f"Ellipsis detected: {implicit_count} implicit element(s)",
                impact="يقين → ظن: Hidden elements create ambiguity"
            )
        
        # Check operators for implicit triggers
        for op in operators:
            if isinstance(op, dict) and op.get("has_implicit_scope", False):
                return ConditionViolation(
                    condition=GateCondition.NO_ELLIPSIS,
                    severity="HIGH",
                    evidence=f"Operator '{op.get('name', '')}' has implicit scope",
                    impact="يقين → ظن: Implicit operator scope reduces certainty"
                )
        
        return None
    
    def _check_no_specification(self, semantic: List[Any], context: Optional[Dict]) -> Optional[ConditionViolation]:
        """Check for specification (تخصيص) - restriction of general meaning"""
        # Check for specification markers
        for item in semantic:
            if isinstance(item, dict):
                if item.get("is_specified", False) or item.get("has_restriction", False):
                    return ConditionViolation(
                        condition=GateCondition.NO_SPECIFICATION,
                        severity="HIGH",
                        evidence=f"Specification detected in '{item.get('form', '')}'",
                        impact="يقين → ظن: Restricted meaning requires verification"
                    )
        
        # Check context for specification indicators
        if context and context.get("has_specification", False):
            return ConditionViolation(
                condition=GateCondition.NO_SPECIFICATION,
                severity="HIGH",
                evidence="Contextual specification detected",
                impact="يقين → ظن: General term restricted by context"
            )
        
        return None
    
    def _check_no_abrogation(self, context: Optional[Dict]) -> Optional[ConditionViolation]:
        """Check for abrogation (نسخ) - canceled/superseded meaning"""
        if context and context.get("has_abrogation", False):
            return ConditionViolation(
                condition=GateCondition.NO_ABROGATION,
                severity="MEDIUM",
                evidence="Abrogated meaning detected",
                impact="يقين → ظن: Superseded ruling affects interpretation"
            )
        return None
    
    def _check_no_reorder(self, relations: Dict) -> Optional[ConditionViolation]:
        """Check for reordering (تقديم وتأخير) that affects meaning"""
        if relations.get("has_reordering", False) or relations.get("marked_order", False):
            return ConditionViolation(
                condition=GateCondition.NO_REORDER,
                severity="MEDIUM",
                evidence="Marked word order detected",
                location=relations.get("reorder_location"),
                impact="يقين → ظن: Non-canonical order may affect meaning"
            )
        return None
    
    def _check_no_case_shift(self, morphology: Dict, operators: List[Any]) -> Optional[ConditionViolation]:
        """Check for case shift (تغيير إعراب) that changes meaning"""
        # Check for alternative case analyses
        if morphology.get("case_ambiguity", False):
            return ConditionViolation(
                condition=GateCondition.NO_CASE_SHIFT,
                severity="MEDIUM",
                evidence="Case ambiguity detected",
                impact="يقين → ظن: Alternative case readings possible"
            )
        
        # Check operators for case-sensitive effects
        for op in operators:
            if isinstance(op, dict) and op.get("case_dependent", False):
                return ConditionViolation(
                    condition=GateCondition.NO_CASE_SHIFT,
                    severity="MEDIUM",
                    evidence=f"Case-dependent operator: '{op.get('name', '')}'",
                    impact="يقين → ظن: Meaning depends on case marking"
                )
        
        return None
    
    def _check_no_morph_shift(self, morphology: Dict) -> Optional[ConditionViolation]:
        """Check for morphological variation (تصريف) affecting meaning"""
        if morphology.get("morph_ambiguity", False):
            return ConditionViolation(
                condition=GateCondition.NO_MORPH_SHIFT,
                severity="MEDIUM",
                evidence="Morphological ambiguity detected",
                impact="يقين → ظن: Alternative morphological analyses possible"
            )
        return None
    
    def _check_no_rational_contradiction(self, text_analysis: Dict[str, Any]) -> Optional[ConditionViolation]:
        """Check for rational contradiction (معارض عقلي)"""
        # Check for logical conflicts
        if text_analysis.get("logical_conflict", False):
            return ConditionViolation(
                condition=GateCondition.NO_RATIONAL_CONTRADICTION,
                severity="HIGH",
                evidence="Logical contradiction detected",
                impact="Rejected: Rational contradiction invalidates claim"
            )
        
        # Check judgment layer for conflicts
        judgment = text_analysis.get("judgment", {})
        if judgment.get("has_contradiction", False):
            return ConditionViolation(
                condition=GateCondition.NO_RATIONAL_CONTRADICTION,
                severity="HIGH",
                evidence="Contradiction in judgment",
                impact="Rejected: Internal inconsistency"
            )
        
        return None
    
    def _determine_gate_level(
        self,
        violations: List[ConditionViolation],
        passed: List[GateCondition]
    ) -> GateLevel:
        """Determine final gate level based on violations"""
        # Check for critical violations (HIGH severity)
        high_severity_violations = [v for v in violations if v.severity == "HIGH"]
        
        # REJECTED: Rational contradiction
        if any(v.condition == GateCondition.NO_RATIONAL_CONTRADICTION for v in violations):
            return GateLevel.REJECTED
        
        # CERTAIN: All 10 conditions passed
        if len(violations) == 0:
            return GateLevel.CERTAIN
        
        # PROBABLE: Gate5 (first 5) passed, but Gate10 failed
        gate5_passed = all(c in passed for c in self.gate5_conditions)
        if gate5_passed and len(high_severity_violations) == 0:
            return GateLevel.PROBABLE
        
        # POSSIBLE: Some conditions passed
        if len(passed) >= 3:
            return GateLevel.POSSIBLE
        
        # REJECTED: Too many failures
        return GateLevel.REJECTED
    
    def _calculate_score(
        self,
        violations: List[ConditionViolation],
        passed: List[GateCondition]
    ) -> float:
        """Calculate numeric gate score (0.0-1.0)"""
        total_conditions = len(self.gate10_conditions)
        passed_count = len(passed)
        
        # Base score from passed conditions
        base_score = passed_count / total_conditions
        
        # Penalty for HIGH severity violations
        high_penalty = sum(0.15 for v in violations if v.severity == "HIGH")
        medium_penalty = sum(0.08 for v in violations if v.severity == "MEDIUM")
        low_penalty = sum(0.03 for v in violations if v.severity == "LOW")
        
        final_score = max(0.0, base_score - high_penalty - medium_penalty - low_penalty)
        
        return round(final_score, 2)


# Convenience function for direct usage
def evaluate_textual_certainty(
    text_analysis: Dict[str, Any],
    context: Optional[Dict[str, Any]] = None,
    feature_flag: bool = True
) -> GateResult:
    """
    Convenience function to evaluate textual certainty
    
    Args:
        text_analysis: Analysis output from XAI engine
        context: Optional context information
        feature_flag: Enable/disable CTE mode
        
    Returns:
        GateResult with epistemic assessment
        
    Example:
        >>> result = evaluate_textual_certainty(analysis)
        >>> if result.gate_level == GateLevel.CERTAIN:
        >>>     print("يقين - Certain textual knowledge")
    """
    gate = TextualCertaintyGate(feature_flag=feature_flag)
    return gate.evaluate(text_analysis, context)
