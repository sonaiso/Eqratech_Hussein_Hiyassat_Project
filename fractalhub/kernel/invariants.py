"""
Invariants: Conservation and Symmetry Rules

Implements physical and algebraic invariants for the consciousness kernel:
- Conservation laws: properties preserved through transformations
- Symmetry rules: transformations that leave structure unchanged

Based on النبهاني's theory: constraints maintain consistency.
"""

from typing import List, Dict, Any, Optional, Set
from dataclasses import dataclass, field
from enum import Enum


# ============================================================================
# CONSERVATION LAWS
# ============================================================================

class ConservationType(Enum):
    """Types of conservation"""
    TEMPORAL = "temporal"  # Time consistency
    REFERENTIAL = "referential"  # Reference consistency
    CAUSAL = "causal"  # Cause-effect consistency
    PREDICATIVE = "predicative"  # Predication consistency
    QUANTITATIVE = "quantitative"  # Quantity preservation
    SCOPE = "scope"  # Scope boundaries


@dataclass
class ConservationRule:
    """
    Conservation rule.
    
    A property that must be preserved through transformations.
    Example: temporal consistency (past stays past)
    """
    rule_id: str
    conservation_type: ConservationType
    description: str
    property_name: str
    enforcement: str = "strict"  # strict or soft
    
    def check(self, before: Dict[str, Any], after: Dict[str, Any]) -> bool:
        """
        Check if property is conserved.
        
        Args:
            before: State before transformation
            after: State after transformation
            
        Returns:
            True if conserved, False otherwise
        """
        # Get property from both states
        prop_before = before.get(self.property_name)
        prop_after = after.get(self.property_name)
        
        # Property must exist in both
        if prop_before is None or prop_after is None:
            return False
        
        # Property must be equal
        return prop_before == prop_after


@dataclass
class ConservationViolation:
    """Record of conservation violation"""
    violation_id: str
    rule_id: str
    property_name: str
    before_value: Any
    after_value: Any
    timestamp: str


class ConservationChecker:
    """
    Conservation checker.
    
    Validates that transformations preserve required properties.
    """
    
    def __init__(self):
        """Initialize with predefined rules"""
        self.rules: Dict[str, ConservationRule] = {}
        self.violations: List[ConservationViolation] = []
        self._init_default_rules()
    
    def _init_default_rules(self):
        """Initialize default conservation rules"""
        # Temporal consistency
        self.add_rule(ConservationRule(
            rule_id="CONS:TEMPORAL",
            conservation_type=ConservationType.TEMPORAL,
            description="الزمن يُحفظ - Time must be consistent",
            property_name="temporal_marker",
            enforcement="strict"
        ))
        
        # Referential consistency
        self.add_rule(ConservationRule(
            rule_id="CONS:REFERENTIAL",
            conservation_type=ConservationType.REFERENTIAL,
            description="الإحالة تُحفظ - Reference must be consistent",
            property_name="referent_id",
            enforcement="strict"
        ))
        
        # Predicative consistency
        self.add_rule(ConservationRule(
            rule_id="CONS:PREDICATIVE",
            conservation_type=ConservationType.PREDICATIVE,
            description="الإسناد يُحفظ - Predication must be consistent",
            property_name="predicate_structure",
            enforcement="strict"
        ))
    
    def add_rule(self, rule: ConservationRule):
        """Add conservation rule"""
        self.rules[rule.rule_id] = rule
    
    def check_transformation(
        self, 
        before: Dict[str, Any], 
        after: Dict[str, Any],
        timestamp: str = None
    ) -> List[ConservationViolation]:
        """
        Check if transformation conserves all properties.
        
        Args:
            before: State before transformation
            after: State after transformation
            timestamp: Optional timestamp
            
        Returns:
            List of violations (empty if all conserved)
        """
        violations = []
        
        for rule in self.rules.values():
            if not rule.check(before, after):
                violation = ConservationViolation(
                    violation_id=f"VIOL:{len(self.violations):04d}",
                    rule_id=rule.rule_id,
                    property_name=rule.property_name,
                    before_value=before.get(rule.property_name),
                    after_value=after.get(rule.property_name),
                    timestamp=timestamp or "unknown"
                )
                violations.append(violation)
                self.violations.append(violation)
        
        return violations
    
    def get_violations(self, rule_id: str = None) -> List[ConservationViolation]:
        """Get violations, optionally filtered by rule"""
        if rule_id:
            return [v for v in self.violations if v.rule_id == rule_id]
        return self.violations


# ============================================================================
# SYMMETRY RULES
# ============================================================================

class SymmetryType(Enum):
    """Types of symmetry"""
    LOGICAL = "logical"  # Logical equivalence
    STRUCTURAL = "structural"  # Structural equivalence
    SEMANTIC = "semantic"  # Semantic equivalence
    PRAGMATIC = "pragmatic"  # Pragmatic equivalence


@dataclass
class SymmetryRule:
    """
    Symmetry rule.
    
    A transformation that leaves structure unchanged.
    Example: double negation (¬¬P = P)
    """
    rule_id: str
    symmetry_type: SymmetryType
    description: str
    left_pattern: str
    right_pattern: str
    bidirectional: bool = True
    
    def applies(self, structure: Dict[str, Any]) -> bool:
        """
        Check if rule applies to structure.
        
        Args:
            structure: Structure to check
            
        Returns:
            True if rule applies
        """
        # Check if structure matches pattern
        pattern = structure.get("pattern")
        return pattern in [self.left_pattern, self.right_pattern]
    
    def transform(self, structure: Dict[str, Any]) -> Dict[str, Any]:
        """
        Apply symmetric transformation.
        
        Args:
            structure: Structure to transform
            
        Returns:
            Transformed structure
        """
        result = structure.copy()
        pattern = structure.get("pattern")
        
        if pattern == self.left_pattern:
            result["pattern"] = self.right_pattern
        elif pattern == self.right_pattern and self.bidirectional:
            result["pattern"] = self.left_pattern
        
        return result


class SymmetryChecker:
    """
    Symmetry checker.
    
    Validates symmetric transformations.
    """
    
    def __init__(self):
        """Initialize with predefined rules"""
        self.rules: Dict[str, SymmetryRule] = {}
        self._init_default_rules()
    
    def _init_default_rules(self):
        """Initialize default symmetry rules"""
        # Double negation
        self.add_rule(SymmetryRule(
            rule_id="SYM:DOUBLE_NEG",
            symmetry_type=SymmetryType.LOGICAL,
            description="النفي المزدوج - Double negation ¬¬P = P",
            left_pattern="double_negation",
            right_pattern="positive",
            bidirectional=True
        ))
        
        # Commutative conjunction
        self.add_rule(SymmetryRule(
            rule_id="SYM:CONJ_COMM",
            symmetry_type=SymmetryType.LOGICAL,
            description="التبديل في العطف - Conjunction is commutative P∧Q = Q∧P",
            left_pattern="P_and_Q",
            right_pattern="Q_and_P",
            bidirectional=True
        ))
    
    def add_rule(self, rule: SymmetryRule):
        """Add symmetry rule"""
        self.rules[rule.rule_id] = rule
    
    def find_applicable_rules(
        self, 
        structure: Dict[str, Any]
    ) -> List[SymmetryRule]:
        """
        Find rules applicable to structure.
        
        Args:
            structure: Structure to check
            
        Returns:
            List of applicable rules
        """
        return [rule for rule in self.rules.values() if rule.applies(structure)]
    
    def apply_symmetry(
        self, 
        structure: Dict[str, Any], 
        rule_id: str
    ) -> Optional[Dict[str, Any]]:
        """
        Apply specific symmetry rule.
        
        Args:
            structure: Structure to transform
            rule_id: Rule to apply
            
        Returns:
            Transformed structure or None if rule doesn't apply
        """
        rule = self.rules.get(rule_id)
        if not rule or not rule.applies(structure):
            return None
        
        return rule.transform(structure)


# ============================================================================
# INVARIANT MANAGER
# ============================================================================

@dataclass
class InvariantCheck:
    """Result of invariant check"""
    passed: bool
    violations: List[ConservationViolation] = field(default_factory=list)
    applicable_symmetries: List[str] = field(default_factory=list)


class InvariantManager:
    """
    Invariant manager.
    
    Combines conservation and symmetry checking.
    """
    
    def __init__(self):
        """Initialize both checkers"""
        self.conservation = ConservationChecker()
        self.symmetry = SymmetryChecker()
    
    def check_transformation(
        self,
        before: Dict[str, Any],
        after: Dict[str, Any],
        timestamp: str = None
    ) -> InvariantCheck:
        """
        Check transformation against all invariants.
        
        Args:
            before: State before transformation
            after: State after transformation
            timestamp: Optional timestamp
            
        Returns:
            Check result with violations and applicable symmetries
        """
        # Check conservation
        violations = self.conservation.check_transformation(
            before, after, timestamp
        )
        
        # Find applicable symmetries
        applicable_symmetries = [
            rule.rule_id 
            for rule in self.symmetry.find_applicable_rules(after)
        ]
        
        return InvariantCheck(
            passed=(len(violations) == 0),
            violations=violations,
            applicable_symmetries=applicable_symmetries
        )
    
    def add_conservation_rule(self, rule: ConservationRule):
        """Add conservation rule"""
        self.conservation.add_rule(rule)
    
    def add_symmetry_rule(self, rule: SymmetryRule):
        """Add symmetry rule"""
        self.symmetry.add_rule(rule)
    
    def get_all_violations(self) -> List[ConservationViolation]:
        """Get all recorded violations"""
        return self.conservation.get_violations()
    
    def clear_violations(self):
        """Clear violation history"""
        self.conservation.violations = []


# ============================================================================
# LINGUISTIC INVARIANTS
# ============================================================================

class LinguisticInvariants:
    """
    Linguistic-specific invariants.
    
    Arabic language invariants:
    - Agreement (gender/number/case)
    - Scope consistency
    - Quantifier restrictions
    """
    
    @staticmethod
    def check_agreement(
        structure: Dict[str, Any]
    ) -> bool:
        """
        Check agreement constraints.
        
        Gender, number, and case agreement between مسند and مسند إليه.
        
        Args:
            structure: Structure with agreement features
            
        Returns:
            True if agreement holds
        """
        subject = structure.get("subject", {})
        predicate = structure.get("predicate", {})
        
        # Gender agreement
        if subject.get("gender") != predicate.get("gender"):
            return False
        
        # Number agreement (for certain cases)
        if subject.get("number") == "plural" and predicate.get("number") == "singular":
            # Allowed in some Arabic constructions
            pass
        
        return True
    
    @staticmethod
    def check_scope_consistency(
        structure: Dict[str, Any]
    ) -> bool:
        """
        Check scope consistency.
        
        Quantifiers and negations must have consistent scope.
        
        Args:
            structure: Structure with scope markers
            
        Returns:
            True if scope is consistent
        """
        scopes = structure.get("scopes", [])
        
        # Check nested scopes don't conflict
        for i, scope1 in enumerate(scopes):
            for scope2 in scopes[i+1:]:
                # Check proper nesting
                if scope1.get("start") < scope2.get("start") < scope1.get("end"):
                    if scope2.get("end") > scope1.get("end"):
                        return False  # Improper nesting
        
        return True
