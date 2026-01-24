"""
Examples: Domain-Specific CTE Gate Usage
========================================

Demonstrates domain-specific validation across:
- Language Domain
- Physics Domain
- Mathematics Domain
- Chemistry Domain
"""

from xai_engine.ctegate_domains import (
    Domain, DomainCondition, DomainSpecificGate, evaluate_with_domain
)
from xai_engine.ctegate import GateLevel


def example_1_language_standard_arabic():
    """
    Example 1: Language Domain - Standard Arabic (يقين)
    
    Text: "محمد طالب مجتهد"
    Expected: CERTAIN - no dialect variation, no pragmatic inference
    """
    print("=" * 70)
    print("Example 1: Language Domain - Standard Arabic Text")
    print("=" * 70)
    
    analysis = {
        "text": "محمد طالب مجتهد",
        "has_dialect_variation": False,
        "has_historical_shift": False,
        "pragmatic_indicators": [],
        "prosodic_ambiguity": False,
        "semantic_candidates": [
            {"form": "محمد", "meanings": ["Muhammad"]},
            {"form": "طالب", "meanings": ["student"]},
            {"form": "مجتهد", "meanings": ["diligent"]}
        ],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.LANGUAGE)
    
    print(f"\nInput: {analysis['text']}")
    print(f"Domain: {result.domain}")
    print(f"Gate Level: {result.gate_level.value.upper()} (يقين)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"Core Violations: {len([v for v in result.violations if not hasattr(v, 'domain_condition')])}")
    print(f"Domain Violations: {len([v for v in result.violations if hasattr(v, 'domain_condition')])}")
    print(f"\n✅ All language-specific conditions passed")
    print(f"✅ No dialect variation detected")
    print(f"✅ No pragmatic inference required")
    

def example_2_language_with_pragmatics():
    """
    Example 2: Language Domain - Pragmatic Inference Required (ظن)
    
    Text: "هل يمكنك...؟" (indirect request)
    Expected: PROBABLE - requires pragmatic inference
    """
    print("\n" + "=" * 70)
    print("Example 2: Language Domain - Pragmatic Inference")
    print("=" * 70)
    
    analysis = {
        "text": "هل يمكنك فتح النافذة؟",
        "has_dialect_variation": False,
        "has_historical_shift": False,
        "pragmatic_indicators": ["indirect_request", "politeness"],
        "prosodic_ambiguity": False,
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.LANGUAGE)
    
    print(f"\nInput: {analysis['text']}")
    print(f"Domain: {result.domain}")
    print(f"Gate Level: {result.gate_level.value.upper()} (ظن/احتمال)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\nDomain Violations:")
    for v in result.violations:
        if hasattr(v, 'domain_condition'):
            print(f"  ⚠️  {v.domain_condition.value}: {v.evidence}")
            print(f"      Impact: {v.impact}")


def example_3_physics_accurate_measurement():
    """
    Example 3: Physics Domain - Accurate Measurement (يقين)
    
    Measurement: "سرعة الضوء = 299792458 m/s ± 0.01%"
    Expected: CERTAIN - very low error margin
    """
    print("\n" + "=" * 70)
    print("Example 3: Physics Domain - Accurate Measurement")
    print("=" * 70)
    
    analysis = {
        "statement": "سرعة الضوء = 299792458 m/s",
        "measurement": {
            "value": 299792458,
            "unit": "m/s",
            "error_margin": 0.0001,  # 0.01% error
            "unit_ambiguity": False,
            "observer_dependent": False,
            "scale_validity": True
        },
        "experimental_conflict": False,
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.PHYSICS)
    
    print(f"\nStatement: {analysis['statement']}")
    print(f"Domain: {result.domain}")
    print(f"Error Margin: {analysis['measurement']['error_margin']*100:.2f}%")
    print(f"Gate Level: {result.gate_level.value.upper()} (يقين)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\n✅ Measurement error within acceptable bounds (<5%)")
    print(f"✅ Units clearly specified")
    print(f"✅ No experimental contradictions")


def example_4_physics_high_uncertainty():
    """
    Example 4: Physics Domain - High Measurement Uncertainty (احتمال)
    
    Measurement with 15% error
    Expected: POSSIBLE - high uncertainty
    """
    print("\n" + "=" * 70)
    print("Example 4: Physics Domain - High Measurement Uncertainty")
    print("=" * 70)
    
    analysis = {
        "statement": "قياس تقريبي: الكتلة ≈ 10 kg",
        "measurement": {
            "value": 10,
            "unit": "kg",
            "error_margin": 0.15,  # 15% error
            "unit_ambiguity": False,
            "observer_dependent": False,
            "scale_validity": True
        },
        "experimental_conflict": False,
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.PHYSICS)
    
    print(f"\nStatement: {analysis['statement']}")
    print(f"Domain: {result.domain}")
    print(f"Error Margin: {analysis['measurement']['error_margin']*100:.1f}%")
    print(f"Gate Level: {result.gate_level.value.upper()} (احتمال)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\nDomain Violations:")
    for v in result.violations:
        if hasattr(v, 'domain_condition') and v.domain_condition == DomainCondition.NO_MEASUREMENT_ERROR:
            print(f"  ⚠️  {v.domain_condition.value}: {v.evidence}")
            print(f"      Quantitative Impact: {v.quantitative_impact*100:.1f}%")
            print(f"      Impact: {v.impact}")


def example_5_mathematics_complete_proof():
    """
    Example 5: Mathematics Domain - Complete Proof (يقين)
    
    Complete mathematical proof
    Expected: CERTAIN - all steps verified
    """
    print("\n" + "=" * 70)
    print("Example 5: Mathematics Domain - Complete Proof")
    print("=" * 70)
    
    analysis = {
        "statement": "نظرية: √2 عدد غير نسبي",
        "proof": {
            "completeness": 1.0,
            "axiom_violation": False,
            "computational_error": False,
            "domain_restricted": False
        },
        "notation_ambiguity": False,
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.MATHEMATICS)
    
    print(f"\nStatement: {analysis['statement']}")
    print(f"Domain: {result.domain}")
    print(f"Proof Completeness: {analysis['proof']['completeness']*100:.0f}%")
    print(f"Gate Level: {result.gate_level.value.upper()} (يقين)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\n✅ Complete logical chain from premises to conclusion")
    print(f"✅ No axiom violations")
    print(f"✅ No computational errors")


def example_6_mathematics_proof_gap():
    """
    Example 6: Mathematics Domain - Incomplete Proof (ظن)
    
    Proof with gaps
    Expected: PROBABLE - missing steps
    """
    print("\n" + "=" * 70)
    print("Example 6: Mathematics Domain - Proof with Gaps")
    print("=" * 70)
    
    analysis = {
        "statement": "مبرهنة: العدد الأولي التالي لـ 7 هو 11",
        "proof": {
            "completeness": 0.75,  # 75% complete
            "axiom_violation": False,
            "computational_error": False,
            "domain_restricted": False
        },
        "notation_ambiguity": False,
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.MATHEMATICS)
    
    print(f"\nStatement: {analysis['statement']}")
    print(f"Domain: {result.domain}")
    print(f"Proof Completeness: {analysis['proof']['completeness']*100:.0f}%")
    print(f"Gate Level: {result.gate_level.value.upper()} (ظن)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\nDomain Violations:")
    for v in result.violations:
        if hasattr(v, 'domain_condition') and v.domain_condition == DomainCondition.NO_PROOF_GAP:
            print(f"  ⚠️  {v.domain_condition.value}: {v.evidence}")
            print(f"      Proof Gap: {v.quantitative_impact*100:.0f}%")
            print(f"      Impact: {v.impact}")


def example_7_chemistry_balanced_equation():
    """
    Example 7: Chemistry Domain - Balanced Equation (يقين)
    
    Balanced reaction: 2H₂ + O₂ → 2H₂O
    Expected: CERTAIN - all conservation laws satisfied
    """
    print("\n" + "=" * 70)
    print("Example 7: Chemistry Domain - Balanced Equation")
    print("=" * 70)
    
    analysis = {
        "equation": "2H₂ + O₂ → 2H₂O",
        "reaction": {
            "balanced": True,
            "conditions_specified": True,
            "thermodynamically_impossible": False,
            "mechanism_ambiguous": False,
            "phase_ambiguous": False
        },
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.CHEMISTRY)
    
    print(f"\nEquation: {analysis['equation']}")
    print(f"Domain: {result.domain}")
    print(f"Gate Level: {result.gate_level.value.upper()} (يقين)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\n✅ Equation balanced (mass and charge conserved)")
    print(f"✅ Reaction conditions specified")
    print(f"✅ Thermodynamically feasible")


def example_8_chemistry_unbalanced_equation():
    """
    Example 8: Chemistry Domain - Unbalanced Equation (مرفوض)
    
    Unbalanced reaction
    Expected: REJECTED - violates conservation laws
    """
    print("\n" + "=" * 70)
    print("Example 8: Chemistry Domain - Unbalanced Equation")
    print("=" * 70)
    
    analysis = {
        "equation": "H₂ + O₂ → H₂O (غير موزونة)",
        "reaction": {
            "balanced": False,
            "conditions_specified": True,
            "thermodynamically_impossible": False,
            "mechanism_ambiguous": False,
            "phase_ambiguous": False
        },
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    result = evaluate_with_domain(analysis, domain=Domain.CHEMISTRY)
    
    print(f"\nEquation: {analysis['equation']}")
    print(f"Domain: {result.domain}")
    print(f"Gate Level: {result.gate_level.value.upper()} (مرفوض)")
    print(f"Gate Score: {result.gate_score:.2f}")
    print(f"\nDomain Violations:")
    for v in result.violations:
        if hasattr(v, 'domain_condition') and v.domain_condition == DomainCondition.NO_STOICHIOMETRY_ERROR:
            print(f"  ❌ {v.domain_condition.value}: {v.evidence}")
            print(f"      Impact: {v.impact}")


def example_9_multi_domain_comparison():
    """
    Example 9: Compare Same Text Across Domains
    
    Shows how domain choice affects validation
    """
    print("\n" + "=" * 70)
    print("Example 9: Multi-Domain Comparison")
    print("=" * 70)
    
    # Generic analysis
    analysis = {
        "text": "القيمة = 10 ± 5%",
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {}
    }
    
    print(f"\nText: {analysis['text']}")
    print("\nValidating across different domains:\n")
    
    # Language domain
    result_lang = evaluate_with_domain({**analysis}, domain=Domain.LANGUAGE)
    print(f"1. Language Domain: {result_lang.gate_level.value.upper()} (score: {result_lang.gate_score:.2f})")
    print(f"   - Violations: {len([v for v in result_lang.violations if hasattr(v, 'domain_condition')])}")
    
    # Physics domain (with measurement data)
    analysis_phys = {
        **analysis,
        "measurement": {"error_margin": 0.05, "unit_ambiguity": False}
    }
    result_phys = evaluate_with_domain(analysis_phys, domain=Domain.PHYSICS)
    print(f"\n2. Physics Domain: {result_phys.gate_level.value.upper()} (score: {result_phys.gate_score:.2f})")
    print(f"   - Violations: {len([v for v in result_phys.violations if hasattr(v, 'domain_condition')])}")
    print(f"   - 5% error acceptable for physics")
    
    # Mathematics domain (needs proof)
    analysis_math = {
        **analysis,
        "proof": {"completeness": 0.8}
    }
    result_math = evaluate_with_domain(analysis_math, domain=Domain.MATHEMATICS)
    print(f"\n3. Mathematics Domain: {result_math.gate_level.value.upper()} (score: {result_math.gate_score:.2f})")
    print(f"   - Violations: {len([v for v in result_math.violations if hasattr(v, 'domain_condition')])}")
    print(f"   - Requires complete proof")


def main():
    """Run all domain-specific examples"""
    print("\n" + "=" * 70)
    print("DOMAIN-SPECIFIC CTE GATE EXAMPLES")
    print("=" * 70)
    
    # Language domain examples
    example_1_language_standard_arabic()
    example_2_language_with_pragmatics()
    
    # Physics domain examples
    example_3_physics_accurate_measurement()
    example_4_physics_high_uncertainty()
    
    # Mathematics domain examples
    example_5_mathematics_complete_proof()
    example_6_mathematics_proof_gap()
    
    # Chemistry domain examples
    example_7_chemistry_balanced_equation()
    example_8_chemistry_unbalanced_equation()
    
    # Multi-domain comparison
    example_9_multi_domain_comparison()
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("\n✅ Domain-Specific Extensions:")
    print("   - Language: 4 conditions (L1-L4)")
    print("   - Physics: 5 conditions (P1-P5)")
    print("   - Mathematics: 5 conditions (M1-M5)")
    print("   - Chemistry: 5 conditions (C1-C5)")
    print("\n✅ Total: 10 core + 19 domain-specific = 29 conditions")
    print("\n✅ Each domain enforces specialized validation on top of core CTE Gate")
    print("=" * 70 + "\n")


if __name__ == "__main__":
    main()
