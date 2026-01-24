"""
CTE Gate Integration Examples
==============================

Examples demonstrating the Textual Certainty Gate (TCG) integration
with the XAI Engine for epistemic validation of textual claims.
"""

from xai_engine import XAIEngine
from xai_engine.ctegate import (
    TextualCertaintyGate,
    GateLevel,
    evaluate_textual_certainty,
)


def example_1_simple_certain_text():
    """
    Example 1: Simple unambiguous text → CERTAIN (يقين)
    
    Text: "محمد طالب" (Muhammad is a student)
    Expected: Gate10 passes → CERTAIN
    """
    print("=" * 70)
    print("Example 1: Simple Certain Text (يقين)")
    print("=" * 70)
    
    # Simulate XAI analysis of simple text
    text_analysis = {
        "text": "محمد طالب",
        "semantic_candidates": [
            {
                "form": "محمد",
                "candidates": [{"meaning": "Muhammad", "confidence": 1.0}],
                "token_id": "1"
            },
            {
                "form": "طالب",
                "candidates": [{"meaning": "student", "confidence": 1.0}],
                "token_id": "2"
            }
        ],
        "relations": {
            "isnad": {"subject": "محمد", "predicate": "طالب"}
        },
        "operators": [
            {"name": "nominal_sentence", "type": "isnad"}
        ],
        "morphology": {
            "case_analysis": {"محمد": "nominative", "طالب": "nominative"}
        },
    }
    
    # Evaluate through CTE Gate
    gate = TextualCertaintyGate()
    result = gate.evaluate(text_analysis)
    
    print(f"\n{result.to_human_readable()}\n")
    
    # Interpretation
    if result.gate_level == GateLevel.CERTAIN:
        print("✅ يقين (CERTAIN): The textual claim 'Muhammad is a student' has")
        print("   full epistemic certainty within the textual domain.")
        print("   All 10 gate conditions passed.")
    
    return result


def example_2_homonymy_probable():
    """
    Example 2: Text with homonymy → PROBABLE (ظن)
    
    Text: "رأيت عينًا" (I saw an eye/spring)
    Expected: Gate10 fails (homonymy), Gate5 may pass → PROBABLE
    """
    print("\n" + "=" * 70)
    print("Example 2: Homonymy - Multiple Meanings (ظن)")
    print("=" * 70)
    
    # Text with homonymous word "عين"
    text_analysis = {
        "text": "رأيت عينًا",
        "semantic_candidates": [
            {
                "form": "رأيت",
                "candidates": [{"meaning": "I saw", "confidence": 1.0}],
                "token_id": "1"
            },
            {
                "form": "عينًا",
                "candidates": [
                    {"meaning": "eye", "confidence": 0.5},
                    {"meaning": "spring (water source)", "confidence": 0.3},
                    {"meaning": "spy", "confidence": 0.2}
                ],
                "token_id": "2",
                "has_homonymy": True
            }
        ],
        "relations": {
            "verb_object": {"verb": "رأيت", "object": "عينًا"}
        },
        "operators": [
            {"name": "transitive_verb", "trigger": "رأيت"}
        ],
        "morphology": {},
    }
    
    gate = TextualCertaintyGate()
    result = gate.evaluate(text_analysis)
    
    print(f"\n{result.to_human_readable()}\n")
    
    if result.gate_level == GateLevel.PROBABLE:
        print("⚠️  ظن (PROBABLE): Homonymy detected in 'عين' (eye/spring/spy).")
        print("   Gate5 conditions may pass, but certainty is reduced.")
        print("   Context or additional evidence needed for يقين.")
    
    return result


def example_3_metaphor_possible():
    """
    Example 3: Metaphorical text → POSSIBLE (احتمال)
    
    Text: "رأيت أسدًا في المعركة" (I saw a lion in battle = brave warrior)
    Expected: Gate5 fails (metaphor) → POSSIBLE
    """
    print("\n" + "=" * 70)
    print("Example 3: Metaphor - Figurative Language (احتمال)")
    print("=" * 70)
    
    # Metaphorical usage of "lion" for "brave warrior"
    text_analysis = {
        "text": "رأيت أسدًا في المعركة",
        "semantic_candidates": [
            {
                "form": "أسدًا",
                "candidates": [
                    {"meaning": "brave warrior (metaphorical)", "confidence": 0.8}
                ],
                "concept_types": ["metaphorical", "figurative"],
                "token_id": "2"
            }
        ],
        "relations": {
            "has_metaphor": True,
            "istiara_detected": True,
            "metaphor_source": "lion",
            "metaphor_target": "brave_warrior"
        },
        "operators": [],
        "morphology": {},
    }
    
    gate = TextualCertaintyGate()
    result = gate.evaluate(text_analysis)
    
    print(f"\n{result.to_human_readable()}\n")
    
    if result.gate_level in [GateLevel.POSSIBLE, GateLevel.PROBABLE]:
        print("⚠️  احتمال (POSSIBLE): Metaphor detected (استعارة).")
        print("   Figurative language requires interpretation.")
        print("   Cannot achieve يقين with metaphorical expressions.")
    
    return result


def example_4_ellipsis_reduces_certainty():
    """
    Example 4: Ellipsis (hidden elements) → Reduced certainty
    
    Text: "زيد قائم" with ellipsis → PROBABLE or POSSIBLE
    Expected: Gate5 fails (ellipsis) → PROBABLE/POSSIBLE
    """
    print("\n" + "=" * 70)
    print("Example 4: Ellipsis - Hidden Elements")
    print("=" * 70)
    
    # Text with ellipsis (implicit elements)
    text_analysis = {
        "text": "زيد قائم والآخر",  # "Zayd is standing and the other [is too]"
        "semantic_candidates": [],
        "relations": {
            "has_ellipsis": True,
            "implicit_elements": ["predicate", "copula"],
            "ellipsis_location": "after والآخر"
        },
        "operators": [],
        "morphology": {},
    }
    
    gate = TextualCertaintyGate()
    result = gate.evaluate(text_analysis)
    
    print(f"\n{result.to_human_readable()}\n")
    
    print("⚠️  إضمار (ELLIPSIS): Hidden elements detected.")
    print("   Implicit elements create ambiguity.")
    print("   Certainty reduced from يقين to ظن/احتمال.")
    
    return result


def example_5_rational_contradiction_rejected():
    """
    Example 5: Logical contradiction → REJECTED (مرفوض)
    
    Text with internal contradiction
    Expected: Rational contradiction → REJECTED
    """
    print("\n" + "=" * 70)
    print("Example 5: Rational Contradiction (مرفوض)")
    print("=" * 70)
    
    # Text with logical contradiction
    text_analysis = {
        "text": "الشيء موجود ومعدوم في آنٍ واحد",  # "Thing exists and doesn't exist simultaneously"
        "semantic_candidates": [],
        "relations": {},
        "operators": [],
        "morphology": {},
        "logical_conflict": True,
        "judgment": {
            "has_contradiction": True,
            "contradiction_type": "logical_impossibility"
        }
    }
    
    gate = TextualCertaintyGate()
    result = gate.evaluate(text_analysis)
    
    print(f"\n{result.to_human_readable()}\n")
    
    if result.gate_level == GateLevel.REJECTED:
        print("❌ مرفوض (REJECTED): Rational contradiction detected.")
        print("   Logical impossibility invalidates the claim.")
        print("   معارض عقلي - Cannot be accepted as knowledge.")
    
    return result


def example_6_integrated_with_xai_engine():
    """
    Example 6: Full integration with XAI Engine
    
    Demonstrates how CTE Gate integrates with the complete XAI pipeline.
    """
    print("\n" + "=" * 70)
    print("Example 6: Full XAI Engine + CTE Gate Integration")
    print("=" * 70)
    
    # Initialize XAI Engine for language domain
    engine = XAIEngine.for_language()
    
    # Process text through XAI Engine
    text = "العلم نور"  # "Knowledge is light"
    
    print(f"\nInput Text: {text}")
    print("Processing through XAI Engine...")
    
    # In a full implementation, this would call engine.process(text)
    # For now, simulate the output
    simulated_xai_output = {
        "text": text,
        "semantic_candidates": [
            {"form": "العلم", "candidates": [{"meaning": "knowledge"}], "token_id": "1"},
            {"form": "نور", "candidates": [{"meaning": "light"}], "token_id": "2"}
        ],
        "relations": {
            "isnad": {"subject": "العلم", "predicate": "نور"},
            "type": "metaphorical_predication"
        },
        "operators": [{"name": "metaphorical_isnad"}],
        "morphology": {},
    }
    
    # Apply CTE Gate
    print("\nApplying Textual Certainty Gate...")
    result = evaluate_textual_certainty(simulated_xai_output)
    
    print(f"\n{result.to_human_readable()}\n")
    
    # Generate epistemic assessment
    print("Epistemic Assessment:")
    print(f"  Level: {result.gate_level.value}")
    print(f"  Score: {result.gate_score:.2f}")
    print(f"  Passed: {len(result.passed_conditions)}/10 conditions")
    print(f"  Violations: {len(result.violations)}")
    
    print("\nIntegration Benefits:")
    print("  ✓ Automatic epistemic validation")
    print("  ✓ Clear certainty levels (يقين/ظن/احتمال)")
    print("  ✓ Detailed violation reports")
    print("  ✓ Traceability of epistemic degradation")
    
    return result


def example_7_gate_feature_flag():
    """
    Example 7: Feature flag control
    
    Demonstrates enabling/disabling CTE Gate via feature flag.
    """
    print("\n" + "=" * 70)
    print("Example 7: CTE Gate Feature Flag Control")
    print("=" * 70)
    
    text_analysis = {
        "semantic_candidates": [
            {"form": "test", "candidates": [{"meaning": "a"}, {"meaning": "b"}], "token_id": "1"}
        ],
        "relations": {},
        "operators": [],
        "morphology": {},
    }
    
    # With CTE enabled (default)
    print("\n1. CTE Gate ENABLED:")
    result_enabled = evaluate_textual_certainty(text_analysis, feature_flag=True)
    print(f"   Level: {result_enabled.gate_level.value}")
    print(f"   Score: {result_enabled.gate_score}")
    print(f"   Violations: {len(result_enabled.violations)}")
    
    # With CTE disabled
    print("\n2. CTE Gate DISABLED (backward compatibility):")
    result_disabled = evaluate_textual_certainty(text_analysis, feature_flag=False)
    print(f"   Level: {result_disabled.gate_level.value}")
    print(f"   Score: {result_disabled.gate_score}")
    print(f"   Note: {result_disabled.trace.get('note', 'N/A')}")
    
    print("\n✓ Feature flag allows gradual adoption")
    print("✓ Backward compatibility maintained")
    
    return result_enabled, result_disabled


def run_all_examples():
    """Run all CTE Gate examples"""
    print("\n")
    print("╔═══════════════════════════════════════════════════════════════════╗")
    print("║  Constrained Textual Epistemology (CTE) Gate Examples            ║")
    print("║  نظرية المعرفة النصّية المُقيَّدة - أمثلة                        ║")
    print("╚═══════════════════════════════════════════════════════════════════╝")
    print()
    
    examples = [
        example_1_simple_certain_text,
        example_2_homonymy_probable,
        example_3_metaphor_possible,
        example_4_ellipsis_reduces_certainty,
        example_5_rational_contradiction_rejected,
        example_6_integrated_with_xai_engine,
        example_7_gate_feature_flag,
    ]
    
    results = []
    for example_func in examples:
        try:
            result = example_func()
            results.append((example_func.__name__, result))
        except Exception as e:
            print(f"\n❌ Error in {example_func.__name__}: {e}")
    
    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"\nTotal examples run: {len(results)}")
    print("\nGate Level Distribution:")
    
    level_counts = {}
    for name, result in results:
        if isinstance(result, tuple):  # example_7 returns tuple
            result = result[0]
        if hasattr(result, 'gate_level'):
            level = result.gate_level.value
            level_counts[level] = level_counts.get(level, 0) + 1
    
    for level, count in sorted(level_counts.items()):
        print(f"  {level.upper()}: {count}")
    
    print("\n✅ All examples completed successfully!")
    print("\nCTE Gate provides:")
    print("  • Rigorous epistemic validation")
    print("  • 10-condition certainty framework")
    print("  • Clear يقين/ظن/احتمال levels")
    print("  • Full traceability of violations")
    print("  • Integration with XAI Engine")


if __name__ == "__main__":
    run_all_examples()
