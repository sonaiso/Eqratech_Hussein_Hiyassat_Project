# Domain-Specific CTE Gate Extensions

## Overview

This document describes the domain-specific extensions to the Textual Certainty Gate (CTE Gate), adding specialized epistemic validation conditions for four domains:

- **Language Domain (لغوي)**: 4 conditions
- **Physics Domain (فيزيائي)**: 5 conditions  
- **Mathematics Domain (رياضي)**: 5 conditions
- **Chemistry Domain (كيميائي)**: 5 conditions

**Total: 10 core conditions + 19 domain-specific conditions = 29 conditions**

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│              Domain-Specific CTE Gate                       │
│                                                             │
│  ┌───────────────────────────────────────────────────────┐ │
│  │     Core CTE Gate (10 Conditions)                     │ │
│  │  Gate5 + Gate10                                       │ │
│  │  يقين/ظن/احتمال/مرفوض                                 │ │
│  └───────────────────────────────────────────────────────┘ │
│                          +                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │   Domain-Specific Extensions (4-5 per domain)        │ │
│  │                                                       │ │
│  │  Language (4)  │  Physics (5)  │  Math (5)  │ Chem (5)│ │
│  │  L1-L4         │  P1-P5        │  M1-M5     │ C1-C5   │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                             │
│  Result: Enhanced Epistemic Validation with Domain Context │
└─────────────────────────────────────────────────────────────┘
```

## Domain-Specific Conditions

### Language Domain (لغوي) - L1-L4

**L1. NO_DIALECT_VARIATION** (لا تباين لهجي)
- **What it checks**: Ensures no dialectal variation that affects meaning
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال (Probable → Possible)
- **Example violation**: Using Egyptian colloquial "عايز" instead of standard "أريد"

**L2. NO_HISTORICAL_SHIFT** (لا تحول تاريخي)
- **What it checks**: No historical semantic shift in word meaning
- **Severity**: MEDIUM  
- **Impact**: ظن → احتمال
- **Example violation**: Using "الحاسوب" with ancient meaning instead of modern "computer"

**L3. NO_PRAGMATIC_INFERENCE** (لا استنتاج تداولي)
- **What it checks**: No context-dependent pragmatic meaning required
- **Severity**: HIGH
- **Impact**: يقين → ظن (Certain → Probable)
- **Example violation**: "هل يمكنك...؟" as indirect request, not literal question

**L4. NO_PROSODIC_AMBIGUITY** (لا غموض تنغيمي)
- **What it checks**: Meaning not dependent on intonation/stress
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: "أنت ذاهب؟" (question vs. statement depends on intonation)

### Physics Domain (فيزيائي) - P1-P5

**P1. NO_MEASUREMENT_ERROR** (لا خطأ قياس)
- **What it checks**: Measurement within acceptable error bounds (≤5%)
- **Severity**: HIGH if >10%, MEDIUM if 5-10%
- **Impact**: يقين → ظن if error >5%
- **Quantitative**: Tracks error_margin as percentage
- **Example violation**: "الكتلة = 10 kg ± 15%" (15% error)

**P2. NO_UNIT_AMBIGUITY** (لا غموض في الوحدات)
- **What it checks**: Clear and consistent units specified
- **Severity**: HIGH
- **Impact**: يقين → ظن
- **Example violation**: "السرعة = 100" (units not specified)

**P3. NO_EXPERIMENTAL_CONTRADICTION** (لا تعارض تجريبي)
- **What it checks**: No conflict with established experimental evidence
- **Severity**: HIGH
- **Impact**: مرفوض (Rejected)
- **Example violation**: Claiming perpetual motion contradicts thermodynamics

**P4. NO_OBSERVER_DEPENDENCE** (لا اعتماد على المراقب)
- **What it checks**: Observable not observer-frame dependent (where inappropriate)
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: Stating absolute velocity without reference frame

**P5. NO_SCALE_VIOLATION** (لا انتهاك النطاق)
- **What it checks**: Applied within appropriate scale/regime of validity
- **Severity**: HIGH
- **Impact**: مرفوض
- **Example violation**: Using Newtonian mechanics at relativistic speeds

### Mathematics Domain (رياضي) - M1-M5

**M1. NO_AXIOM_VIOLATION** (لا انتهاك للبديهيات)
- **What it checks**: No violation of axiomatic system
- **Severity**: HIGH
- **Impact**: مرفوض (Rejected)
- **Example violation**: Dividing by zero, assuming parallel postulate in non-Euclidean geometry

**M2. NO_PROOF_GAP** (لا فجوة في البرهان)
- **What it checks**: Complete logical chain from premises to conclusion
- **Severity**: HIGH if <70% complete, MEDIUM if 70-99%
- **Impact**: يقين → ظن if incomplete
- **Quantitative**: Tracks completeness percentage
- **Example violation**: "Therefore x=5" without showing intermediate steps

**M3. NO_DOMAIN_RESTRICTION** (لا تقييد المجال)
- **What it checks**: Valid across entire domain of definition
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: "√x is always defined" (only for x≥0)

**M4. NO_NOTATION_AMBIGUITY** (لا غموض في الترميز)
- **What it checks**: Clear mathematical notation
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: Using f(x) for both function and value

**M5. NO_COMPUTATIONAL_ERROR** (لا خطأ حسابي)
- **What it checks**: Verified computation
- **Severity**: HIGH
- **Impact**: مرفوض
- **Example violation**: "2 + 2 = 5"

### Chemistry Domain (كيميائي) - C1-C5

**C1. NO_STOICHIOMETRY_ERROR** (لا خطأ تفاعل كيميائي)
- **What it checks**: Balanced chemical equations (mass and charge conserved)
- **Severity**: HIGH
- **Impact**: مرفوض (Rejected)
- **Example violation**: "H₂ + O₂ → H₂O" (unbalanced)

**C2. NO_CONDITION_VIOLATION** (لا انتهاك الشروط)
- **What it checks**: Reaction conditions clearly specified
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: Not specifying temperature, pressure, catalyst

**C3. NO_THERMODYNAMIC_IMPOSSIBILITY** (لا استحالة ثرموديناميكية)
- **What it checks**: Thermodynamically feasible reaction
- **Severity**: HIGH
- **Impact**: مرفوض
- **Example violation**: Endothermic reaction with ΔG > 0 at stated conditions

**C4. NO_MECHANISM_AMBIGUITY** (لا غموض في الآلية)
- **What it checks**: Clear reaction mechanism
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: Multiple competing pathways without specification

**C5. NO_PHASE_AMBIGUITY** (لا غموض في الحالة)
- **What it checks**: Clear phase specifications (s, l, g, aq)
- **Severity**: MEDIUM
- **Impact**: ظن → احتمال
- **Example violation**: "NaCl → Na + Cl" without phase states

## Usage

### Basic Usage

```python
from xai_engine.ctegate_domains import Domain, evaluate_with_domain

# Evaluate with domain-specific conditions
result = evaluate_with_domain(
    text_analysis,
    domain=Domain.PHYSICS,
    feature_flag=True
)

print(f"Domain: {result.domain}")
print(f"Level: {result.gate_level.value}")
print(f"Score: {result.gate_score:.2f}")
print(f"Domain violations: {len(result.domain_violations)}")
```

### Using DomainSpecificGate Directly

```python
from xai_engine.ctegate_domains import Domain, DomainSpecificGate

# Create domain-specific gate
gate = DomainSpecificGate(domain=Domain.MATHEMATICS)

# Evaluate
result = gate.evaluate(text_analysis)

# Access domain-specific violations
for violation in result.domain_violations:
    print(f"{violation.domain_condition.value}: {violation.evidence}")
    if violation.quantitative_impact:
        print(f"  Impact: {violation.quantitative_impact*100:.1f}%")
```

### Example: Physics Domain

```python
analysis = {
    "statement": "سرعة الجسم = 50 m/s",
    "measurement": {
        "error_margin": 0.08,  # 8% error
        "unit_ambiguity": False,
        "observer_dependent": False,
        "scale_validity": True
    },
    "semantic_candidates": [],
    "relations": {},
    "operators": [],
    "morphology": {}
}

result = evaluate_with_domain(analysis, domain=Domain.PHYSICS)
# Result: PROBABLE (ظن) due to 8% measurement error
```

### Example: Mathematics Domain

```python
analysis = {
    "statement": "Theorem: √2 is irrational",
    "proof": {
        "completeness": 1.0,
        "axiom_violation": False,
        "computational_error": False,
        "domain_restricted": False
    },
    "semantic_candidates": [],
    "relations": {},
    "operators": [],
    "morphology": {}
}

result = evaluate_with_domain(analysis, domain=Domain.MATHEMATICS)
# Result: CERTAIN (يقين) - complete proof, no violations
```

## Integration with XAI Engine

```python
from xai_engine import XAIEngine
from xai_engine.ctegate_domains import evaluate_with_domain, Domain

# Process through XAI Engine
engine = XAIEngine.for_physics()
xai_result = engine.process("F = ma")

# Add domain-specific validation
gate_result = evaluate_with_domain({
    "measurement": xai_result.measurement.to_dict(),
    "semantic_candidates": xai_result.semantic,
    "relations": xai_result.relations.to_dict(),
    "operators": xai_result.measurement.operators,
    "morphology": xai_result.form.morphology
}, domain=Domain.PHYSICS)

# Use combined results
final_confidence = gate_result.gate_score
epistemic_level = gate_result.gate_level.value
```

## Score Calculation

Domain violations apply penalties to the base gate score:

- **HIGH severity**: -0.15 per violation
- **MEDIUM severity**: -0.08 per violation
- **LOW severity**: -0.03 per violation

**Final score** = max(0.0, min(1.0, base_score - penalties))

**Level determination**:
- **CERTAIN** (يقين): score ≥ 0.95
- **PROBABLE** (ظن): 0.70 ≤ score < 0.95
- **POSSIBLE** (احتمال): 0.40 ≤ score < 0.70
- **REJECTED** (مرفوض): score < 0.40

## Feature Flag Control

Domain-specific checks can be disabled:

```python
# Disabled - uses only core gate
result = evaluate_with_domain(
    analysis,
    domain=Domain.LANGUAGE,
    feature_flag=False
)

# Enabled (default)
result = evaluate_with_domain(
    analysis,
    domain=Domain.LANGUAGE,
    feature_flag=True
)
```

## Testing

Run domain-specific tests:

```bash
python -m pytest tests/test_ctegate_domains.py -v
```

Run domain-specific examples:

```bash
python xai_engine/examples_ctegate_domains.py
```

## Files

**Implementation:**
- `xai_engine/ctegate_domains.py` - Domain-specific gate implementation
- `xai_engine/__init__.py` - Exports domain components

**Tests:**
- `tests/test_ctegate_domains.py` - Comprehensive test suite (40+ tests)

**Examples:**
- `xai_engine/examples_ctegate_domains.py` - 9 working examples

**Documentation:**
- `CTE_GATE_DOMAINS_GUIDE.md` - This file

## Summary

✅ **29 total conditions**: 10 core + 19 domain-specific
✅ **4 domains supported**: Language, Physics, Mathematics, Chemistry
✅ **Backward compatible**: Base CTE Gate remains unchanged
✅ **Feature flag control**: Can enable/disable domain checks
✅ **Quantitative tracking**: Numeric impact for measurable violations
✅ **Full integration**: Works seamlessly with XAI Engine
✅ **Production ready**: Complete tests, examples, and documentation

---

**Philosophy:**

```
المعرفة المتخصصة تحتاج تحققًا متخصصًا
Specialized knowledge requires specialized validation

كل مجال له شروطه ومعاييره الخاصة لليقين
Each domain has its own conditions and standards for certainty
```

**Next Steps:**
1. Extend to additional domains (biology, economics, etc.)
2. Add domain-specific metrics and thresholds
3. Integrate with domain-specific XAI Engine configurations
