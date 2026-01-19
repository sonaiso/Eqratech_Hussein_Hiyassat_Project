# معايير النشر الأكاديمي | Academic Publication Standards

**For:** Consciousness Kernel v1.2 + FractalHub Dictionary v02 + XAI Engine  
**Version:** 1.0.0  
**Architecture:** locked_v1  
**Date:** January 19, 2026

---

## تمهيد | Preamble

هذا المستند يحدد **نطاق الادعاءات** و**قابلية التفنيد** و**بروتوكول التقييم** للنظام بشكل صارم وقابل للاختبار، مع تجنب الادعاءات المطلقة أو غير القابلة للتحقق.

This document defines the **scope of claims**, **falsifiability**, and **evaluation protocol** for the system in a strict, testable manner, avoiding absolute or unverifiable claims.

---

# القسم (أ): نطاق الادعاءات | Section A: Scope of Claims

## 1. بيان الادعاءات | Claims Statement

### 1.1 الادعاءات المعمارية | Architectural Claims

#### CLAIM-A1: Layer Sequence Enforcement
**النص:** The system enforces sequential processing through 6 layers (Form → Semantic → Relational → Measurement → Judgment → Explanation) without layer skipping.

**المجال:** All domains (language, physics, mathematics, chemistry)

**الطبقات المعنية:** A0-A6 (architectural layers)

**الأدلة المطلوبة:**
- Code inspection showing layer validation
- Runtime checks preventing layer jumps
- Test cases attempting layer jumps and being blocked

**حدود النطاق:**
- ✗ لا يضمن صحة المعالجة داخل كل طبقة
- ✗ Does not guarantee correctness of processing within each layer
- ✗ لا يمنع الأخطاء المنطقية في تصميم الطبقة
- ✗ Does not prevent logical errors in layer design
- ✓ يمنع فقط القفز بين الطبقات
- ✓ Only prevents skipping between layers

**ظروف الفشل المتوقعة:**
- If layer validation code is bypassed
- If layers are called directly without pipeline
- If architectural constraints are removed

---

#### CLAIM-A2: Constraint Enforcement
**النص:** The system enforces 8 architectural constraints at runtime, raising ConstraintViolation exceptions when violated.

**المجال:** All domains

**الطبقات المعنية:** All layers (A0-A6)

**الأدلة المطلوبة:**
- Unit tests for each constraint showing violations are blocked
- Code showing constraint checks at appropriate points
- Exception logs showing constraint violations

**القيود الثمانية:**
1. لا نتيجة بلا قياس - No result without measurement
2. لا تعميم بلا نطاق - No generalization without scope
3. لا حكم بلا علاقة - No judgment without relation
4. لا تفسير بلا سند - No explanation without trace
5. لا قفز بين الطبقات - No layer jumping
6. لا خلط بين المجالات - No domain mixing
7. لا معنى بلا دال - No meaning without form
8. لا قياس بلا عامل - No measurement without operator

**حدود النطاق:**
- ✓ يمنع انتهاكات معمارية محددة
- ✓ Prevents specific architectural violations
- ✗ لا يضمن صحة المحتوى أو المنطق
- ✗ Does not guarantee correctness of content or logic
- ✗ لا يمنع الأخطاء في البيانات المدخلة
- ✗ Does not prevent errors in input data

**ظروف الفشل المتوقعة:**
- If constraint validation is disabled
- If code paths bypass constraint checks
- If constraint logic contains bugs

---

#### CLAIM-A3: Anti-Hallucination Under Locked Rules
**النص (المعدّل):** Under locked architectural rules, the system prevents **specific types of unsupported outputs**: (1) meanings without signifiers, (2) judgments without relational structure, (3) results without measurement traces, (4) explanations without evidence chains.

**المجال:** All domains

**الطبقات المعنية:** A1-A6

**الأدلة المطلوبة:**
- Test cases showing these 4 violation types are blocked
- Code showing enforcement mechanisms
- Failure cases where violations are attempted

**أنواع الهلوسة المُمنوعة:**
1. Floating meanings (معانٍ عائمة) - meanings without signifiers
2. Groundless judgments (أحكام بلا أساس) - judgments without relations
3. Unmeasured results (نتائج غير مقاسة) - results without measurement
4. Unsupported explanations (تفسيرات بلا دليل) - explanations without traces

**أنواع الأخطاء غير المُمنوعة:**
- ✗ معجم خاطئ - Incorrect lexicon entries
- ✗ أدلة غير ذات صلة - Irrelevant evidence
- ✗ غموض دلالي - Semantic ambiguity
- ✗ أخطاء في تطبيق العوامل - Errors in operator application
- ✗ تفسيرات مضللة لكن مدعومة - Misleading but supported explanations
- ✗ أحكام منطقيًا خاطئة لكن معمارياً صحيحة - Logically incorrect but architecturally valid judgments

**حدود النطاق:**
- ✓ يمنع انتهاكات معمارية محددة
- ✓ Prevents specific architectural violations
- ✗ لا يضمن صحة المحتوى الدلالي
- ✗ Does not guarantee semantic correctness
- ✗ لا يمنع الأخطاء المنطقية
- ✗ Does not prevent logical errors

---

### 1.2 الادعاءات المنهجية | Methodological Claims

#### CLAIM-M1: Multi-Domain Consistency
**النص:** The same 6-layer pipeline operates across 4 domains (language, physics, mathematics, chemistry) with domain-specific measurement systems but identical architectural constraints.

**المجال:** Cross-domain

**الطبقات المعنية:** All layers

**الأدلة المطلوبة:**
- Code showing shared pipeline implementation
- Domain-specific configuration for measurement
- Test cases in all 4 domains

**حدود النطاق:**
- ✓ نفس الهيكل المعماري - Same architectural structure
- ✓ قيود موحدة - Unified constraints
- ✗ لا يضمن جودة متساوية عبر المجالات - Does not guarantee equal quality across domains
- ✗ لا يضمن اكتمال التطبيق - Does not guarantee complete implementation

**ظروف الفشل المتوقعة:**
- Incomplete implementation in specific domains
- Domain-specific operators missing
- Verification rules not fully defined

---

#### CLAIM-M2: Traceability Completeness
**النص:** Every judgment produced includes a complete trace showing: (1) input processing through all 6 layers, (2) decisions made at each layer with reasoning, (3) alternatives considered and rejected.

**المجال:** All domains

**الطبقات المعنية:** A0-A6

**الأدلة المطلوبة:**
- Output inspection showing all trace components
- Code showing trace generation at each layer
- Examples with complete traces

**حدود النطاق:**
- ✓ يوثق المسار المعماري - Documents architectural path
- ✓ يسجل القرارات المتخذة - Records decisions made
- ✗ لا يضمن صحة التفسيرات - Does not guarantee correctness of explanations
- ✗ لا يشمل تفاصيل داخلية غير موثقة - Does not include undocumented internal details

---

### 1.3 الادعاءات الأدائية | Performance Claims

#### CLAIM-P1: Processing Latency
**النص:** For simple Arabic sentences (3-5 tokens), processing through all 6 layers completes in <1 second on standard hardware (no GPU required).

**المجال:** Language domain

**الطبقات المعنية:** All layers

**الأدلة المطلوبة:**
- Timing measurements for sample sentences
- Hardware specifications
- Benchmark results

**حدود النطاق:**
- ✓ ينطبق على جمل بسيطة (3-5 كلمات) - Applies to simple sentences (3-5 tokens)
- ✗ لا يضمن نفس الأداء للجمل المعقدة - Does not guarantee same performance for complex sentences
- ✗ يعتمد على العتاد المستخدم - Depends on hardware used

**ظروف الفشل المتوقعة:**
- Complex sentences with many operators
- Large operator catalogs
- Slow hardware

---

#### CLAIM-P2: Memory Efficiency
**النص:** The system operates with <500MB RAM for language processing tasks with standard operator catalogs (<100 operators).

**المجال:** Language domain

**الطبقات المعنية:** All layers

**الأدلة المطلوبة:**
- Memory profiling results
- Operator catalog sizes tested
- Memory usage measurements

**حدود النطاق:**
- ✓ ينطبق على كتالوجات قياسية (<100 عامل) - Applies to standard catalogs (<100 operators)
- ✗ لا يضمن نفس الكفاءة لكتالوجات كبيرة - Does not guarantee same efficiency for large catalogs

---

### 1.4 الادعاءات التفسيرية | Explainability Claims

#### CLAIM-E1: Why-Chain Completeness
**النص:** For every judgment, the system generates why-chains answering: (1) Why this meaning? (2) Why this relation? (3) Why this measurement? (4) Why this judgment?

**المجال:** All domains

**الطبقات المعنية:** A6 (Explanation Layer)

**الأدلة المطلوبة:**
- Output inspection showing all 4 why-chains
- Code generating why-chains
- Examples with complete explanations

**حدود النطاق:**
- ✓ يوفر سلاسل "لماذا" لكل قرار - Provides why-chains for each decision
- ✗ لا يضمن جودة التفسير - Does not guarantee explanation quality
- ✗ لا يضمن فهم المستخدم - Does not guarantee user comprehension

---

#### CLAIM-E2: Failure Point Identification
**النص:** The enhanced reporting system identifies potential failure points with: (1) condition causing failure, (2) reason, (3) impact, (4) mitigation strategy.

**المجال:** All domains

**الطبقات المعنية:** Enhanced Reporting

**الأدلة المطلوبة:**
- Report examples showing failure points
- Code for failure detection
- Coverage of common failure types

**حدود النطاق:**
- ✓ يحدد نقاط فشل محتملة معروفة - Identifies known potential failure points
- ✗ لا يضمن تحديد كل نقاط الفشل - Does not guarantee identification of all failure points
- ✗ لا يمنع الفشل نفسه - Does not prevent failure itself

---

#### CLAIM-E3: C1/C2/C3 Governance Annotation
**النص:** Reports include governance framework annotations with domain-specific: (1) conceptual framework (C1), (2) representation system (C2), (3) verification rules (C3), (4) epistemic order.

**المجال:** All domains

**الطبقات المعنية:** Enhanced Reporting

**الأدلة المطلوبة:**
- Report examples showing governance annotations
- Domain-specific configurations
- Epistemic order definitions

**حدود النطاق:**
- ✓ يوثق الإطار المعرفي المستخدم - Documents epistemological framework used
- ✗ لا يضمن صحة الإطار نفسه - Does not guarantee correctness of framework itself
- ✗ لا يفرض استخدام ترتيب الأدلة - Does not enforce use of epistemic order

---

## 2. تصنيف الادعاءات | Claims Classification

### 2.1 حسب القوة | By Strength

**ادعاءات قوية (Strong Claims):**
- CLAIM-A1, CLAIM-A2: معمارياً قابلة للتحقق - Architecturally verifiable
- CLAIM-M2: قابل للفحص المباشر - Directly inspectable

**ادعاءات متوسطة (Medium Claims):**
- CLAIM-M1: يتطلب اختبار عبر المجالات - Requires cross-domain testing
- CLAIM-E1, CLAIM-E2, CLAIM-E3: يعتمد على جودة التطبيق - Depends on implementation quality

**ادعاءات ضعيفة (Weak Claims):**
- CLAIM-A3: محدود بنطاق ضيق - Limited to narrow scope
- CLAIM-P1, CLAIM-P2: يعتمد على العتاد والبيانات - Hardware and data dependent

### 2.2 حسب قابلية الاختبار | By Testability

**قابل للاختبار الآلي (Automatically Testable):**
- CLAIM-A1, CLAIM-A2, CLAIM-P1, CLAIM-P2

**قابل للفحص اليدوي (Manually Inspectable):**
- CLAIM-M1, CLAIM-M2, CLAIM-E1, CLAIM-E2, CLAIM-E3

**يتطلب تقييم بشري (Requires Human Evaluation):**
- CLAIM-A3 (لتحديد ما إذا كان الخطأ "هلوسة" أم "خطأ منطقي")

---

## 3. توضيح الطبقات | Layer Clarification

### 3.1 التمييز بين المستويات | Distinction Between Levels

لتجنب الالتباس، نقترح الترميز التالي:

**A) الطبقات المعمارية (Architectural Layers):**
- **A0:** Input/Reality Layer (الواقع/المدخل)
- **A1:** Form Layer (الدال)
- **A2:** Semantic Layer (المدلول)
- **A3:** Relational Layer (النِّسب)
- **A4:** Measurement Layer (القياس)
- **A5:** Judgment Layer (الحكم)
- **A6:** Explanation Layer (التفسير)

**B) الطبقات المعرفية (Epistemological Layers):**
- **E1 (التصور):** Conceptual Framework - ما المفاهيم المستخدمة؟
- **E2 (التمثيل):** Representation System - كيف تُمثّل المفاهيم؟
- **E3 (التحقق):** Verification Rules - كيف نتحقق من الصحة؟

**C) حدود العقل (Epistemic Limits):**
- **L1:** حدود المعرفة (Knowledge limits)
- **L2:** حدود اليقين (Certainty limits)
- **L3:** نطاق الصلاحية (Validity scope)

**ملاحظة:** نظام FractalHub يستخدم C0/C1/C2/C3 للطبقات المعمارية، بينما نظام الحوكمة يستخدم C1/C2/C3 للطبقات المعرفية. يُنصح بتوحيد الترميز في النشر الأكاديمي.

---

# القسم (ب): قابلية التفنيد | Section B: Falsifiability

## 1. اختبارات التفنيد | Falsification Tests

### Test-A1: Layer Sequence Enforcement

**الفرضية القابلة للتفنيد:**
إذا تم محاولة القفز من الطبقة A1 إلى A4 مباشرة، يجب أن يُرفع استثناء ConstraintViolation.

**بروتوكول الاختبار:**
```python
# Test Case
from xai_engine.core import GlobalConstraints

constraints = GlobalConstraints()

try:
    # محاولة القفز من A1 (form) إلى A4 (measurement)
    constraints.no_layer_jump(
        from_layer="form",
        to_layer="measurement",
        layer_sequence=["form", "semantic", "relational", "measurement"]
    )
    # إذا لم يُرفع استثناء، الاختبار فاشل
    result = "FAILED - No exception raised"
except ConstraintViolation as e:
    # إذا رُفع استثناء، الاختبار ناجح
    result = "PASSED - ConstraintViolation raised"
```

**معايير النجاح:**
- ✓ يُرفع استثناء ConstraintViolation
- ✓ رسالة الخطأ تذكر الطبقات المعنية
- ✓ لا تتم معالجة الطبقة المستهدفة

**معايير الفشل (التفنيد):**
- ✗ لا يُرفع استثناء
- ✗ تتم المعالجة رغم القفز
- ✗ الاستثناء المرفوع ليس ConstraintViolation

---

### Test-A2: Constraint Enforcement

**الفرضية القابلة للتفنيد:**
لكل من القيود الثمانية، محاولة انتهاكه يجب أن تُرفع ConstraintViolation.

**بروتوكول الاختبار:**
```python
# Test Case للقيد: "لا نتيجة بلا قياس"
constraints = GlobalConstraints()

try:
    constraints.no_result_without_measurement(
        result="some_judgment",
        measurement_trace=None  # انتهاك: لا يوجد قياس
    )
    result = "FAILED"
except ConstraintViolation as e:
    if e.constraint_name == "NO_RESULT_WITHOUT_MEASUREMENT":
        result = "PASSED"
    else:
        result = "FAILED - Wrong constraint name"
```

**معايير النجاح:**
- ✓ الثمانية قيود تُرفع استثناءات عند انتهاكها
- ✓ كل استثناء له constraint_name صحيح
- ✓ رسائل الأخطاء واضحة

**معايير الفشل (التفنيد):**
- ✗ قيد أو أكثر لا يُرفع استثناء
- ✗ استثناءات مرفوعة لكن بدون constraint_name
- ✗ رسائل خطأ غير واضحة

---

### Test-A3: Anti-Hallucination Scope

**الفرضية القابلة للتفنيد:**
الأنواع الأربعة المحددة من الهلوسة يجب أن تُمنع، بينما الأخطاء الأخرى لا تُمنع.

**بروتوكول الاختبار:**
```python
# Test 1: منع المعاني بلا دال (يجب أن يُمنع)
try:
    constraints.no_meaning_without_form(
        meaning="orphaned_meaning",
        form=None
    )
    result_1 = "FAILED"
except ConstraintViolation:
    result_1 = "PASSED"

# Test 2: معجم خاطئ (لا يجب أن يُمنع معمارياً)
engine = XAIEngine.for_language()
# معجم يحتوي على تعريفات خاطئة لكن بشكل صحيح
result = engine.process("كلمة_خاطئة_دلالياً")
# النظام يعالج دون رفع ConstraintViolation
result_2 = "PASSED" if result else "FAILED"

# Test 3: غموض دلالي (لا يجب أن يُمنع)
result = engine.process("جملة_غامضة")
# النظام ينتج حكماً (ربما بوزن معرفي منخفض) دون رفع استثناء
result_3 = "PASSED" if result.judgment.epistemic_weight.confidence < 1.0 else "FAILED"
```

**معايير النجاح:**
- ✓ الأنواع الأربعة من الهلوسة تُمنع
- ✓ الأخطاء غير المعمارية لا تُمنع (لكن قد تُعلَّم بوزن معرفي منخفض)
- ✓ الفرق واضح بين الانتهاكات المعمارية والأخطاء المنطقية

**معايير الفشل (التفنيد):**
- ✗ نوع من الهلوسة الأربعة لا يُمنع
- ✗ أخطاء غير معمارية تُمنع (false positive)
- ✗ لا تمييز بين الانتهاكات والأخطاء

---

### Test-M1: Multi-Domain Consistency

**الفرضية القابلة للتفنيد:**
نفس المدخل (مُعرّب لكل مجال) يمر بنفس الطبقات الست في كل المجالات.

**بروتوكول الاختبار:**
```python
# اختبار أن كل مجال يمر بالطبقات الست
engines = {
    "language": XAIEngine.for_language(),
    "physics": XAIEngine.for_physics(),
    "mathematics": XAIEngine.for_mathematics(),
    "chemistry": XAIEngine.for_chemistry(),
}

inputs = {
    "language": "محمد طالب",
    "physics": "F = ma",
    "mathematics": "a² + b² = c²",
    "chemistry": "2H₂ + O₂ → 2H₂O",
}

for domain, engine in engines.items():
    result = engine.process(inputs[domain])
    
    # تحقق من وجود كل الطبقات
    assert hasattr(result, 'parse_tree')  # A1
    assert hasattr(result, 'semantic_candidates')  # A2
    assert hasattr(result, 'relation_graph')  # A3
    assert hasattr(result, 'measurement_trace')  # A4
    assert hasattr(result, 'judgment')  # A5
    assert hasattr(result, 'explanation')  # A6
```

**معايير النجاح:**
- ✓ كل المجالات الأربعة تمر بالطبقات الست
- ✓ كل مجال له measurement_system خاص
- ✓ القيود الثمانية مطبقة في كل المجالات

**معايير الفشل (التفنيد):**
- ✗ مجال يتخطى طبقة
- ✗ measurement_system واحد لكل المجالات
- ✗ قيود غير مطبقة في مجال معين

---

### Test-E1: Why-Chain Completeness

**الفرضية القابلة للتفنيد:**
كل حكم يحتوي على أربع سلاسل "لماذا" كاملة.

**بروتوكول الاختبار:**
```python
engine = XAIEngine.for_language()
result = engine.process("النص العربي")

# تحقق من وجود السلاسل الأربع
assert hasattr(result.explanation, 'why_this_meaning')
assert hasattr(result.explanation, 'why_this_relation')
assert hasattr(result.explanation, 'why_this_measurement')
assert hasattr(result.explanation, 'why_this_judgment')

# تحقق من أن كل سلسلة بها إجابة
assert len(result.explanation.why_this_meaning.answer) > 0
assert len(result.explanation.why_this_relation.answer) > 0
assert len(result.explanation.why_this_measurement.answer) > 0
assert len(result.explanation.why_this_judgment.answer) > 0
```

**معايير النجاح:**
- ✓ وجود السلاسل الأربع
- ✓ كل سلسلة بها سؤال وإجابة وأدلة
- ✓ السلاسل مرتبطة بالقرارات الفعلية

**معايير الفشل (التفنيد):**
- ✗ سلسلة مفقودة
- ✗ إجابات فارغة
- ✗ سلاسل عامة غير مرتبطة بالمدخل

---

## 2. نطاق التفنيد | Falsification Scope

### 2.1 ما يمكن تفنيده | What Can Be Falsified

**ادعاءات معمارية (Architectural Claims):**
- ✓ قابلة للتفنيد عبر اختبارات الوحدة
- ✓ قابلة للفحص عبر مراجعة الكود
- ✓ قابلة للقياس عبر أدوات التغطية

**ادعاءات منهجية (Methodological Claims):**
- ✓ قابلة للتفنيد عبر اختبارات التكامل
- ✓ قابلة للفحص عبر أمثلة واقعية
- ⚠ تتطلب معايير نجاح محددة

**ادعاءات أداء (Performance Claims):**
- ✓ قابلة للتفنيد عبر القياس
- ⚠ تعتمد على العتاد والبيانات
- ⚠ تتطلب بيئة اختبار قياسية

### 2.2 ما لا يمكن تفنيده | What Cannot Be Falsified

**ادعاءات فلسفية:**
- ✗ "النظام يفهم النص" - غير قابل للتحقق
- ✗ "النظام واعٍ" - غير قابل للقياس
- ✗ "النظام ذكي" - مفهوم غامض

**ادعاءات مطلقة:**
- ✗ "استحالة الهلوسة المطلقة" - واسع جداً
- ✗ "صحة كاملة" - غير محدد
- ✗ "يعمل في كل الحالات" - غير قابل للاستنفاد

**ادعاءات ذاتية:**
- ✗ "التفسيرات واضحة" - يعتمد على المستخدم
- ✗ "النتائج مفيدة" - معيار ذاتي
- ✗ "سهل الاستخدام" - تقييم شخصي

---

# القسم (ج): بروتوكول التقييم | Section C: Evaluation Protocol

## 1. البيئة المعيارية | Standard Environment

### 1.1 متطلبات العتاد | Hardware Requirements

**الحد الأدنى (Minimum):**
- CPU: 2 cores, 2.0 GHz
- RAM: 4 GB
- Storage: 1 GB
- OS: Linux/macOS/Windows

**المُوصى به (Recommended):**
- CPU: 4 cores, 3.0 GHz
- RAM: 8 GB
- Storage: 5 GB
- OS: Linux (Ubuntu 20.04+)

### 1.2 متطلبات البرمجيات | Software Requirements

```
Python: 3.8+
Dependencies: requirements.txt
Test Framework: pytest
Profiling: cProfile, memory_profiler
```

---

## 2. بروتوكول الاختبار الشامل | Comprehensive Test Protocol

### 2.1 المرحلة الأولى: اختبارات الوحدة | Phase 1: Unit Tests

**الهدف:** التحقق من كل ادعاء معماري

**الخطوات:**
1. تشغيل اختبارات القيود (8 tests)
2. تشغيل اختبارات الطبقات (6 tests)
3. تشغيل اختبارات التفنيد (10+ tests)

**معايير النجاح:**
- ✓ 100% نجاح في اختبارات القيود
- ✓ 100% نجاح في اختبارات الطبقات
- ✓ تغطية كود >80%

**الأدوات:**
```bash
pytest tests/ --cov=xai_engine --cov-report=html
```

---

### 2.2 المرحلة الثانية: اختبارات التكامل | Phase 2: Integration Tests

**الهدف:** التحقق من الادعاءات المنهجية

**الخطوات:**
1. اختبار كل مجال بـ10 أمثلة
2. فحص اكتمال التتبع
3. فحص جودة التفسير

**معايير النجاح:**
- ✓ كل الأمثلة تُنتج نتائج
- ✓ كل النتائج بها تتبع كامل
- ✓ لا استثناءات غير متوقعة

**مجموعة البيانات:**
- Language: 10 جمل عربية (بسيطة/مركبة)
- Physics: 10 معادلات فيزيائية
- Mathematics: 10 عبارات رياضية
- Chemistry: 10 معادلات كيميائية

---

### 2.3 المرحلة الثالثة: اختبارات الأداء | Phase 3: Performance Tests

**الهدف:** التحقق من الادعاءات الأدائية

**الخطوات:**
1. قياس زمن المعالجة (10 runs per sample)
2. قياس استخدام الذاكرة
3. قياس استخدام CPU

**معايير النجاح:**
- ✓ متوسط الوقت <1 ثانية للجمل البسيطة
- ✓ متوسط الذاكرة <500MB
- ✓ استقرار الأداء عبر التشغيلات

**الأدوات:**
```bash
python -m cProfile xai_engine/examples.py
python -m memory_profiler xai_engine/examples.py
```

---

### 2.4 المرحلة الرابعة: تقييم بشري | Phase 4: Human Evaluation

**الهدف:** تقييم جودة التفسيرات

**الخطوات:**
1. اختيار 20 مثال متنوع
2. تقييم التفسيرات من 3 خبراء
3. قياس: وضوح، اكتمال، دقة

**معايير النجاح:**
- ✓ متوسط تقييم الوضوح >3/5
- ✓ متوسط تقييم الاكتمال >3/5
- ✓ اتفاق بين المقيّمين >60%

**استمارة التقييم:**
```
1. هل التفسير واضح؟ (1-5)
2. هل التفسير كامل؟ (1-5)
3. هل التفسير دقيق؟ (1-5)
4. هل نقاط الفشل مفيدة؟ (نعم/لا)
5. هل الحوكمة C1/C2/C3 مفهومة؟ (نعم/لا)
```

---

## 3. بروتوكول إعادة الإنتاج | Reproducibility Protocol

### 3.1 نشر الكود | Code Publication

**المطلوب:**
- ✓ كود مصدري كامل على GitHub
- ✓ ملف requirements.txt محدّث
- ✓ أمثلة قابلة للتشغيل
- ✓ اختبارات قابلة للتكرار

### 3.2 نشر البيانات | Data Publication

**المطلوب:**
- ✓ مجموعات البيانات التجريبية
- ✓ نتائج الاختبارات
- ✓ ملفات التقارير النموذجية
- ✓ قياسات الأداء

### 3.3 نشر التوثيق | Documentation Publication

**المطلوب:**
- ✓ دليل التثبيت
- ✓ دليل الاستخدام
- ✓ دليل الادعاءات (هذا المستند)
- ✓ دليل التقييم

---

## 4. معايير القبول للنشر | Publication Acceptance Criteria

### 4.1 معايير إلزامية | Mandatory Criteria

- ✓ **M1:** كل ادعاء محدد النطاق
- ✓ **M2:** كل ادعاء قابل للتفنيد
- ✓ **M3:** بروتوكول تقييم كامل ومنشور
- ✓ **M4:** نتائج تجريبية تدعم الادعاءات
- ✓ **M5:** كود ومصادر منشورة

### 4.2 معايير مستحسنة | Recommended Criteria

- ⭐ **R1:** تقييم بشري من خبراء مستقلين
- ⭐ **R2:** مقارنة مع أنظمة بديلة
- ⭐ **R3:** تحليل حالات الفشل
- ⭐ **R4:** نقاش القيود والافتراضات
- ⭐ **R5:** خطة للتطوير المستقبلي

---

# الملاحق | Appendices

## ملحق (أ): قائمة مرجعية للمراجعين | Appendix A: Reviewer Checklist

**للمراجع الأكاديمي:**

### التحقق من نطاق الادعاءات:
- [ ] هل كل ادعاء محدد النطاق؟
- [ ] هل الحدود والاستثناءات واضحة؟
- [ ] هل تم تجنب الادعاءات المطلقة؟
- [ ] هل تم توضيح الفرق بين الطبقات المعمارية والمعرفية؟

### التحقق من قابلية التفنيد:
- [ ] هل كل ادعاء قابل للتفنيد؟
- [ ] هل اختبارات التفنيد واضحة ومحددة؟
- [ ] هل معايير النجاح والفشل محددة؟
- [ ] هل تم تحديد ما لا يمكن تفنيده؟

### التحقق من البروتوكول:
- [ ] هل بروتوكول التقييم كامل؟
- [ ] هل البيئة المعيارية محددة؟
- [ ] هل الأدوات والمتطلبات واضحة؟
- [ ] هل النتائج قابلة للتكرار؟

---

## ملحق (ب): أمثلة على الفشل المتوقع | Appendix B: Expected Failure Examples

### مثال 1: معجم خاطئ

**المدخل:**
```
كلمة عربية بتعريف خاطئ في المعجم
```

**النتيجة:**
- ✓ النظام يعالج بدون ConstraintViolation
- ✓ يُنتج حكماً بناءً على التعريف الخاطئ
- ⚠ الحكم منطقياً خاطئ لكن معمارياً صحيح

**التفسير:**
النظام لا يمنع الأخطاء في البيانات المدخلة، بل يمنع فقط الانتهاكات المعمارية.

---

### مثال 2: غموض دلالي

**المدخل:**
```
"رأيت الرجل بالمنظار"
```

**النتيجة:**
- ✓ النظام ينتج عدة مرشحات معنى
- ✓ يختار واحداً بناءً على القياس
- ⚠ الاختيار قد يكون غير صحيح
- ✓ الوزن المعرفي منخفض (يعكس الغموض)

**التفسير:**
النظام يتعامل مع الغموض بإنتاج مرشحات واختيار واحد، لكن يُعلّم بوزن معرفي منخفض.

---

### مثال 3: قفز بين الطبقات (محاولة)

**الكود:**
```python
# محاولة استدعاء طبقة مباشرة
measurement_layer.process(raw_text)  # تخطي A1, A2, A3
```

**النتيجة:**
- ✓ يُرفع ConstraintViolation
- ✓ المعالجة تتوقف
- ✓ رسالة خطأ واضحة

**التفسير:**
النظام يمنع القفز بين الطبقات بشكل صارم.

---

## ملحق (ج): مصطلحات ورموز | Appendix C: Terminology and Notation

### الطبقات المعمارية (Architectural Layers):
- **A0:** Input/Reality Layer
- **A1:** Form Layer (الدال)
- **A2:** Semantic Layer (المدلول)
- **A3:** Relational Layer (النِّسب)
- **A4:** Measurement Layer (القياس)
- **A5:** Judgment Layer (الحكم)
- **A6:** Explanation Layer (التفسير)

### الطبقات المعرفية (Epistemological Layers):
- **E1:** Conceptual Framework (التصور)
- **E2:** Representation System (التمثيل)
- **E3:** Verification Rules (التحقق)

### القيود (Constraints):
- **C1:** No result without measurement
- **C2:** No generalization without scope
- **C3:** No judgment without relation
- **C4:** No explanation without trace
- **C5:** No layer jumping
- **C6:** No domain mixing
- **C7:** No meaning without form
- **C8:** No measurement without operator

---

## ملحق (د): المراجع والمصادر | Appendix D: References

### كود المشروع:
- GitHub: sonaiso/Eqratech_Arabic_Diana_Project
- Branch: copilot/upgrade-to-conciousness-kernel
- Commits: 8868120, ef7cf8c, 9f67779, 1d4746b

### التوثيق:
- xai_engine/README.md
- ENHANCED_REPORTING_GUIDE.md
- XAI_ENGINE_SUMMARY.md

### الأمثلة:
- xai_engine/examples.py
- xai_engine/examples_enhanced.py

---

## الخلاصة | Conclusion

هذا المستند يوفر إطاراً صارماً لنشر البحث حول النظام، مع:

1. ✅ **ادعاءات محددة النطاق** - 13 ادعاء قابل للتحقق
2. ✅ **قابلية تفنيد واضحة** - اختبارات محددة لكل ادعاء
3. ✅ **بروتوكول تقييم شامل** - 4 مراحل قابلة للتكرار
4. ✅ **توضيح القيود** - ما يُمنع وما لا يُمنع
5. ✅ **معايير قبول** - 5 معايير إلزامية + 5 مستحسنة

**ملاحظة نهائية:**
يُنصح بمراجعة هذا المستند مع كل تحديث للنظام، وتحديث الادعاءات والاختبارات بناءً على النتائج الجديدة.

---

**تاريخ النشر:** 19 يناير 2026  
**الإصدار:** 1.0  
**الحالة:** جاهز للمراجعة الأكاديمية
