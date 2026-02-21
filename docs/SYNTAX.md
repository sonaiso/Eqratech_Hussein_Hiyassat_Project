# Syntax Module Documentation

**Sprint 4: I3rab (Syntax) Analysis**

The syntax module provides I3rab (إعراب) analysis for Classical Arabic text, specifically designed for Quranic text analysis.

---

## 🏗️ Architecture Overview

The syntax module uses a **3-layer architecture**:

```
Layer 1: I3rabAnnotation (Raw Corpus Data)
    ↓
Layer 2: I3rabComponents (Parsed Structured Data)
    ↓
Layer 3: SyntaxFeatures (High-Level Features)
```

### Layer 1: I3rabAnnotation
Raw I3rab data from corpus (e.g., Quranic I3rab corpus).

```python
from fvafk.c2b.syntax import I3rabAnnotation

annotation = I3rabAnnotation(
    word="الْحَمْدُ",
    i3rab_text="مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة",
    surah=1,
    ayah=2,
    word_index=0
)
```

### Layer 2: I3rabComponents
Parsed, structured I3rab data.

```python
from fvafk.c2b.syntax import I3rabComponents

components = I3rabComponents(
    i3rab_type="mubtada",        # مبتدأ
    case="nominative",            # مرفوع
    case_marker="damma",          # الضمة
    mahall="في محل رفع",
    confidence=0.9
)
```

### Layer 3: SyntaxFeatures
High-level linguistic features for ML/analysis.

```python
from fvafk.c2b.syntax import SyntaxFeatures

features = SyntaxFeatures(
    syntactic_role="subject",
    case="nominative",
    i3rab_type_ar="مبتدأ",
    i3rab_type_en="mubtada",
    confidence=0.9
)
```

---

## 🔧 Core Components

### 1. I3rab Parser

Extracts structured data from Arabic I3rab text using regex patterns.

**Extracts:**
- I3rab type (مبتدأ، خبر، فاعل، مفعول به، حرف)
- Case (مرفوع، منصوب، مجرور)
- Case marker (الضمة، الفتحة، الكسرة)
- Mahall (في محل / لا محل له من الإعراب)

**Example:**

```python
from fvafk.c2b.syntax import I3rabParser, parse_i3rab

# Using parser class
parser = I3rabParser()
result = parser.parse("مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة")

print(f"I3rab Type: {result.i3rab_type}")  # mubtada
print(f"Case: {result.case}")              # nominative
print(f"Marker: {result.case_marker}")     # damma
print(f"Confidence: {result.confidence}")  # 0.9

# Using convenience function
result = parse_i3rab("خبر مرفوع وعلامة رفعه الضمة")
```

### 2. Syntax Evaluator

Compares syntax predictions against gold standard annotations.

**Metrics:**
- I3rab type accuracy
- Case accuracy
- Case marker accuracy
- Overall accuracy and F1 scores
- Per-class precision/recall
- Coverage (% of words analyzed)

**Example:**

```python
from fvafk.c2b.syntax import SyntaxEvaluator, I3rabComponents

evaluator = SyntaxEvaluator()

predictions = [
    I3rabComponents(i3rab_type="mubtada", case="nominative"),
    I3rabComponents(i3rab_type="khabar", case="nominative"),
]

gold_standard = [
    I3rabComponents(i3rab_type="mubtada", case="nominative"),
    I3rabComponents(i3rab_type="khabar", case="nominative"),
]

result = evaluator.evaluate(predictions, gold_standard)

print(f"Overall Accuracy: {result.overall_accuracy()}")
print(f"Overall F1: {result.overall_f1()}")
print(f"Coverage: {result.coverage}")

# Get detailed summary
summary = result.summary()
print(summary["features"]["i3rab_type"]["accuracy"])
```

### 3. Morph-Syntax Bridge

Predicts syntax features from morphology using rule-based inference.

**Rules:**
1. Definite nominative at sentence start → مبتدأ (mubtada)
2. Indefinite accusative → مفعول به (maf'ul bihi)
3. Genitive after word → مضاف إليه (mudaf_ilayhi)
4. Nominative after nominative → خبر (khabar)
5. Last position nominative → خبر (khabar)

**Example:**

```python
from fvafk.c2b.syntax import MorphSyntaxBridge
from fvafk.c2b.morphology_flags import MorphologyFlags

bridge = MorphSyntaxBridge()

# الحمد لله (Al-Hamdu lillah)
morphologies = [
    MorphologyFlags(case="nominative", definiteness=True),  # الحمد
    MorphologyFlags(case="genitive", definiteness=False),   # لله
]

predictions = bridge.predict_sentence(morphologies)

for i, pred in enumerate(predictions):
    print(f"Word {i+1}:")
    print(f"  I3rab Type: {pred.i3rab_type_en}")
    print(f"  Role: {pred.syntactic_role}")
    print(f"  Case: {pred.case}")
    print(f"  Confidence: {pred.confidence}")
```

---

## 📊 Arabic-English Mappings

The module provides bidirectional mappings:

```python
from fvafk.c2b.syntax import (
    I3RAB_TYPE_AR_TO_EN,
    CASE_AR_TO_EN,
    CASE_MARKER_AR_TO_EN,
    map_i3rab_to_role,
    map_ar_to_en,
)

# I3rab type mappings
print(I3RAB_TYPE_AR_TO_EN["مبتدأ"])  # mubtada
print(I3RAB_TYPE_AR_TO_EN["خبر"])    # khabar
print(I3RAB_TYPE_AR_TO_EN["فاعل"])   # fa'il

# Case mappings
print(CASE_AR_TO_EN["مرفوع"])  # nominative
print(CASE_AR_TO_EN["منصوب"])  # accusative
print(CASE_AR_TO_EN["مجرور"])  # genitive

# Case marker mappings
print(CASE_MARKER_AR_TO_EN["الضمة"])  # damma
print(CASE_MARKER_AR_TO_EN["الفتحة"])  # fatha
print(CASE_MARKER_AR_TO_EN["الكسرة"])  # kasra

# I3rab to syntactic role
print(map_i3rab_to_role("mubtada"))    # subject
print(map_i3rab_to_role("fa'il"))      # subject
print(map_i3rab_to_role("maf'ul_bihi")) # object
```

---

## 🎯 Complete Usage Examples

### Example 1: Parse and Analyze I3rab Text

```python
from fvafk.c2b.syntax import I3rabParser

parser = I3rabParser()

# Parse different I3rab types
examples = [
    "مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة على آخره",
    "خبر مرفوع وعلامة رفعه الضمة",
    "فاعل مرفوع وعلامة رفعه الضمة الظاهرة",
    "مفعول به منصوب وعلامة نصبه الفتحة الظاهرة",
    "حرف جر مبني على الكسر لا محل له من الإعراب",
]

for i3rab_text in examples:
    result = parser.parse(i3rab_text)
    print(f"Text: {i3rab_text}")
    print(f"  Type: {result.i3rab_type}")
    print(f"  Case: {result.case}")
    print(f"  Marker: {result.case_marker}")
    print(f"  Confidence: {result.confidence:.2f}")
    print()
```

### Example 2: Predict Syntax from Morphology

```python
from fvafk.c2b.syntax import predict_syntax_from_morphology
from fvafk.c2b.morphology_flags import MorphologyFlags

# بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ
# (Bismillah ir-Rahman ir-Rahim)
morphologies = [
    MorphologyFlags(case="genitive", definiteness=False),  # بسم
    MorphologyFlags(case="genitive", definiteness=True),   # الله
    MorphologyFlags(case="genitive", definiteness=True),   # الرحمن
    MorphologyFlags(case="genitive", definiteness=True),   # الرحيم
]

predictions = predict_syntax_from_morphology(morphologies)

words = ["بِسْمِ", "اللَّهِ", "الرَّحْمَنِ", "الرَّحِيمِ"]
for word, pred in zip(words, predictions):
    print(f"{word}:")
    print(f"  Role: {pred.syntactic_role}")
    print(f"  I3rab: {pred.i3rab_type_ar} ({pred.i3rab_type_en})")
    print(f"  Case: {pred.case}")
    print()
```

### Example 3: Evaluate Predictions

```python
from fvafk.c2b.syntax import evaluate_syntax, I3rabComponents

# Your predictions
predictions = [
    I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
    I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
    I3rabComponents(i3rab_type="fa'il", case="nominative", case_marker="damma"),
]

# Gold standard
gold = [
    I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
    I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
    I3rabComponents(i3rab_type="fa'il", case="nominative", case_marker="damma"),
]

result = evaluate_syntax(predictions, gold)

print(f"Overall Accuracy: {result.overall_accuracy():.2%}")
print(f"Overall F1: {result.overall_f1():.2%}")
print(f"Coverage: {result.coverage:.2%}")
print(f"\nPer-Feature Accuracy:")
print(f"  I3rab Type: {result.i3rab_type_metrics.accuracy:.2%}")
print(f"  Case: {result.case_metrics.accuracy:.2%}")
print(f"  Case Marker: {result.case_marker_metrics.accuracy:.2%}")
```

---

## 🧪 Testing

The syntax module has **66 comprehensive tests**:

```bash
# Run all syntax tests
pytest tests/test_syntax*.py -v

# Run specific test files
pytest tests/test_syntax_models.py -v          # 10 tests - Data models
pytest tests/test_i3rab_parser.py -v           # 13 tests - Parser
pytest tests/test_syntax_evaluator.py -v       # 12 tests - Evaluator
pytest tests/test_morph_syntax_bridge.py -v    # 14 tests - Bridge
pytest tests/test_syntax_integration.py -v     # 17 tests - Integration

# Check test coverage
pytest tests/test_syntax*.py --cov=src/fvafk/c2b/syntax --cov-report=html
```

---

## 📈 Performance & Accuracy

### Parser Performance
- **Confidence Scoring**: 0.0-1.0 based on extracted features
- **Coverage**: Handles top 5 I3rab types (covers ~80% of Quranic I3rab)
- **Extraction Accuracy**: High precision with regex patterns

### Bridge Inference
- **Rule-Based**: 5 inference rules
- **Context-Aware**: Uses previous word information
- **Confidence Levels**:
  - High (0.7-0.8): Strong rule match
  - Medium (0.5-0.7): Contextual inference
  - Low (0.0-0.5): Weak match or unknown

---

## 🔄 Integration with Other Modules

### With Morphology Module

```python
from fvafk.c2b.morphology_flags import MorphologyFlags
from fvafk.c2b.syntax import MorphSyntaxBridge

# Get morphology from morphology module
morph = MorphologyFlags(case="nominative", definiteness=True)

# Predict syntax
bridge = MorphSyntaxBridge()
syntax = bridge.predict_syntax(morph, position=0, total_words=3)
```

### With Evaluation Module

```python
from fvafk.c2b.evaluation.metrics import ConfusionMatrix
from fvafk.c2b.syntax import SyntaxEvaluator

# Evaluator uses evaluation module's ConfusionMatrix
evaluator = SyntaxEvaluator()
result = evaluator.evaluate(predictions, gold)

# Access confusion matrix
cm = result.i3rab_type_metrics.confusion_matrix
cm_summary = cm.summary()
```

---

## 🎓 I3rab Types Supported

| Arabic | English | Syntactic Role | Case |
|--------|---------|----------------|------|
| مبتدأ | mubtada | subject | nominative |
| خبر | khabar | predicate | nominative |
| فاعل | fa'il | subject | nominative |
| مفعول به | maf'ul_bihi | object | accusative |
| حرف | harf | particle | N/A |

---

## 📚 API Reference

### Classes

- `I3rabAnnotation`: Raw corpus I3rab data
- `I3rabComponents`: Parsed I3rab components
- `SyntaxFeatures`: High-level syntax features
- `I3rabParser`: Parse Arabic I3rab text
- `SyntaxEvaluator`: Evaluate syntax predictions
- `SyntaxMetrics`: Metrics for a single feature
- `SyntaxEvaluationResult`: Complete evaluation results
- `MorphSyntaxBridge`: Infer syntax from morphology
- `SimpleContextAnalyzer`: Analyze word context

### Functions

- `parse_i3rab(i3rab_text)`: Parse I3rab text
- `evaluate_syntax(predictions, gold)`: Evaluate predictions
- `predict_syntax_from_morphology(morphologies)`: Predict from morphology
- `map_i3rab_to_role(i3rab_type)`: Map I3rab type to syntactic role
- `map_ar_to_en(mapping_dict, ar_value)`: Generic Arabic to English mapper

---

## 🚀 Future Enhancements

- [ ] Add more I3rab types (e.g., نعت، بدل، حال)
- [ ] Improve confidence scoring with ML
- [ ] Add verb-based syntax rules
- [ ] Support compound I3rab (multiple roles)
- [ ] Add context window analysis
- [ ] Integrate with dependency parsing

---

## 📝 References

- Quranic I3rab Corpus: [quranic-corpus.org](http://corpus.quran.com/)
- Arabic Grammar Resources
- Classical Arabic Syntax (النحو العربي)

---

**Author**: Hussein Hiyassat  
**Sprint**: 4 - Syntax Foundation  
**Date**: February 2026  
**Tests**: 66 tests passing ✅