# الوثيقة الرياضية التأسيسية للعقل الباني — Theory-to-Code Mapping

## نظرة عامة

يُطبِّق هذا الملف «الوثيقة الرياضية التأسيسية للعقل الباني» بوصفها حزمة Python
عملية قابلة للتشغيل والاختبار.

---

## 1. الكون المعرفي والأنطولوجيا

### المفاهيم الأساسية

| المفهوم | التعريف الرياضي | الكلاس |
|--------|-----------------|--------|
| `Ω` (الكون المعرفي) | الفضاء الكلي لكل المعرفة | `KnowledgeUniverse` |
| `R` (الواقع) | `R ⊆ Ω` — الواقعات المُشاهَدة | `Reality` |
| `T` (الأثر) | `T ⊆ Ω` — الآثار المُستخلَصة | `Trace` |
| `τ` (دالة الأثر) | `τ : R → T` | `trace_fn()` |

### الملف: `src/foundation/ontology.py`

```python
from foundation.ontology import KnowledgeUniverse, Reality, Trace, trace_fn

omega = KnowledgeUniverse()           # Ω
r = Reality(raw_text="الكِتَابُ مُفِيدٌ")  # r ∈ R
omega.register(r)
t = omega.apply_trace_fn(r)           # t = τ(r) ∈ T
```

---

## 2. مخرجات النظام الثلاثة

### التمييز الإبستيمي

| المخرج | المعنى | الكلاس | العتبة |
|--------|--------|--------|--------|
| **شهادة** | يقين ثابت بأثر صريح | `Shahada()` | confidence ≥ 0.80 |
| **فرضية** | احتمال معقول | `Hypothesis()` | 0 < confidence < 0.80 |
| **صفر معرفي** | غياب الأثر / «لم يثبت» | `EpistemicZero()` | confidence = 0.0 |

يتناظر هذا مع التقسيم المنطقي-الأصولي: **يقين | ظن | جهل**

### الملف: `src/foundation/outputs.py`

```python
from foundation.outputs import Shahada, Hypothesis, EpistemicZero

# شهادة
out = Shahada("الكِتَابُ اسم مرفوع", confidence=0.95, stage="الحكم")

# فرضية
out = Hypothesis("قد يكون الفعل لازماً", confidence=0.6)

# ترقية تلقائية إذا تجاوزت العتبة
promoted = out.promote()  # يصبح Shahada إذا confidence ≥ 0.80

# صفر معرفي
out = EpistemicZero("النص فارغ أو غير قابل للتحليل")
```

---

## 3. النوى العشرون

### الملف: `src/foundation/nuclei.py`

كل نواة dataclass تُمثِّل مفهوماً أساسياً في منظومة «العقل الباني»:

| الرقم | النواة | الكلاس | المرحلة المقابلة |
|-------|--------|--------|-----------------|
| 1 | الشهادة | `ShahadaNucleus` | الحكم المطبق |
| 2 | الصفر المعرفي | `SifrNucleus` | أي مرحلة |
| 3 | الفرضية | `FaradiyyaNucleus` | الحكم المرشح |
| 4 | الانتقال والبوابة | `TransitionGateNucleus` | بين المراحل |
| 5 | التصور | `TasawwurNucleus` | المرحلة 3 |
| 6 | المفهوم | `MafhumNucleus` | المرحلة 4 |
| 7 | المجال | `MajalNucleus` | نطاق الحكم |
| 8 | الدلالة | `DalalaNucleus` | المرحلة 5 |
| 9 | النسبة | `NisbaNucleus` | المرحلة 6 |
| 10 | الحكم | `HukmNucleus` | المراحل 7-9 |
| 11 | تحقيق المناط | `TahqiqManatNucleus` | المرحلة 8 |
| 12 | القياس | `QiyasNucleus` | المرحلة 10 |
| 13 | العوامل المئة | `MiataamilNucleus` | الطبقة النحوية |
| 14 | الإعراب كمتجه | `IrabVectorNucleus` | الطبقة النحوية |
| 15 | الإفادة | `IfadaNucleus` | الجملة المفيدة |
| 16 | أثر الحكم والسلوك | `AatharHukmNucleus` | المرحلة 11 |
| 17 | التعارض والترجيح | `TaarudTarjihNucleus` | argmin متعدد |
| 18 | أهلية المستدل | `AhliyyaNucleus` | مُعدِّل الوزن |
| 19 | الواقع | `WaqiaNucleus` | المرحلة 1 |
| 20 | الطبقات اللغوية الدنيا | `LowerLayersNucleus` | ربط Eqratech |

---

## 4. وحدات يونيكود العربية

### الملف: `src/foundation/unicode_units.py`

يُحلِّل كل حرف/علامة في النص العربي إلى:
- نقطة الكود (`U+XXXX`)
- تصنيف الوحدة (`UnitKind`)
- السبب / الأثر / الوظيفة

```python
from foundation.unicode_units import ArabicText, UnitKind

text = ArabicText.from_string("الكِتَابُ مُفِيدٌ")

for unit in text:
    print(f"{unit.char}  {unit.codepoint_str}  {unit.kind.value}")
    print(f"  السبب:   {unit.cause}")
    print(f"  الأثر:   {unit.effect}")
    print(f"  الوظيفة: {unit.function}")

# إحصاءات
stats = text.stats()
# {'total_units': N, 'letter_count': N, 'diacritic_count': N, ...}

# كلمات
for token in text.tokens():
    print(token.raw, token.letters_only(), token.harakat_sequence())
```

### أنواع الوحدات (`UnitKind`)

| النوع | القيمة | الوصف |
|-------|--------|-------|
| `LETTER` | `حرف` | حرف هجائي أساسي |
| `HARAKA` | `حركة` | فتحة / ضمة / كسرة |
| `TANWIN` | `تنوين` | تنوين الثلاثة |
| `SHADDA` | `شدة` | U+0651 |
| `SUKUN` | `سكون` | U+0652 |
| `MADD` | `مد` | ألف خنجرية U+0670 |
| `HAMZA` | `همزة` | الهمزة بأشكالها |
| `ALEF_VARIANTS` | `ألف` | أشكال الألف |

---

## 5. الدالة الجامعة — الإحدى عشر مرحلة

### الملف: `src/foundation/pipeline.py`

```python
from foundation.pipeline import AnalysisPipeline

pipeline = AnalysisPipeline()
analysis = pipeline.run("الكِتَابُ مُفِيدٌ")

print(analysis.summary())
# يطبع: كل مرحلة مع نوع المخرج ودرجة الثقة
```

### خريطة المراحل

```
PipelineStage                المرحلة                    المُطبَّق
─────────────────────────────────────────────────────────────────
1  OBSERVED_REALITY         واقع مشهود           ✓ v0.1
2  CONFIRMED_TRACE          أثر مثبت             ✓ v0.1
3  DETERMINED_CONCEPTION    تصور متعين            ✓ v0.1
4  BOUNDED_CONCEPT          مفهوم محدود           ✓ v0.1 (جزئي)
5  SIGNIFICATION            دلالة مضبوطة          ~ v0.1 (placeholder)
6  BINARY_RELATION          نسبة ذات طرفين        ✓ v0.1 (جزئي)
7  CANDIDATE_RULING         حكم مرشح             ✓ v0.1
8  MANAT_ACTUALIZATION      تحقيق مناط            ✓ v0.1
9  APPLIED_RULING           حكم مطبق             ✓ v0.1
10 ANALOGY                  قياس                  ~ v0.1 (placeholder)
11 BEHAVIORAL_EFFECT        أثر الحكم             ✓ v0.1
```

---

## 6. استخلاص الأثر

### الملف: `src/foundation/trace.py`

```python
from foundation.trace import TraceExtractor
from foundation.ontology import Reality, TraceLevel

extractor = TraceExtractor()
r = Reality(raw_text="الكِتَابُ مُفِيدٌ")

# أثر سطحي
rt = extractor.extract(r, TraceLevel.SURFACE)

# أثر شامل
rt = extractor.extract_full(r)

# بيانات المستويات
rt.level_data["surface"]   # إحصاءات سطحية
rt.level_data["phonemic"]  # تسلسل الحركات
```

---

## 7. التسلسل والإخراج

### الملف: `src/foundation/serialization.py`

```python
from foundation.serialization import (
    serialize_analysis,
    save_analysis,
    load_analysis,
    format_analysis_text,
    format_trace_units,
)

# تحويل إلى JSON
json_str = serialize_analysis(analysis)

# حفظ إلى ملف
save_analysis(analysis, "output/analysis.json")

# تحميل
data = load_analysis("output/analysis.json")

# عرض نصي
print(format_analysis_text(analysis))
print(format_trace_units(analysis))
```

---

## 8. هيكل الملفات

```
src/foundation/
├── __init__.py           — الصادرات الرئيسية
├── ontology.py           — Ω / R / T / τ
├── outputs.py            — شهادة / فرضية / صفر معرفي
├── nuclei.py             — النوى العشرون
├── unicode_units.py      — ArabicUnit / ArabicText
├── trace.py              — TraceExtractor / RichTrace
├── pipeline.py           — AnalysisPipeline / 11 مراحل
└── serialization.py      — JSON / نص / حفظ/تحميل

tests/foundation/
└── test_foundation.py    — 66 اختباراً

examples/
└── foundation_demo.py    — مثال تشغيلي CLI

docs/
└── foundation_theory.md  — هذا الملف
```

---

## 9. خريطة الربط بـ Eqratech

### الطبقات المتكاملة (v0.2+)

| طبقة Foundation | محركات Eqratech | الملف |
|-----------------|-----------------|-------|
| TraceLevel.PHONEMIC | C2a gates (sukun, shadda, …) | `src/fvafk/c2a/` |
| TraceLevel.MORPHEMIC | C2b (RootExtractor) | `src/fvafk/c2b/` |
| TraceLevel.SYNTACTIC | SyntaxTheory | `src/syntax_theory/` |
| `IrabVectorNucleus` | MaqamTheory gates | `src/maqam_theory/` |
| `LowerLayersNucleus` | جميع محركات Engines | `src/engines/` |

### مثال الربط (v0.2)
```python
# الربط المستقبلي
lower = LowerLayersNucleus()
lower.bind_engine("صوتي", "PhonemesEngine")
lower.bind_engine("صرفي", "RootExtractor")
lower.bind_engine("نحوي", "SyntaxTheory")
```

---

## 10. التشغيل

```bash
# تشغيل جميع الأمثلة
python examples/foundation_demo.py

# تحليل نص محدد
python examples/foundation_demo.py --text "قَرَأَ الطَّالِبُ الدَّرْسَ"

# مع عرض وحدات يونيكود
python examples/foundation_demo.py --text "كِتَابٌ" --units

# إخراج JSON
python examples/foundation_demo.py --text "الكِتَابُ مُفِيدٌ" --json

# تشغيل الاختبارات
pytest tests/foundation/ -v
```

---

## 11. الحالة (v0.1)

### ✅ مُطبَّق بالكامل
- الأنطولوجيا: `Ω / R / T / τ`
- مخرجات النظام الثلاثة
- النوى العشرون (dataclasses)
- وحدات يونيكود العربية (كاملة)
- خط الأنابيب 11 مرحلة (هيكل كامل)
- تسلسل JSON
- 66 اختباراً

### 🔄 جزئي في v0.1
- تحليل المفهوم (مرحلة 4): تصنيف بسيط
- الدلالة (مرحلة 5): placeholder
- القياس (مرحلة 10): placeholder

### 📋 مخطط لـ v0.2
- ربط TraceExtractor بمحركات C2a/C2b
- ربط Pipeline بـ SyntaxTheory
- تحليل دلالي بالمحركات المعجمية
- القياس الأصولي الكامل
