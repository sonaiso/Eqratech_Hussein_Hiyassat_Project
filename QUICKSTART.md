# دليل البداية السريعة | Quick Start Guide

**مشروع نظام اللغة العربية الحسابي**  
**Computational Arabic Language System**

---

## ⚡ التثبيت السريع | Quick Installation

### متطلبات النظام | System Requirements
- Python 3.8+
- pip

### خطوتان للبدء | Two Steps to Start

```bash
# 1. تثبيت الاعتماديات | Install dependencies
pip install -r requirements.txt

# 2. تعيين مسار Python | Set Python path
export PYTHONPATH=src  # Linux/Mac
# or
set PYTHONPATH=src     # Windows
```

---

## 🚀 الاستخدام الأساسي | Basic Usage

### 1. تحليل صوتي | Phonological Analysis

```bash
python -m fvafk.cli "كَاتِبٌ"
```

**الإخراج | Output**:
```
Input: كَاتِبٌ
✓ C1: Normalization
✓ C2a: Phonological gates
✓ C2b: Morphological analysis
```

### 2. تحليل صرفي كامل | Full Morphological Analysis

```bash
python -m fvafk.cli "كَاتِبٌ" --morphology
```

**الإخراج | Output**:
```
Root: كتب
Pattern: فاعل
Type: Active Participle
```

### 3. إخراج JSON | JSON Output

```bash
python -m fvafk.cli "كَاتِبٌ" --morphology --json
```

---

## 🔍 استكشاف المحركات | Explore Engines

### عرض جميع المحركات | Show All Engines

```bash
python engine_hierarchy.py
```

**الإخراج | Output**:
```
📂 Layer 1: PHONOLOGY (الصوتيات)
  └─ Group 1.1: Core Phonemes
      • PhonemesEngine
      • SoundEngine
...
```

### التصفية حسب الطبقة | Filter by Layer

```bash
python engine_hierarchy.py --layer 2  # Morphology
python engine_hierarchy.py --layer 4  # Syntax
```

### البحث بالمصطلح | Search by Term

```bash
python engine_hierarchy.py --search "فاعل"
python engine_hierarchy.py --search "تشبيه"
```

### الإحصائيات | Statistics

```bash
python engine_hierarchy.py --stats
```

**الإخراج | Output**:
```
Total Engines: 66
Layers: 6
Groups: 30
```

---

## 📊 تصدير القواعد | Export Grammar

### تصدير إلى Excel | Export to Excel

```bash
python Main_engine.py
```

**الإخراج | Output**: `full_multilayer_grammar.xlsx` (249 KB)

---

## 🧪 تشغيل الاختبارات | Run Tests

### جميع الاختبارات | All Tests

```bash
pytest -v
```

### اختبارات محددة | Specific Tests

```bash
pytest tests/test_gate_sukun.py -v
pytest tests/c2b/ -v
pytest tests/engines/phonology/ -v
```

### تقرير التغطية | Coverage Report

```bash
pytest --cov=src --cov-report=html
```

---

## 🌉 التكامل | Integration

### استخدام Pipeline المتكامل | Using Integrated Pipeline

```python
import sys
sys.path.insert(0, 'src')

from integration import ArabicNLPPipeline

# إنشاء pipeline | Create pipeline
pipeline = ArabicNLPPipeline()

# معالجة | Process
result = pipeline.process(root="كتب", pattern="فاعل")

print(f"Success: {result['success']}")
print(f"Sentence: {result['sentence']}")
print(f"Stages: {', '.join(result['stages'])}")
```

**الإخراج | Output**:
```
Success: True
Sentence: كتب → فاعل
Stages: phonology, morphology, syntax, generation
```

---

## 📚 أمثلة شاملة | Comprehensive Examples

### مثال 1: تحليل كلمة | Example 1: Analyze Word

```python
from fvafk.c2b import RootExtractor

extractor = RootExtractor()
root = extractor.extract("كَاتِبٌ")

print(f"Root: {root.letters}")  # ('ك', 'ت', 'ب')
print(f"Type: {root.root_type}")  # TRILATERAL
```

### مثال 2: استخدام محرك | Example 2: Use Engine

```python
import sys
sys.path.insert(0, 'src')

from engines.phonology import PhonemesEngine

df = PhonemesEngine.make_df()
print(f"Phonemes: {len(df)}")
print(df[['الأداة', 'النوع']].head())
```

### مثال 3: بناء شجرة تركيبية | Example 3: Build Syntax Tree

```python
import sys
sys.path.insert(0, 'src')

from syntax_theory.structures import SyntacticInput, LexicalAtom

# إنشاء مدخل | Create input
x = SyntacticInput(
    lexical_atoms=[
        LexicalAtom(token="كتب", lex_type="V"),
        LexicalAtom(token="أحمد", lex_type="N")
    ]
)

print(f"Input created: {x}")
```

---

## 🔧 أدوات التطوير | Development Tools

### فحص البنية | Check Structure

```bash
# عرض هيكل src/ | Show src/ structure
tree src -L 2

# عدّ الملفات | Count files
find src -name "*.py" | wc -l
```

### فحص الجودة | Quality Checks

```bash
# تحقق من النمط | Check style (if configured)
# flake8 src/

# فحص الأنواع | Type checking (if configured)
# mypy src/
```

---

## 🐛 استكشاف الأخطاء | Troubleshooting

### خطأ: No module named 'pandas'

```bash
pip install pandas openpyxl
```

### خطأ: No module named 'engines'

```bash
export PYTHONPATH=src  # Linux/Mac
set PYTHONPATH=src     # Windows
```

### خطأ: No module named 'pytest'

```bash
pip install pytest pytest-cov
```

### فشل الاختبارات | Tests Failing

```bash
# تشغيل اختبار واحد مع تفاصيل | Run one test with details
pytest tests/test_gate_sukun.py -v --tb=long
```

---

## 📖 التوثيق الإضافي | Additional Documentation

### للمستخدمين | For Users
- [README.md](README.md) - النظرة العامة | Overview
- [ENGINE_TAXONOMY.md](ENGINE_TAXONOMY.md) - التصنيف الكامل | Complete classification
- [ANALYSIS_SUMMARY.md](ANALYSIS_SUMMARY.md) - ملخص التحليل | Analysis summary

### للمطورين | For Developers
- [ENGINE_MANIFEST.md](ENGINE_MANIFEST.md) - البنية المعمارية | Architecture
- [IMPLEMENTATION_ROADMAP.md](IMPLEMENTATION_ROADMAP.md) - خطة التنفيذ | Implementation plan
- [PROJECT_CRITIQUE.md](PROJECT_CRITIQUE.md) - النقد والتحليل | Critique & analysis

### للباحثين | For Researchers
- [THEORY_SUMMARY.md](THEORY_SUMMARY.md) - النظرية الصوتية | Phonological theory
- [SYNTAX_THEORY_SUMMARY.md](SYNTAX_THEORY_SUMMARY.md) - نظرية التركيب | Syntax theory
- [تحليل_ونقد_المشروع.md](تحليل_ونقد_المشروع.md) - التحليل الشامل | Comprehensive analysis

---

## 💡 نصائح سريعة | Quick Tips

### 1. استخدم الإكمال التلقائي | Use Tab Completion
```bash
python engine_<TAB>  # يعرض الخيارات | Shows options
```

### 2. اختصارات مفيدة | Useful Shortcuts
```bash
# اختبار سريع | Quick test
pytest -x  # توقف عند أول فشل | Stop at first failure

# إخراج مختصر | Brief output
pytest -q  # quiet mode

# تشغيل آخر الفشل | Run last failures
pytest --lf
```

### 3. الوصول السريع | Quick Access
```bash
# حفظ الأوامر الشائعة | Save common commands
alias test='pytest -v'
alias engines='python engine_hierarchy.py'
alias analyze='python -m fvafk.cli'
```

---

## 🎯 الخطوات التالية | Next Steps

### للمستخدمين الجدد | For New Users
1. ✅ اقرأ README.md | Read README.md
2. ✅ استكشف المحركات | Explore engines
3. ⏭️ جرّب الأمثلة | Try examples
4. ⏭️ اقرأ التوثيق التفصيلي | Read detailed docs

### للمطورين | For Developers
1. ✅ افهم البنية المعمارية | Understand architecture
2. ✅ اقرأ خطة التنفيذ | Read implementation plan
3. ⏭️ اختر مهمة | Pick a task
4. ⏭️ ساهم | Contribute

### للباحثين | For Researchers
1. ✅ اقرأ النظريات الرياضية | Read mathematical theories
2. ✅ افهم البراهين | Understand proofs
3. ⏭️ استكشف إمكانيات النشر | Explore publication opportunities
4. ⏭️ ابنِ على البنية الموجودة | Build on existing foundation

---

## 📞 الحصول على المساعدة | Getting Help

### المشاكل الشائعة | Common Issues
راجع قسم "استكشاف الأخطاء" أعلاه | See "Troubleshooting" section above

### التقارير | Reporting
- **الأخطاء | Bugs**: افتح issue على GitHub | Open GitHub issue
- **الأسئلة | Questions**: راجع التوثيق أولاً | Check documentation first
- **المساهمات | Contributions**: مرحب بها! | Welcome!

---

**تم التحديث | Last Updated**: 2026-02-04  
**الإصدار | Version**: 2.0.0

**والله الموفق** | **Good luck!** 🚀
