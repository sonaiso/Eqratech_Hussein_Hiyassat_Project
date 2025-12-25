# مشروع إقرأتك العربية (Eqratech Arabic Diana Project)

## نظرة عامة / Overview

**مشروع إقرأتك العربية** هو نظام متكامل لمعالجة اللغة العربية الطبيعية (NLP) يهدف إلى بناء محركات شاملة لتحليل وتوليد النصوص العربية بدقة عالية. يركز المشروع على الجوانب الصوتية والصرفية والنحوية والبلاغية للغة العربية.

**Eqratech Arabic Diana Project** is a comprehensive Arabic Natural Language Processing (NLP) system aimed at building advanced engines for analyzing and generating Arabic texts with high accuracy. The project focuses on phonetic, morphological, syntactic, and rhetorical aspects of the Arabic language.

### الأهداف الرئيسية / Core Objectives

- **تحليل شامل للنصوص العربية**: معالجة دقيقة للفونيمات، الحركات، والتراكيب النحوية
- **توليد الجمل**: إنشاء جمل عربية صحيحة نحوياً وبلاغياً
- **التصنيف النحوي**: تصنيف آلي للعناصر النحوية والصرفية
- **معالجة القرآن الكريم**: تطبيق نماذج التعلم العميق على النصوص القرآنية

## البنية المعمارية المزدوجة / Dual Architecture

يجمع المشروع بين نهجين متكاملين:

1. **محركات Python العملية** (Practical NLP Engines): 68+ محرك لتحليل وتوليد النصوص
2. **نواة Coq الرياضية** (Formal Verification Kernel): نظام إثبات رياضي يتحقق من صحة المخرجات

The project combines two complementary approaches:

1. **Python Practical Engines**: 68+ engines for text analysis and generation
2. **Coq Mathematical Kernel**: Formal verification system ensuring correctness

### نموذج التحقق / Verification Model

```
محرك Python → شهادة JSON → التحقق بـ Coq → قبول/رفض
Python Engine → JSON Certificate → Coq Verification → Accept/Reject
```

## الميزات الرئيسية / Key Features

### 1. محركات النحو الشاملة (68+ محرك متخصص)

المشروع يحتوي على أكثر من 68 محرك متخصص يغطي جميع جوانب النحو العربي:

#### أ. المحركات الصوتية (Phonetic Engines)
- **محرك الفونيمات** (`phonemes_engine.py`): معالجة الأصوات العربية الأساسية (28 حرف + الهمزات)
- **محرك الحركات** (`harakat_engine.py`): معالجة الحركات (فتحة، ضمة، كسرة، سكون، تنوين، شدة)
- **محرك الأصوات المحدثة** (`aswat_muhdatha_engine.py`): معالجة الأصوات الحديثة

#### ب. المحركات الصرفية (Morphological Engines)
- **محرك الأفعال** (`verbs_engine.py`): الأفعال الماضي والمضارع والأمر
- **محرك اسم الفاعل** (`active_participle_engine.py`): أوزان اسم الفاعل (فاعل، مُفَاعِل، إلخ)
- **محرك اسم المفعول** (`passive_participle_engine.py`): أوزان اسم المفعول
- **محرك الصفة المشبهة** (`adjective_engine.py`): الصفات وأوزانها
- **محرك اسم التفضيل** (`superlative_engine.py`): صيغ المبالغة والتفضيل
- **محرك المصدر الصناعي** (`masdar_sinai_engine.py`): المصادر الصناعية
- **محرك التصغير** (`tasgheer_engine.py`): أوزان التصغير
- **محرك النسبة** (`nisba_engine.py`): النسب (مصري، دمشقي، إلخ)

#### ج. المحركات النحوية (Syntactic Engines)
- **محرك الفاعل** (`fael_engine.py`): تحليل الفاعل وأنواعه
- **محرك المفعول به** (`mafoul_bih_engine.py`): المفعول به
- **محرك المفعول لأجله** (`mafoul_ajlih_engine.py`): المفعول لأجله
- **محرك المفعول المطلق** (`mafoul_mutlaq_engine.py`): المفعول المطلق
- **محرك نائب الفاعل** (`naeb_fael_engine.py`): نائب الفاعل والبناء للمجهول
- **محرك المبني للمجهول** (`mabni_majhool_engine.py`): الأفعال المبنية للمجهول
- **محرك المبتدأ والخبر** (`mobtada_khabar_engine.py`): الجملة الاسمية
- **محرك الحال** (`haal_engine.py`): الحال وأنواعها
- **محرك التمييز** (`tamyeez_engine.py`): التمييز
- **محرك البناء** (`binaa_engine.py`): الكلمات المبنية

#### د. محركات الضمائر والإشارة (Pronouns & Demonstratives)
- **محرك أسماء الإشارة** (`demonstratives_engine.py`): هذا، هذه، ذلك، تلك، إلخ
- **محرك أسماء الموصول**: الذي، التي، اللذان، إلخ
- **محرك الضمائر**: الضمائر المتصلة والمنفصلة

#### هـ. محركات الأعلام والأسماء (Proper Nouns & Names)
- **محرك أعلام الأشخاص** (`a3lam_ashkhas_engine.py`): أسماء الأشخاص
- **محرك أعلام الأماكن** (`a3lam_amakin_engine.py`): أسماء الأماكن والبلدان
- **محرك أعلام المنقولة** (`a3lam_manqula_engine.py`): الأعلام المنقولة
- **محرك أسماء الله الحسنى** (`asma_allah_engine.py`): أسماء الله تعالى
- **محرك أسماء الله المركبة** (`asma_allah_murakkaba_engine.py`): الأسماء المركبة
- **محرك الأسماء العامة** (`generic_nouns_engine.py`): الأسماء العامة
- **محرك أسماء الأعداد** (`adad_names_engine.py`): أسماء الأعداد

#### و. المحركات البلاغية (Rhetorical Engines)
- **محرك التشبيه** (`tashbih_engine.py`): أساليب التشبيه
- **محرك الاستعارة** (`istiara_engine.py`): الاستعارات
- **محرك الكناية** (`kinaya_engine.py`): الكناية
- **محرك الجناس** (`jinass_engine.py`): الجناس
- **محرك الطباق** (`tibaq_engine.py`): الطباق
- **محرك المقابلة** (`muqabala_engine.py`): المقابلة البلاغية
- **محرك الطباق والمقابلة** (`tibaq_muqabala_engine.py`): الجمع بينهما
- **محرك السجع** (`saja_engine.py`): السجع
- **محرك الإيجاز والإطناب** (`ijaz_itnab_engine.py`): أساليب الإيجاز والإطناب
- **محرك القصر** (`qasr_engine.py`): أسلوب القصر
- **محرك قصر التقديم** (`qasr_taqdim_engine.py`): القصر بالتقديم
- **محرك التقديم والتأخير** (`taqdim_engine.py`): التقديم والتأخير
- **محرك الترادف** (`taraduf_engine.py`): المترادفات

#### ز. محركات الأساليب الخاصة (Special Constructions)
- **محرك الاستفهام** (`istifham_engine.py`): أدوات الاستفهام
- **محرك النفي**: أدوات النفي
- **محرك الجواب** (`jawab_engine.py`): أساليب الجواب
- **محرك التعجب** (`taajjub_engine.py`): أساليب التعجب
- **محرك الاشتغال** (`ishtighal_engine.py`): أسلوب الاشتغال
- **محرك الأفعال الخمسة** (`afaal_khamsa_engine.py`): الأفعال الخمسة

#### ح. محركات الأوزان والصيغ (Patterns & Forms)
- **محرك اسم الآلة** (`ism_ala_engine.py`): أوزان اسم الآلة (مِفعال، مِفعل، إلخ)
- **محرك اسم الهيئة** (`ism_hay_a_engine.py`): اسم الهيئة
- **محرك اسم المرة** (`ism_marra_engine.py`): اسم المرة
- **محرك الأسماء الميمية** (`mimi_nouns_engine.py`): الأسماء التي تبدأ بالميم
- **محرك الاسم الممدود** (`ism_mamdod_engine.py`): الأسماء الممدودة
- **محرك الاسم المنقوص** (`ism_manqus_engine.py`): الأسماء المنقوصة
- **محرك الاسم المقصور** (`ism_maqsor_engine.py`): الأسماء المقصورة
- **محرك صيغة المبالغة** (`mubalagh_sigha_engine.py`): صيغ المبالغة

#### ط. محركات الجنس والعدد (Gender & Number)
- **محرك الجنس** (`gender_engine.py`): التذكير والتأنيث
- **محرك الجنس الإفرادي** (`jins_ifradi_engine.py`): المفرد
- **محرك الجنس الجمعي** (`jins_jamii_engine.py`): الجمع
- **محرك الكائنات العاقلة** (`kainat_aqila_engine.py`): أسماء العقلاء
- **محرك الكائنات غير العاقلة** (`kainat_ghair_aqila_engine.py`): أسماء غير العقلاء

#### ي. محركات أخرى (Other Engines)
- **محرك الحروف** (`particles_engine.py`): حروف الجر والعطف والنصب والجزم
- **محرك الصوت** (`sound_engine.py`): معالجة الأصوات
- **محرك الأماكن** (`place_engine.py`): ظروف المكان
- **محرك المصطلحات الشرعية** (`musatalahat_sharia_engine.py`): المصطلحات الإسلامية
- **محرك الخصائص المشتركة** (`common_attributes_engine.py`): الخصائص العامة

### 2. مولدات الجمل (Sentence Generators)

المشروع يوفر ثلاثة مستويات من توليد الجمل:

- **المولد البسيط** (`simple_sentence_generator.py`): توليد جمل بسيطة
- **المولد الشامل** (`comprehensive_sentence_generator.py`): توليد جمل معقدة باستخدام جميع المحركات (حتى 5000 جملة)
- **المولد المحسن** (`enhanced_sentence_generation_engine.py`): توليد جمل محسنة مع قواعد استبعاد للتراكيب غير الصحيحة
- **المولد الثابت** (`static_sentence_generator.py`): توليد جمل ثابتة لأغراض الاختبار

### 3. تصدير البيانات (Data Export)

- **المحرك الرئيسي** (`Main_engine.py`): تجميع جميع المحركات وتصديرها إلى ملف Excel واحد
- **التصدير الكامل** (`export_full_multilayer_grammar_minimal.py`): تصدير قواعد النحو متعددة الطبقات
- **ملف Excel شامل** (`full_multilayer_grammar.xlsx`): يحتوي على 68+ ورقة عمل، كل ورقة تمثل محرك نحوي

### 4. معالجة القرآن الكريم (Quran Processing)

- **إعداد البيانات** (`scripts/prepare_quran_dataset.py`): تطبيع نصوص القرآن وإنشاء مجموعات التدريب والتحقق والاختبار
- **التدريب بالترانسفورمر** (`scripts/train_transformer_quran.py`): تدريب نماذج Transformer على النصوص القرآنية
- **دفتر ملاحظات Colab** (`notebooks/quran_transformer.ipynb`): سير عمل التدريب على Google Colab
- **البيانات**: نص القرآن الكريم المحسن مع التشكيل الكامل

### 5. خادم الويب (Web Server)

- **API بتقنية FastAPI** (`run_server.py`): خادم ويب لتصنيف النحو العربي
- **نقاط النهاية RESTful**: واجهات برمجية للتفاعل مع المحركات المختلفة
- **إمكانية إعادة التحميل**: وضع التطوير مع إعادة التحميل التلقائي

### 6. أدوات المقارنة والتحليل (Analysis Tools)

- **مقارنة المحركات** (`engine_comparison_report.py`): إنشاء تقارير مقارنة بين المحركات المختلفة
- **مقارنة الفونيمات** (`compare_phonemes_to_export.py`): مقارنة البيانات الصوتية
- **أدوات إعادة البناء** (`reconstruction_utils.py`): أدوات مساعدة لإعادة بناء البيانات

## البنية المعمارية / Architecture

```
الفونولوجيا (Phonology) → الصرف (Morphology) → النحو (Syntax) → البلاغة (Rhetoric)
     ↓                          ↓                      ↓                    ↓
الفونيمات والحركات          الأوزان والصيغ           التراكيب النحوية      الأساليب البلاغية
```

### سير العمل (Pipeline Flow)

1. **المستوى الصوتي**: تحليل الفونيمات والحركات
2. **المستوى الصرفي**: تحديد الأوزان والصيغ
3. **المستوى النحوي**: تحليل التراكيب النحوية
4. **المستوى البلاغي**: تحديد الأساليب البلاغية
5. **التصدير والتوليد**: إنشاء البيانات والجمل
6. **التحقق الرياضي** (اختياري): التحقق من صحة المخرجات بواسطة نواة Coq

## التحقق الرسمي / Formal Verification

### نواة Coq (Coq Kernel)

المشروع يتضمن نواة رياضية مبنية على Coq لإثبات صحة التراكيب اللغوية:

- **المبدأ الفراكتالي**: كل بنية لغوية تتبع نمط C1-C2-C3
- **القيود الثابتة** (Invariants):
  - لا صامت بدون صائت/حركة
  - لا بداية مركبة (CC onset)
  - مبدأ OCP (Obligatory Contour Principle)
  - كل دور دلالي يجب أن يكون مرخصاً من C2
  
**الموقع**: `coq/theories/ArabicKernel/`

**الاستخدام**:
```python
from coq_bridge import verify_construct, ConstructCertificate, Phoneme, C2Spec, RoleFilling

cert = ConstructCertificate(
    word="كَتَبَ",
    phonemes=[Phoneme(consonant="ك", haraka="َ"), ...],
    c2_spec=C2Spec(kind="VERB", voice="ACTIVE", valency="V1"),
    roles=[RoleFilling(role="AGENT", filled=True), ...]
)

is_valid, message = verify_construct(cert)
```

**البناء** (Build):
```bash
cd coq
make
```

**الوثائق**: انظر `coq/README.md` للتفاصيل الكاملة

## البدء السريع / Getting Started

### المتطلبات المسبقة / Prerequisites

- **Python**: 3.8 أو أحدث
- **نظام التشغيل**: Windows, Linux, macOS
- **المكتبات**: pandas, openpyxl, FastAPI, uvicorn

### التثبيت / Installation

```bash
# 1. إنشاء بيئة افتراضية
python -m venv .venv

# 2. تفعيل البيئة الافتراضية
# على Windows:
.venv\Scripts\activate
# على Linux/Mac:
source .venv/bin/activate

# 3. تثبيت المتطلبات
pip install -r requirements.txt

# 4. تثبيت متطلبات التطوير (اختياري)
pip install -r requirements-dev.txt
```

### الاستخدام السريع / Quick Start

#### 1. تصدير جميع المحركات إلى Excel
```bash
python Main_engine.py
```
سيتم إنشاء ملف `full_multilayer_grammar.xlsx` يحتوي على جميع البيانات النحوية.

#### 2. توليد جمل شاملة
```bash
python comprehensive_sentence_generator.py
```

#### 3. تشغيل خادم الويب
```bash
python run_server.py
# أو مع إعادة التحميل التلقائي:
python run_server.py --reload
```
الخادم سيعمل على: `http://127.0.0.1:8000`

#### 4. إعداد بيانات القرآن
```bash
python scripts/prepare_quran_dataset.py
```

#### 5. التحقق الرسمي (اختياري)
```bash
# Build Coq kernel
cd coq
make

# Verify a construct from Python
cd ..
python -c "from coq_bridge import *; print(verify_construct(...))"
```

## بنية المشروع / Project Layout

```
.
├── *_engine.py              # 68+ محرك نحوي متخصص
├── Main_engine.py            # المحرك الرئيسي لتجميع البيانات
├── reconstruction_utils.py   # أدوات إعادة البناء
├── coq_bridge.py            # جسر Python-Coq للتحقق الرسمي
├── comprehensive_sentence_generator.py  # مولد الجمل الشامل
├── enhanced_sentence_generation_engine.py  # مولد الجمل المحسن
├── run_server.py            # خادم FastAPI
├── coq/                     # نواة التحقق الرسمي Coq
│   ├── theories/ArabicKernel/
│   │   ├── FractalCore.v   # النمط الفراكتالي C1-C2-C3
│   │   ├── Roles.v          # نظام الأدوار الدلالية
│   │   ├── SlotsTable.v     # جدول الفتحات (Slots)
│   │   └── All.v            # التصدير الشامل
│   ├── Makefile             # بناء Coq
│   └── README.md            # وثائق التحقق الرسمي
├── data/                    # بيانات المشروع
│   └── quran/              # نصوص القرآن الكريم
├── scripts/                 # البرامج النصية
│   ├── prepare_quran_dataset.py
│   └── train_transformer_quran.py
├── notebooks/               # دفاتر Jupyter
│   └── quran_transformer.ipynb
├── tests/                   # الاختبارات
│   └── test_arabic_normalization.py
├── docs/                    # الوثائق
├── configs/                 # ملفات الإعداد
├── *.csv                    # بيانات CSV للفونيمات والحركات
└── full_multilayer_grammar.xlsx  # ملف Excel الشامل
```

## ملفات البيانات / Data Files

### ملفات CSV
- `Phonemes.csv` / `الفونيمات.csv`: بيانات الفونيمات (28 حرف + الهمزات)
- `Harakat.csv` / `الحركات.csv`: بيانات الحركات (فتحة، ضمة، كسرة، إلخ)
- `broken_plurals.csv` / `جمع التكسير معدّل.csv`: جموع التكسير
- `demonstrative_pronouns.csv` / `اسم_الاشارة.csv`: أسماء الإشارة
- `coordinating_conjunctions.csv`: حروف العطف
- `interrogative_tools_categories.csv`: أدوات الاستفهام
- `preposition_meanings.csv`: معاني حروف الجر
- `present_naseb_tools.csv`: أدوات نصب المضارع
- `tool_negatives.csv`: أدوات النفي

## الاختبار / Testing

```bash
# تشغيل الاختبارات
pytest

# تشغيل اختبارات محددة
pytest tests/test_arabic_normalization.py

# تشغيل مع التفاصيل
pytest -v
```

## المساهمة / Contributing

نرحب بالمساهمات! يرجى اتباع المعايير التالية:

- **الترميز**: استخدم UTF-8 لجميع الملفات
- **التنسيق**: اتبع PEP 8 للكود Python
- **التعليقات**: استخدم العربية أو الإنجليزية حسب السياق
- **الاختبارات**: أضف اختبارات لأي ميزة جديدة

## الترخيص / License

هذا المشروع مملوك لمشروع إقرأتك العربية. جميع الحقوق محفوظة.

## إحصائيات المشروع / Project Statistics

- **عدد المحركات النحوية**: 68+ محرك متخصص
- **عدد الأسطر البرمجية**: ~5,500 سطر في الملفات الرئيسية
- **عدد ملفات البيانات**: 20+ ملف CSV
- **اللغات المدعومة**: العربية الفصحى
- **التقنيات**: Python, pandas, FastAPI, Transformers

---
آخر تحديث: 2025-12-24
