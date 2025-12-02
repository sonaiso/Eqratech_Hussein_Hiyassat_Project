# AGT Complete - Arabic Grammar Technology Project Documentation

## Project Overview

The **Eqratech Arabic Diana Project** is a comprehensive Arabic Natural Language Processing (NLP) system designed to generate, analyze, and process multi-layered Arabic grammatical data. This project represents a complete Arabic Grammar Technology (AGT) framework that handles phonetic, morphological, syntactic, and semantic aspects of the Arabic language.

## What is AGT_Complete?

AGT_Complete refers to the **complete** Arabic Grammar Technology implementation that encompasses:

- **68+ specialized engine modules** for different grammatical aspects
- **Multi-layer grammar processing** from phonetic to syntactic levels
- **Comprehensive sentence generation** capabilities
- **Full Unicode and UTF-8 support** for Arabic text processing
- **Excel-based data export** with organized grammatical sheets

## System Architecture

### Core Components

#### 1. Base Infrastructure
- **`reconstruction_utils.py`**: Central utility for reconstructing grammatical data with Unicode/UTF-8 encoding
- **`BaseReconstructionEngine`**: Base class inherited by all grammatical engines
- **`Main_engine.py`**: Main orchestration module for engine collection and export

#### 2. Data Processing Layers

The system processes Arabic text through multiple layers:

##### Layer 1: Phonetic Foundation (الأساس الصوتي)
- **Phonemes Engine** (`phonemes_engine.py`): Handles basic phonetic units (consonants, vowels)
- **Harakat Engine** (`harakat_engine.py` / `حركات`): Processes diacritical marks (فتحة، ضمة، كسرة، etc.)
- **Sound Engine** (`sound_engine.py`): Manages sound-related data

##### Layer 2: Particles & Tools (الأدوات والحروف)
Processing grammatical particles including:
- Coordinating conjunctions (العطف)
- Negation tools (النفي)
- Prepositions (الجر)
- Accusative markers (النصب)
- Jussive markers (الجزم)
- Conditional tools (الشرط)
- Restriction markers (القصر)
- Interrogative tools (الاستفهام)
- Emphasis markers (التوكيد)
- Vocative particles (النداء)
- Exception tools (الاستثناء)

##### Layer 3: Nouns & Their Derivatives (الأسماء ومشتقاتها)
Including 40+ noun-related engines:

**Basic Noun Categories:**
- Definiteness (`definiteness_engine.py`)
- Demonstratives (`demonstratives_engine.py`)
- Pronouns (`pronouns_engine.py`)
- Numbers (`adad_engine.py`, `adad_names_engine.py`)
- Dual & Plural forms (`number_gender_suffixes_engine.py`)
- Broken plurals (`brokenplural_templates_engine.py`)

**Derived Forms (المشتقات):**
- Active participle (`active_participle_engine.py`) - اسم الفاعل
- Passive participle (`passive_participle_engine.py`) - اسم المفعول
- Superlative (`superlative_engine.py`) - اسم التفضيل
- Adjectives (`adjective_engine.py`) - الصفات
- Mimetic nouns (`mimi_nouns_engine.py`) - الأسماء الميمية
- Diminutive forms (`tasgheer_engine.py`) - التصغير
- Relative adjectives (`nisba_engine.py`) - النسب
- Industrial source (`masdar_sinai_engine.py`) - المصدر الصناعي
- Exaggeration forms (`mubalagh_sigha_engine.py`) - صيغ المبالغة
- Instance nouns (`ism_marra_engine.py`) - اسم المرة
- State nouns (`ism_hay_a_engine.py`) - اسم الهيئة
- Tool nouns (`ism_ala_engine.py`) - اسم الآلة

**Specialized Categories:**
- Generic nouns (`generic_nouns_engine.py`)
- Proper nouns (`proper_nouns_engine.py`)
- Place names (`place_engine.py`, `a3lam_amakin_engine.py`)
- Personal names (`a3lam_ashkhas_engine.py`)
- Transferred proper nouns (`a3lam_manqula_engine.py`)
- Collective nouns (`jins_jamii_engine.py`)
- Singular nouns (`jins_ifradi_engine.py`)
- Living entities (`kainat_aqila_engine.py`)
- Non-living entities (`kainat_ghair_aqila_engine.py`)
- Divine names (`asma_allah_engine.py`, `asma_allah_murakkaba_engine.py`)
- Religious terms (`musatalahat_sharia_engine.py`)
- Sounds (`aswat_muhdatha_engine.py`)

**Special Noun Forms:**
- Shortened nouns (`ism_maqsor_engine.py`) - الاسم المقصور
- Extended nouns (`ism_mamdod_engine.py`) - الاسم الممدود
- Defective nouns (`ism_manqus_engine.py`) - الاسم المنقوص

##### Layer 4: Verbs & Verbal Constructions (الأفعال)
- Basic verbs (`verbs_engine.py`)
- Five verbs (`afaal_khamsa_engine.py`) - الأفعال الخمسة
- Passive voice (`mabni_majhool_engine.py`)

**Verbal Arguments:**
- Subject (`fael_engine.py`) - الفاعل
- Passive subject (`naeb_fael_engine.py`) - نائب الفاعل
- Direct object (`mafoul_bih_engine.py`) - المفعول به
- Purpose object (`mafoul_ajlih_engine.py`) - المفعول لأجله
- Absolute object (`mafoul_mutlaq_engine.py`) - المفعول المطلق
- Circumstance (`haal_engine.py`) - الحال
- Specification (`tamyeez_engine.py`) - التمييز

##### Layer 5: Syntactic Constructions (التراكيب النحوية)
- Subject-predicate (`mobtada_khabar_engine.py`) - المبتدأ والخبر
- Construction type (`binaa_engine.py`) - البناء
- Engagement (`ishtighal_engine.py`) - الاشتغال
- Common attributes (`common_attributes_engine.py`)
- Gender (`gender_engine.py`)

##### Layer 6: Rhetorical Devices (البلاغة)
- Simile (`tashbih_engine.py`) - التشبيه
- Metaphor (`istiara_engine.py`) - الاستعارة
- Metonymy (`kinaya_engine.py`) - الكناية
- Antithesis (`tibaq_engine.py`) - الطباق
- Contrast (`muqabala_engine.py`) - المقابلة
- Brevity/verbosity (`ijaz_itnab_engine.py`) - الإيجاز والإطناب
- Rhymed prose (`saja_engine.py`) - السجع
- Paronomasia (`jinass_engine.py`) - الجناس
- Synonymy (`taraduf_engine.py`) - الترادف
- Fronting (`taqdim_engine.py`) - التقديم
- Restriction by fronting (`qasr_taqdim_engine.py`) - قصر التقديم
- Exclamation (`taajjub_engine.py`) - التعجب

#### 3. Sentence Generation System

The project includes multiple sentence generation engines:

- **`comprehensive_sentence_generator.py`** (605 lines): 
  - Generates comprehensive Arabic sentences
  - Uses all available engines
  - Implements algorithms to exclude grammatically incorrect constructions
  - Maximum 5000+ sentences for comprehensive coverage

- **`enhanced_sentence_generation_engine.py`** (387 lines):
  - Enhanced sentence generation with advanced features
  - Multi-component sentence construction

- **`sentence_generation_engine.py`** (363 lines):
  - Core sentence generation logic
  - Component-based assembly

- **`simple_sentence_generator.py`** (354 lines):
  - Simplified sentence generation
  - Basic patterns and structures

- **`static_sentence_generator.py`** (311 lines):
  - Static template-based generation

#### 4. Export & Data Management

- **`export_full_multilayer_grammar_minimal.py`** (208 lines):
  - Main export script for multi-layer grammar
  - Generates `full_multilayer_grammar.xlsx` with 70+ sheets
  - Organized from lowest (phonetic) to highest (syntactic) levels
  - Includes Unicode and UTF-8 encoding for all text

- **`Main_engine.py`** (59 lines):
  - Collects all engines dynamically
  - Orchestrates the export process
  - Removes duplicates by sheet name

## Data Files

### CSV Data Files (20+ files)
- `Harakat.csv`, `الحركات.csv`, `الحركات_كامل.csv`: Diacritical marks
- `Phonemes.csv`, `الفونيمات.csv`: Phoneme data
- `broken_plurals.csv`, `جمع التكسير معدّل(1).csv`: Broken plural patterns
- `coordinating_conjunctions.csv`: Conjunction data
- `demonstrative_pronouns.csv`, `اسم_الاشارة.csv`: Demonstrative pronouns
- `interrogative_tools_categories.csv`: Question tools
- `preposition_meanings.csv`: Preposition meanings
- `present_naseb_tools.csv`: Present tense accusative tools
- `tool_negatives.csv`: Negation tools
- Various functional classification files (phonetic, morphological, semantic, syntactic)

### Excel Output
- `full_multilayer_grammar.xlsx`: Comprehensive output with 70+ sheets
- `full_multilayer_grammar1.csv`: CSV export version

## Technical Features

### Unicode & UTF-8 Processing
The system implements comprehensive Unicode support:
- Preserves internal spaces in multi-word tools
- Normalizes hamza/alif forms according to rules
- Generates Unicode representation (U+XXXX format)
- Generates UTF-8 byte representation
- Handles diacritics and special Arabic characters

### Reconstruction Pipeline
Each engine's data passes through `reconstruct_from_base_df()`:
1. Preserves spacing in compound tools
2. Normalizes character forms
3. Infers phonemes and diacritics if missing
4. Generates Unicode representations
5. Generates UTF-8 encodings
6. Cleans formatting issues

### Data Organization
The multi-layer Excel file organizes sheets logically:
1. **Phonetic Foundation** (الأساس الصوتي)
2. **Particles & Tools** (الأدوات)
3. **Nouns at All Levels** (الأسماء)
4. **Verbs & Complements** (الأفعال)
5. **Generated Sentences** (الجُمَل المولدة)

## Generated Sentence Components

The sentence generation sheet (`جُمَل_مولدة`) includes:
- **الأداة**: Complete generated sentence
- **القالب/التركيب**: Structural description (e.g., pronoun+present verb+adverb)
- **النوع**: Type (verbal/nominal/semi-sentence)
- **مكوّنات**: List of components with text values
- **UTF-8 للمكوّنات**: UTF-8 encoding of each sub-element
- **الوظيفة الصوتية**: Phonetic function summary
- **الوظيفة الاشتقاقية**: Derivational function aggregation

## Adding New Engines

To add a new grammatical engine:
1. Create a new engine file inheriting from `BaseReconstructionEngine`
2. Implement `make_df()` returning a DataFrame with at least an "الأداة" column
3. Define `SHEET_NAME` class attribute
4. Import the engine in `export_full_multilayer_grammar_minimal.py`
5. Add to the appropriate list maintaining logical order
6. Run the export script to regenerate Excel file

## Project Statistics

- **68+ Engine Files**: Specialized grammatical processors
- **70+ Excel Sheets**: Comprehensive grammatical data
- **5540+ Total Lines**: Python implementation
- **20+ CSV Files**: Source data and configuration
- **Multi-language Support**: Arabic with full diacritics and Unicode

## Key Technologies

- **Python 3.x**: Primary programming language
- **Pandas**: Data processing and manipulation
- **OpenPyXL**: Excel file generation
- **Unicode/UTF-8**: Full Arabic character support

## Purpose & Applications

This AGT_Complete system can be used for:
- Arabic NLP research and development
- Grammar teaching and learning tools
- Text generation and analysis
- Linguistic database construction
- Arabic language processing applications
- Computational linguistics research

## Conclusion

AGT_Complete represents a comprehensive Arabic Grammar Technology framework that systematically processes and generates Arabic grammatical data across all linguistic levels—from individual phonemes to complete sentences, with full rhetorical device support. The modular architecture allows easy extension and maintenance while ensuring data consistency through centralized reconstruction utilities.
