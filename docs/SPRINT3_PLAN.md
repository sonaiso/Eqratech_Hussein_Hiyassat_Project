# SPRINT3_PLAN.md — Morphology Layer

**Sprint:** 3 of 6  
**Branch:** sprint3/morphology-layer  
**Prerequisites:** Sprint 1 ✅ Sprint 2 ✅ (373 tests passing)  
**Goal:** Build morphological analysis layer with word boundaries, root/pattern extraction, and feature tagging

---

## Overview

Sprint 3 implements the morphology layer (Part 3 of MASTER_PLAN_CHECKLIST.md), focusing on:

1. **Word Boundary Detection** — Segment Arabic text into words
2. **Pattern Catalog** — Extract roots and patterns (فَعَلَ، فَاعِل، etc.)
3. **Morphological Flags** — Tag definiteness, gender, number, case
4. **Gold Corpus** — Annotated dataset with F1 ≥ 0.85 target

---

## Success Criteria

| Metric | Target |
|--------|--------|
| Word boundary F1 | ≥ 0.85 |
| Pattern catalog coverage | ≥ 20 patterns |
| Gold corpus size | ≥ 200 words |
| New tests | ≥ 100 |
| Coq skeletons | ≥ 2 files |

---

## Tasks

### 3.1 Word Boundary Detector

**Goal:** Segment Arabic text into words, handling clitics and compounds

#### 3.1.1 Implement Plan B Algorithm
- **Description:** Simpler rule-based algorithm (fallback from ML approach)
- **Approach:**
  - Detect common prefixes: ال (definite), و/ف/ب/ك/ل (conjunctions/prepositions)
  - Detect common suffixes: ها/هم/هن/ك/كم/كن (pronouns)
  - Handle compound cases (والكتاب → و + ال + كتاب)
- **Files:**
  - `src/fvafk/c3/word_boundary.py` — `WordBoundaryDetector` class
  - `src/fvafk/c3/__init__.py` — Module init
- **Tests:** `tests/test_word_boundary.py` (30+ cases)
- **Acceptance:**
  - Correctly segments 10 test sentences
  - Handles edge cases (no clitics, multiple clitics, compounds)

#### 3.1.2 Handle Clitics
- **Description:** Extract and classify clitics
- **Clitics to handle:**
  - **Prefixes:** ال، و، ف، ب، ك، ل
  - **Suffixes:** ها، هم، هن، ك، كم، كن، ي، نا
- **Output:** `CliticAnalysis` model with prefix/stem/suffix
- **Tests:** `tests/test_clitics.py` (20+ cases)
- **Acceptance:**
  - Correctly identifies clitics in 95% of test cases
  - Handles ambiguous cases (هل vs ه + ل)

#### 3.1.3 Integration with Pipeline
- **Description:** Connect to existing phonology pipeline
- **Input:** `AnalysisResult` from phonology layer
- **Output:** `MorphologicalAnalysis` with word boundaries
- **Files:**
  - Update `app/models/analysis.py` — Add `MorphologicalAnalysis` model
  - Update `app/cli.py` — Add `--morphology` flag
- **Tests:** `tests/test_morphology_integration.py` (15+ cases)
- **Acceptance:**
  - CLI outputs word boundaries in JSON
  - Backward compatible (morphology is optional)

#### 3.1.4 Gold Annotations (Word Boundaries)
- **Description:** Create gold-standard annotations for evaluation
- **Format:** JSON with `{text, boundaries: [{start, end, word}]}`
- **Files:** `data/gold/word_boundaries.json`
- **Size:** 50-100 sentences
- **Acceptance:**
  - Manual review by 2 annotators
  - Inter-annotator agreement ≥ 0.90

---

### 3.2 Pattern Catalog

**Goal:** Extract roots and identify morphological patterns

#### 3.2.1 Root Extraction Logic
- **Description:** Extract trilateral/quadrilateral roots
- **Approach:**
  - Strip prefixes/suffixes
  - Remove vowels/diacritics
  - Identify 3-4 consonant root
- **Files:** `src/fvafk/c3/root_extractor.py`
- **Tests:** `tests/test_root_extraction.py` (40+ cases)
- **Acceptance:**
  - Correctly extracts roots from 20 known words
  - Handles irregular roots (أخذ، قال، etc.)

#### 3.2.2 Pattern Templates
- **Description:** Catalog of common Arabic patterns
- **Patterns to include:**
  - **Verbs:** فَعَلَ، فَعَّلَ، فَاعَلَ، أَفْعَلَ، تَفَعَّلَ، اِنْفَعَلَ، اِسْتَفْعَلَ
  - **Nouns:** فَاعِل، مَفْعُول، مَفْعَل، فَعِيل، فُعَال
- **Files:** `src/fvafk/c3/pattern_catalog.py`
- **Format:** `Pattern` class with template string and morphological features
- **Tests:** `tests/test_pattern_catalog.py` (30+ cases)
- **Acceptance:**
  - Catalog contains ≥ 20 patterns
  - Each pattern has examples and tests

#### 3.2.3 Pattern Matching Algorithm
- **Description:** Match words to pattern templates
- **Approach:**
  - Given root + word, identify pattern
  - Use template matching (ف ع ل positions)
  - Return pattern name + morphological features
- **Files:** `src/fvafk/c3/pattern_matcher.py`
- **Tests:** `tests/test_pattern_matching.py` (50+ cases)
- **Acceptance:**
  - Correctly matches 30 known root-pattern pairs
  - Handles ambiguous cases (multiple valid patterns)

#### 3.2.4 Pattern-Based Features
- **Description:** Derive morphological features from patterns
- **Features:**
  - **Voice:** active (مَفْعُول vs فَاعِل)
  - **Aspect:** perfective/imperfective (for verbs)
  - **Transitivity:** transitive/intransitive
- **Files:** Update `app/models/morphology.py` — Add `PatternFeatures` model
- **Acceptance:**
  - Feature extraction covers 15+ patterns
  - Property-based tests verify consistency

---

### 3.3 Morphological Flags

**Goal:** Tag words with morphological features

#### 3.3.1 Flag Data Model
- **Description:** Pydantic models for morphological features
- **Fields:**
  - `definiteness`: definite/indefinite/none
  - `gender`: masculine/feminine/none
  - `number`: singular/dual/plural/none
  - `case`: nominative/accusative/genitive/none
  - `person`: 1st/2nd/3rd/none (for verbs/pronouns)
  - `tense`: past/present/imperative/none (for verbs)
- **Files:** `app/models/morphology.py` — `MorphFlags` class
- **Acceptance:**
  - Model validates correct values
  - JSON serialization works

#### 3.3.2 Feature Extractors
- **Description:** Extract features from word forms
- **Extractors:**
  - `DefinitenessExtractor` — Detect ال prefix
  - `GenderExtractor` — Detect ة، ات، ين endings
  - `NumberExtractor` — Detect plural patterns (أَفْعَال، فِعَال، etc.)
  - `CaseExtractor` — Detect case endings (ُ، َ، ِ، ٌ، ً، ٍ)
- **Files:** `src/fvafk/c3/feature_extractors.py`
- **Tests:** `tests/test_feature_extraction.py` (60+ cases)
- **Acceptance:**
  - Each extractor has 15+ test cases
  - Handles ambiguous/missing diacritics

#### 3.3.3 Integration with WordForm
- **Description:** Add `morph_flags` to `WordForm` model
- **Changes:**
  - Update `app/models/word.py` — Add `morph_flags: Optional[MorphFlags]`
  - Update CLI output to include flags
- **Files:** `app/models/word.py`, `app/cli.py`
- **Acceptance:**
  - CLI outputs morphological flags in JSON
  - Backward compatible (flags are optional)

#### 3.3.4 Property-Based Tests
- **Description:** Use Hypothesis to test morphological invariants
- **Properties to test:**
  - If word has ال prefix, definiteness = definite
  - If word has ة ending, gender likely feminine
  - If word has ُونَ ending, number = plural, gender = masculine
- **Files:** `tests/test_morph_properties.py`
- **Tests:** ≥ 20 property tests
- **Acceptance:**
  - All properties pass on generated examples
  - No false positives on known edge cases

---

### 3.4 Gold Corpus

**Goal:** Build annotated corpus for evaluation

#### 3.4.1 Annotation Format
- **Description:** Design JSON schema for morphological annotations
- **Fields:**
  - `text`: original Arabic text
  - `words`: list of word objects
    - `surface`: surface form
    - `root`: extracted root
    - `pattern`: identified pattern
    - `morph_flags`: morphological features
    - `boundaries`: start/end character positions
- **Files:** `data/gold/schema.json`, `docs/ANNOTATION_FORMAT.md`
- **Acceptance:**
  - Schema validates example annotations
  - Documentation explains each field

#### 3.4.2 Corpus Collection
- **Description:** Annotate 200+ words from diverse sources
- **Sources:**
  - Quranic verses (50 words)
  - News articles (50 words)
  - Literary texts (50 words)
  - Constructed examples (50 words)
- **Files:** `data/gold/corpus.json`
- **Tools:** Create annotation script `tools/annotate_morphology.py`
- **Acceptance:**
  - 200+ words annotated
  - Covers diverse morphological phenomena

#### 3.4.3 Inter-Annotator Agreement
- **Description:** Validate annotation quality
- **Approach:**
  - 2 annotators independently annotate 50 words
  - Calculate agreement (Cohen's Kappa or F1)
  - Resolve disagreements, update guidelines
- **Files:** `docs/ANNOTATION_GUIDELINES.md`
- **Target:** Agreement ≥ 0.90
- **Acceptance:**
  - Agreement report documented
  - Guidelines updated based on disagreements

#### 3.4.4 Evaluation Tools
- **Description:** Measure system performance on gold corpus
- **Metrics:**
  - **Word boundaries:** Precision, Recall, F1
  - **Root extraction:** Accuracy
  - **Pattern matching:** Accuracy
  - **Feature tagging:** Accuracy per feature
- **Files:** `tools/evaluate_morphology.py`
- **Tests:** `tests/test_evaluation.py`
- **Acceptance:**
  - Tool outputs F1 ≥ 0.85 on word boundaries
  - Report shows per-feature performance

---

### 3.5 Coq Formalization (Optional)

**Goal:** Formal proofs for morphological properties

#### 3.5.1 Morphology Predicates
- **Description:** Define predicates for morphological concepts
- **Predicates:**
  - `IsDefinite(word)` — Word has ال prefix
  - `HasRoot(word, root)` — Word derives from root
  - `MatchesPattern(word, pattern)` — Word fits pattern
- **Files:** `coq/Morphology/Predicates.v`
- **Acceptance:**
  - File compiles with `coqc`
  - 3+ predicates defined

#### 3.5.2 Word Boundary Proofs (Skeleton)
- **Description:** Proof skeletons for boundary detection correctness
- **Theorems:**
  - `word_boundary_preserves_text` — Segmentation doesn't lose characters
  - `clitic_boundary_valid` — Clitic boundaries respect grammar
- **Files:** `coq/Morphology/WordBoundary.v`
- **Acceptance:**
  - Theorems stated (admitted for now)
  - Comments explain proof strategy

#### 3.5.3 CI Integration
- **Description:** Add Coq morphology files to CI
- **Changes:** Update `.github/workflows/ci.yml`
- **Acceptance:**
  - CI compiles morphology Coq files
  - No build errors

---

## Timeline (6 weeks)

| Week | Focus | Deliverables |
|------|-------|--------------|
| **1-2** | Word boundaries | 3.1.1–3.1.4 (detector, clitics, integration, annotations) |
| **3-4** | Patterns | 3.2.1–3.2.4 (roots, templates, matching, features) |
| **5** | Features | 3.3.1–3.3.4 (model, extractors, integration, properties) |
| **6** | Corpus & eval | 3.4.1–3.4.4 (format, collection, agreement, evaluation) |
| *Ongoing* | Coq | 3.5.1–3.5.3 (predicates, proofs, CI) |

---

## Dependencies

| From Sprint 2 | Used in Sprint 3 |
|---------------|------------------|
| `Unit` model | Word boundary detection (phoneme sequences) |
| `Syllable` model | Pattern matching (syllable structure) |
| `WordForm` model | Extended with `morph_flags` |
| `AnalysisResult` model | Input to morphological analysis |
| OrthographyAdapter | Convert between representations |

---

## File Structure

```
src/fvafk/c3/
├── __init__.py
├── word_boundary.py      # WordBoundaryDetector
├── root_extractor.py
├── pattern_catalog.py
├── pattern_matcher.py
└── feature_extractors.py

app/models/
├── analysis.py           # + MorphologicalAnalysis
├── morphology.py         # MorphFlags, PatternFeatures, CliticAnalysis
└── word.py               # + morph_flags on WordForm

data/gold/
├── schema.json
├── word_boundaries.json
└── corpus.json

coq/Morphology/
├── Predicates.v
└── WordBoundary.v

docs/
├── ANNOTATION_FORMAT.md
└── ANNOTATION_GUIDELINES.md

tools/
├── annotate_morphology.py
└── evaluate_morphology.py

tests/
├── test_word_boundary.py
├── test_clitics.py
├── test_morphology_integration.py
├── test_root_extraction.py
├── test_pattern_catalog.py
├── test_pattern_matching.py
├── test_feature_extraction.py
├── test_morph_properties.py
└── test_evaluation.py
```
