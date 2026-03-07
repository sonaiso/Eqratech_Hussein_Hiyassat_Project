# FVAFK — Where We Are vs Plan (Detailed Expert Report)

**Report Date:** Updated to current snapshot  
**Version:** bayan-fvafk 0.1.0  
**Test Count:** 799 passed, 16 skipped, 0 failed

---

## 1. Plan Reference

| Document | Scope |
|----------|--------|
| **🎯 خطة شاملة لبناء المحركات اللغوية الحقيقية.md** | 6 phases (Infrastructure → Gates → Morphology → Syntax → Constraints → Integration) |
| **MASTER_PLAN_CHECKLIST.md** | Parts 1–6 (foundation → integration) |
| **ENHANCED_ROADMAP.md** | 6-sprint timeline, deliverables |
| **WHERE_WE_ARE_VS_PLAN_2026-03-02.md** | Short snapshot and metrics |

---

## 2. What We Did So Far

### 2.1 Sprint 1: Foundation and Packaging (100%)

| Task | Done | Evidence |
|------|------|----------|
| 1.1 pyproject.toml | Yes | Package bayan-fvafk, entry point fvafk |
| 1.2 Typed library | Yes | src/fvafk, pip install -e . |
| 1.3 Pydantic models | Yes | app/models/ (Unit, Syllable, WordForm, Link, Evidence, ProofArtifact, AnalysisResult) |
| 1.4 OrthographyAdapter + FormCodecV2 | Yes | Reversible encode/decode, tests |
| 1.5 Directories | Yes | theories/, docs/, app/, app/models/ |
| 1.6 Docs | Yes | README, PROJECT_STATUS, WHERE_WE_ARE docs |
| 1.7 CLI JSON + syntax | Yes | word_forms, links.isnadi in output |
| 1.8 10+ CLI tests | Yes | test_cli_comprehensive.py (13+) |
| 1.9 CLI schema | Yes | docs/CLI_SCHEMA.md |

### 2.2 Sprint 2: Phonology Unification (100%)

| Task | Done | Evidence |
|------|------|----------|
| 2.1.1 GateResult canonical | Yes | gate_framework.py: GateDelta, input_units, output_units, delta, time_ms |
| 2.1.2 Unify gates | Yes | BaseGate, 11 gates, PhonologicalGate alias |
| 2.2.1 Syllabifier reference | Yes | syllabifier.py docstring, c2b/README.md |
| 2.2.2 Syllabifier tests | Yes | test_syllabifier_vs_phonology_v2.py (16 tests) |
| 2.3.1 Property tests | Yes | test_gate_properties.py (25, Hypothesis) |
| 2.4.1 Trace | Yes | phonology_trace.py, test_phonology_trace.py (15 tests) |
| 2.5.1 Coq skeletons | Yes | coq/Gates/GateSukun.v, GateShadda.v, GateTanwin.v |
| 2.6.1 CI | Yes | .github/workflows/ci.yml (pytest + coqc; optional generate_enriched_catalog.sh) |
| 2.7 Cleanup & PHONOLOGY.md | Yes | docs/PHONOLOGY.md, .gitignore Coq artifacts |

### 2.3 Morphology & Root Pipeline (Core Done)

| Area | Done | Evidence |
|------|------|----------|
| Word boundary (Plan A) | Yes | word_boundary_detector, pattern_matcher |
| Pattern / classifier / features | Yes | pattern_matcher, word_classifier, features |
| Root extraction | Yes | RootExtractor, RootResolver (CLI → Wazn → Heuristic), RootsDB |
| Canonicalization | Yes | بون→بين, شوء→شيء in resolver; is_rootlike + denylist |
| NO_ROOT_TOKENS | Yes | Manual stoplist (particles, relative pronouns); حتى, كأن, ذي/ذين; test_root_extractor_no_root_tokens.py |
| Full-Quran script | Yes | run_ayat_full_quran.py, analyze_root_sources.py |
| Operators catalog | Yes | OperatorsCatalog + SpecialWordsDatabase prefer enriched CSV; test_operators_catalog_prefers_enriched.py; scripts/generate_enriched_catalog.sh |

### 2.4 Operator Enrichment & Grammar Dataset

| Area | Done | Evidence |
|------|------|----------|
| Enrichment pipeline | Yes | read_inputs_for_enrichment_pipeline.py: quran_i3rab.csv → evidence; NEG+مَا / GEN filtered fallback; OPERATOR_NAME_HINTS |
| Enriched CSV | Yes | data/operators_catalog_split_enriched.csv (signature, usage, evidence) |
| Grammar test dataset | Yes | data/arabic_grammar_test.csv; test_arabic_grammar_test_dataset.py (scoped); test_arabic_grammar_test_dataset_all_lines.py (jar/oath/rubba, 19 validated) |
| REPO_ROOT / paths | Yes | parents[1] in grammar tests; pipeline uses _REPO_ROOT for data/ |

---

## 3. Current State

- **Tests:** 799 passed, 16 skipped, 0 failed
- **Package:** bayan-fvafk 0.1.0
- **Coq:** 3 skeletons compile from repo root (no proofs)
- **CI:** .github/workflows/ci.yml (Python 3.10–3.12 + Coq; optional enriched catalog generation step)
- **C1/C2a:** Done. **C2b (morphology):** Core done (root pipeline, canonicalize, NO_ROOT_TOKENS, operators prefer enriched). **Syntax:** ISNADI only, not in CLI. **Constraints / C2c:** Not started.

---

## 4. Master Plan Alignment

| Part | Status |
|------|--------|
| Part 1 (Foundation) | ✅ Done |
| Part 2 (Phonology + Coq) | ✅ Done (skeletons only for Coq) |
| Part 2.5 (Semantic gates) | 🔴 Not started |
| Part 3 (Morphology) | ✅ Core done (no corpus F1 metric) |
| Part 4 (Syntax TADMINI/TAQYIDI) | 🟡 ISNADI only |
| Part 5 (Constraints) | 🔴 Not started |
| Part 6 (Integration) | 🟡 CLI + C2b + root pipeline; no corpus/C2c |

---

## 5. Next Steps (Priority)

1. **Syntax in CLI (high):** Build WordForms from C2b, call IsnadiLinker, set `result["syntax"]`.
2. **Docs (high):** Keep README and WHERE_WE_ARE in sync; test count 799+.
3. **TADMINI / TAQYIDI (medium):** Implement linkers and small SyntacticParser.
4. **Constraint stubs (medium):** Add constraint modules and validator.
5. **Corpus and metrics (medium):** Trial corpus + F1 for morphology, UAS/LAS when syntax is in pipeline.
6. **Regression tests (low):** Keep grammar dataset and NO_ROOT_TOKENS smoke tests green.

---
*Run: `pytest -q` for current test count. See WHERE_WE_ARE_VS_PLAN_2026-03-02.md for executive summary and metrics.*
