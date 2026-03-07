# Where We Are vs Plan — Snapshot (updated)

This report maps the **current project state** to the master plan in **🎯 خطة شاملة لبناء المحركات اللغوية الحقيقية.md**. It is a snapshot for steering and prioritisation.

**Reference:** Plan = 6 phases (Infrastructure → Gates → Morphology → Syntax → Constraints → Integration), 16–17 weeks, SMART goals (tests, F1, UAS, Coq, performance, docs).

**Current baseline:** **799 passed, 16 skipped, 0 failed**. CLI C1→C2a→C2b (+ Phonology V2, morphology); WordForm + ISNADI in CLI; root extraction pipeline with RootResolver (CLI → Wazn → Heuristic), canonicalization (بون→بين, شوء→شيء), and full-Quran script; RootExtractor NO_ROOT_TOKENS (particles, relative pronouns); operator enrichment pipeline (read_inputs_for_enrichment_pipeline.py) with NEG/GEN evidence filtering; grammar test dataset (arabic_grammar_test.csv) and validation tests; Sprint 2 complete (gate unification, Coq skeletons); no Coq proofs yet; no C2c/Meaning/Corpus.

---

## 1. Executive summary

| Area | Plan target | Current state | Status |
|------|-------------|---------------|--------|
| **Tests** | 300+ tests, 95%+ pass | 799 pass, 16 skipped, 0 fail | 🟢 Target exceeded |
| **C1 (Infrastructure)** | Segment inventory, syllable system, gate framework, OrthographyAdapter | All present; no Coq | 🟢 Done |
| **C2a (10 gates)** | 10 gates, 100+ tests, Coq | 11 gates unified with BaseGate, property tests, Coq skeletons | 🟢 Done |
| **C2b (Morphology)** | Word boundary, pattern, classifier, root, features, F1≥0.85 | Plan A boundaries; pattern/classifier/root/features; RootResolver (CLI + Wazn + Heuristic), canonicalize, denylist; no corpus F1 | 🟢 Core done; 🟡 no corpus metric |
| **Root extraction** | Root + affixes, accuracy ≥80% | RootResolver with RootsDB, WaznAdapter, heuristic; canonicalize in resolver; run_ayat_full_quran + analyze_root_sources | 🟢 Done (no accuracy metric) |
| **Phonology V2** | (Added) | Lattice + witnesses + CLI | 🟢 Done |
| **Syntax (Phase 4)** | ISNADI + TADMINI + TAQYIDI, parser, UAS≥0.80 | ISNADI only; not in CLI; no TADMINI/TAQYIDI | 🟡 Partial |
| **Constraints (Phase 5)** | 5 (or 6) constraints, 0 violations on correct text | Not implemented | 🔴 Not started |
| **C2c / Meaning / Corpus** | Semantic gate, meaning, corpus evaluation | Not implemented | 🔴 Not started |
| **Coq** | 50+ theorems, 100% Qed | 3 Coq skeletons (GateSukun, GateShadda, GateTanwin); CI compiles them | 🟡 Skeletons only |
| **CLI** | `python -m fvafk.cli`, --verbose, --json | Full CLI with --morphology, --phonology-v2, etc. | 🟢 Done |
| **Documentation** | 50,000+ words, 100% coverage | README, deliverables, plan; not measured | 🟡 Partial |

**Overall:** Phases 1–2 are **complete**. Phase 3 (morphology) is **largely done**, including root pipeline and canonicalization. Phase 4 (syntax) is **partial**. Phases 5 and 6 are **not started**.

---

## 2. Recent changes (since last snapshot)

- **Root pipeline:** RootResolver always returns canonicalized roots (بون→بين, شوء→شيء) via `_canonicalize_result`; RootsDB.canonicalize + is_rootlike + denylist; WaznAdapter (FULLMATCH only); heuristic uses is_rootlike and lexical no-root sets.
- **RootExtractor NO_ROOT_TOKENS:** Manual curated stoplist (particles: حتى, كأن, إن, لكن, لعل, ليت, هل, بل, قد, لم, لن, لا; relative pronouns: الذي, التي, الذين, اللذين, ذي, ذين, etc.). Quick exit in `_extract_context`; كأن detected via `startswith("كأ")`; stripped form ذي/ذين → no root. Smoke tests in `tests/c2b/test_root_extractor_no_root_tokens.py` (حتى/كأن → None; مُؤْمِنُونَ → ا-م-ن; كان → root).
- **Operator enrichment pipeline:** `read_inputs_for_enrichment_pipeline.py` builds evidence from quran_i3rab.csv; NEG+مَا early path + filtered GLOBAL (no "لا" evidence); GEN+operator filtered fallback; safe exact-operator match for len≤2 (parenthesized form only); OPERATOR_NAME_HINTS for كَ, مُذْ, حَتَّى, etc. Output: `data/operators_catalog_split_enriched.csv`.
- **Grammar test dataset:** `data/arabic_grammar_test.csv` (lineno, sentence, explanation); REPO_ROOT fixed to `parents[1]` in `tests/test_arabic_grammar_test_dataset.py`; `tests/c2b/test_arabic_grammar_test_dataset_all_lines.py` validates jar/oath/rubba targets (19 validated, 82 skipped other chapters).
- **Scripts:** `run_ayat_full_quran.py` default input set to `data/quran/quran-simple-enhanced.txt`; `scripts/analyze_root_sources.py` (report + optional Tanzil comparison with canonicalization).
- **Tests:** Orthography tests use `strip_diacritics=True`; feature-extractor test accepts multiple case values; pattern-matcher tests skip when pattern is None; `TestDataPatternDatabase` → `AwzanTestPatternDatabase`; i3rab/grammar tests use `data/quran_i3rab.csv` and project `data/` paths; `test_operators_catalog_prefers_enriched.py` ensures enriched CSV is chosen when both exist.
- **Operators catalog:** `OperatorsCatalog` and `SpecialWordsDatabase` (operators_particles_db) prefer `data/operators_catalog_split_enriched.csv` then fallback to plain; `FVAFK_OPERATORS_CSV` supported; docstring + README note and `scripts/generate_enriched_catalog.sh` for CI/local generation.

---

## 3. Plan goals (quick reference)

- **Architecture:** Strict separation C1 → C2a → C2b → C2c → C3.
- **Targets:** Gates 10, 100+ tests; Morphology F1 ≥ 0.85; Syntax UAS ≥ 0.80; Constraints 5–6, 0 violations; Coq 50+ theorems; Tests 300+, 95%+ pass; Performance 1000 words/s; Documentation 50,000+ words.

---

## 4. Phase-by-phase status

| Phase | Plan | Current | Status |
|-------|------|---------|--------|
| **1. Infrastructure** | C1, inventory, syllable, gate framework, orthography, codec, trace | Implemented; no Coq | ✅ Done |
| **2. Gates** | 10 gates, 100+ tests, Coq | 11 gates, tests; Coq skeletons only | ✅ Done |
| **3. Morphology** | Boundaries, pattern, classifier, root, features, F1≥0.85 | Plan A + pattern/classifier/root/features + RootResolver (CLI/Wazn/heuristic, canonicalize); no F1 | ✅ Core done |
| **4. Syntax** | ISNADI, TADMINI, TAQYIDI, parser, UAS≥0.80 | ISNADI only; not in CLI | 🟡 Partial |
| **5. Constraints** | 5–6 constraints, validator | None | 🔴 Not started |
| **6. Integration** | Pipeline, CLI, corpus, C2c, docs | CLI + C2b + root pipeline; no corpus/C2c/full docs | 🟡 Partial |

---

## 5. What is in the plan but not in this repo

- **Coq:** No proofs (only skeletons).
- **Word boundary Plan B:** From syllable stream; only Plan A implemented.
- **TADMINI and TAQYIDI:** Only ISNADI implemented.
- **SyntacticParser:** No single parser (ISNADI → TADMINI → TAQYIDI).
- **Syntax in CLI:** No WordForms from C2b, no `result["syntax"]`.
- **All 5 (or 6) constraints:** None implemented.
- **C2c (semantic gate):** Not implemented.
- **C3 / Meaning, event extraction:** Not in repo.
- **Corpus evaluation:** No F1/UAS/LAS on a designated corpus.
- **Property-based tests:** No Hypothesis tests for idempotence/reversibility at scale.

---

## 6. Recommended next steps (priority)

1. **Syntax in CLI (high):** Build WordForms from C2b, call IsnadiLinker, set `result["syntax"]`.
2. **Update docs (high):** Align README and plan “ما لدينا / ما ينقصنا” with this snapshot; set test count to 790+.
3. **TADMINI / TAQYIDI (medium):** Implement linkers and a small SyntacticParser.
4. **Constraint stubs (medium):** Add constraint modules and validator.
5. **Corpus and metrics (medium):** Trial corpus + F1 for morphology, UAS/LAS for syntax when available.
6. **Corpus and regression tests (low):** Keep grammar dataset and NO_ROOT_TOKENS smoke tests green as data evolves.

---

## 7. Summary

| Metric | Plan | Current |
|--------|------|---------|
| Tests | 300+, 95%+ pass | 799 pass, 16 skipped, 0 fail |
| Root pipeline | Accuracy ≥80% | RootResolver + canonicalize; no metric |
| Morphology F1 | ≥ 0.85 | Not measured |
| Syntax UAS | ≥ 0.80 | N/A (syntax not in pipeline) |
| Constraints | 5–6, 0 violations | Not started |
| Coq | 50+ theorems | Skeletons only |

This document should be updated whenever a major phase is completed or success criteria are redefined.
