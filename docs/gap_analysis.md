# Gap Analysis — Target Layers vs Current Codebase

Each target pipeline stage is classified as **EXISTS**, **PARTIAL**, or **MISSING**. This supports Stage 1 (discovery) and later stages (orchestration, placeholders, and documentation).

---

## Status legend

- **EXISTS:** One or more current modules implement the stage’s responsibility; can be wrapped and used as-is or with a thin adapter.
- **PARTIAL:** Some logic exists but is scattered, duplicated, or tied to a different flow; needs a wrapper or a clear “single” implementation choice.
- **MISSING:** No current implementation; stage will be a pass-through or placeholder until added.

---

## Stage 0 — Input acquisition

| Status | Notes |
|--------|--------|
| **PARTIAL** | No dedicated module. Input is handled inside `fvafk/cli/main.py` (argparse, --input FILE, length limits, progress). Scripts open corpus files themselves. Orchestrator can wrap CLI input logic or implement a minimal “read text + metadata” step. |

---

## Stage 1 — Normalization

| Status | Notes |
|--------|--------|
| **PARTIAL** | Multiple normalizers: `orthography_adapter.py` (full orthography rules), `syllabifier.normalize_word()`, `operators_particles_db.normalize_arabic()`, `root_extractor.normalize_hamza_for_roots()`, `cv_pattern.normalize_word()`. No single canonical entry point. Recommendation: treat OrthographyAdapter as the primary normalizer for stage 1; adapters can call domain-specific normalizers where needed. |

---

## Stage 2 — Tokenization

| Status | Notes |
|--------|--------|
| **EXISTS** | `WordBoundaryDetector` in `fvafk/c2b/word_boundary.py` is the main tokenizer (regex, spans). Segmenter and word-2-cv use `split()` or regex. One clear choice for orchestration: WordBoundaryDetector. |

---

## Stage 3 — Segmentation

| Status | Notes |
|--------|--------|
| **PARTIAL** | Two notions: (1) MASAQ `ArabicSegmenter.segment_word()` (full morph segments), (2) fvafk C2a unit stream + C2b affix split. Neither is exposed as a single “segmentation stage” in the main CLI. Stage 3 can wrap C2a units and/or segmenter; contract (e.g. list of segments per token) must be defined. |

---

## Stage 4 — Particles / operators / functional gating

| Status | Notes |
|--------|--------|
| **EXISTS** | `OperatorsCatalog` and `SpecialWordsCatalog` implement operator/special-word detection. Used at start of morphology in CLI. Clear source for “functional gating” stage. |

---

## Stage 5 — Word typing / routing

| Status | Notes |
|--------|--------|
| **EXISTS** | `WordClassifier` (+ mabni, pattern_analyzer) provides kind/type routing (operator, particle, pronoun, verb, noun, demonstrative, name, unknown). Single entry point for this stage. |

---

## Stage 6 — Phonology / CV extraction

| Status | Notes |
|--------|--------|
| **EXISTS** | `fvafk/c1/cv_pattern.py` (C2a-based) and `fvafk/phonology_v2/phonology_adapter.py` both produce CV (and optionally cv_advanced). Two engines; orchestration must choose one or merge. Logic exists; no single “stage 6” API yet. |

---

## Stage 7 — Syllabification

| Status | Notes |
|--------|--------|
| **EXISTS** | `ArabicSyllabifier` in `fvafk/c2b/syllabifier.py` is the designated syllabifier. Single source of truth. Can be wrapped as stage 7. |

---

## Stage 8 — Root hypothesis extraction

| Status | Notes |
|--------|--------|
| **EXISTS** | `RootExtractor.extract_with_affixes()` and `RootResolver.resolve()` (with RootsDB, WaznAdapter, heuristic) implement root hypothesis and resolution. Clear modules for stage 8. |

---

## Stage 9 — Wazn matching

| Status | Notes |
|--------|--------|
| **EXISTS** | `wazn_matcher` + `WaznAdapter` in root_resolver; also `PatternMatcher`/pattern_analyzer. Two code paths; logic exists. Orchestrator should standardize on one (e.g. WaznAdapter) and optionally map to Pattern shape. |

---

## Stage 10 — Syntax / sentence relations

| Status | Notes |
|--------|--------|
| **EXISTS** | `IsnadiLinker` / `find_isnadi_links()` and `SentenceClassifier` provide links and sentence type. Optional: engines/syntax/*. Sufficient for a stage 10 wrapper. **L10 now runs successfully** in tested paths. The prior runtime failure was due to **missing integration helpers** (CLI expected `from_multi_word_item` and `_word_form_to_syntax_dict`); a **minimal compatibility fix** restored the path—`from_multi_word_item` forwards to `from_c2b`, and `_word_form_to_syntax_dict` was added only to expose syntax output in the CLI/orchestrator. **No analyzer logic was rewritten.** |

---

## Stage 11 — i3rab

| Status | Notes |
|--------|--------|
| **EXISTS** | `i3rab_generator.generate_i3rab(WordInfo)` and `enricher._build_i3rab()` (with c2e verb/noun features) implement i3rab generation. CLI already attaches i3rab_text per word. **Live output:** i3rab-related evidence exists under **`c2b.c2e.i3rab_text`** in morphology JSON. Stage 11 i3rab remains a first-class explicit pipeline stage for later wrapping. Missing: explicit structured i3rab output (token_id, governing_factor, i3rab_case_or_mood, etc.) as a first-class stage payload; current output is a string field. |

---

## Stage 12 — Semantic / rhetorical classification

| Status | Notes |
|--------|--------|
| **EXISTS** | `RhetoricSignalsExtractor` (engines/rhetoric) and `SentenceClassifier` (c2d) provide rhetoric signals and sentence type. Can be wrapped as stage 12. |

---

## Stage 13 — Validation / hypothesis pruning

| Status | Notes |
|--------|--------|
| **MISSING** | No single “pipeline consistency” validator. Local checks exist (CV validity, semantic gates, evaluator vs gold). Need a lightweight stage that consumes accumulated layer outputs and produces global_validity, final_confidence, issues list (e.g. missing prerequisite, wazn without root, i3rab without syntax). |

---

## Stage 14 — Presentation / rendering

| Status | Notes |
|--------|--------|
| **PARTIAL** | Output is currently inline in CLI: JSON dump, CSV write, _print_human_readable(). No separate presenter with multiple report modes (compact summary, layer-by-layer, debug). Recommendation: add presenters/renderers that take the pipeline object and produce these modes without adding analysis. |

---

## Summary table

| Stage | Name | Status |
|-------|------|--------|
| 0 | Input acquisition | PARTIAL |
| 1 | Normalization | PARTIAL |
| 2 | Tokenization | EXISTS |
| 3 | Segmentation | PARTIAL |
| 4 | Particles/operators/gating | EXISTS |
| 5 | Word typing/routing | EXISTS |
| 6 | Phonology/CV | EXISTS |
| 7 | Syllabification | EXISTS |
| 8 | Root extraction | EXISTS |
| 9 | Wazn matching | EXISTS |
| 10 | Syntax/sentence relations | EXISTS |
| 11 | i3rab | EXISTS |
| 12 | Semantic/rhetorical classification | EXISTS |
| 13 | Validation/hypothesis pruning | MISSING |
| 14 | Presentation/rendering | PARTIAL |

---

## Duplicated or overlapping logic (do not delete yet)

| Area | Duplication | Action |
|------|-------------|--------|
| Normalization | orthography_adapter, syllabifier.normalize_word, operators normalize_arabic, root_extractor normalize_hamza, cv_pattern normalize_word | Document; choose canonical normalizer for stage 1; adapters may call others where needed. |
| Wazn/pattern | root_resolver (wazn_matcher + wazn_adapter) vs pattern_matcher/pattern_analyzer | Document; orchestrator uses one path (e.g. WaznAdapter); optional mapping to Pattern for compatibility. |
| Tokenization | WordBoundaryDetector vs segmenter text.split() vs word-2-cv regex | Use WordBoundaryDetector for pipeline; others remain for scripts/specialized flows. |
| CV | cv_pattern (C2a path) vs phonology_v2 | Both kept; stage 6 selects one (e.g. via config/flag) or merges. |

---

## i3rab layer (explicit requirement)

| Aspect | Status |
|--------|--------|
| **Exists as code** | Yes — `i3rab_generator` + `enricher._build_i3rab()`; CLI attaches i3rab_text. |
| **Observed in live output** | i3rab payload appears under **`c2b.c2e.i3rab_text`** in morphology JSON (`--morphology --json`). |
| **Explicit stage** | Not yet — i3rab is produced inside enrichment; no separate “stage 11” in the architecture. Stage 11 remains the first-class explicit pipeline stage for later wrapping. |
| **Structured i3rab JSON** | Partial — current output is a string (i3rab_text). Minimum expected fields (token_id, surface, governing_factor, i3rab_position, i3rab_case_or_mood, i3rab_marker, estimated_reasoning, confidence, dependencies_used, status) can be added by the stage wrapper that calls existing code and fills a structured payload. |
| **Consumes prior stages** | Yes — enricher uses c2b features, verb/noun features, operator context. |

**Conclusion:** i3rab is **EXISTS** with **PARTIAL** structured output. Stage 11 will be an explicit layer that wraps current i3rab generation and emits both the existing text and a structured i3rab object.
