# Layer Mapping — Current Modules to Target Pipeline Stages

This document maps **existing** codebase modules to the **target** multi-layer transformation pipeline. No new analysis logic is proposed; only orchestration and wrapping.

---

## Target Pipeline Stages (Reference)

| Stage | Name |
|-------|------|
| 0 | Input acquisition |
| 1 | Normalization |
| 2 | Tokenization |
| 3 | Segmentation |
| 4 | Particles / operators / functional gating |
| 5 | Word typing / routing |
| 6 | Phonology / CV extraction |
| 7 | Syllabification |
| 8 | Root hypothesis extraction |
| 9 | Wazn matching |
| 10 | Syntax / sentence relations |
| 11 | i3rab |
| 12 | Semantic / rhetorical classification |
| 13 | Validation / hypothesis pruning |
| 14 | Presentation / rendering |

---

## Mapping Table

### Stage 0 — Input acquisition

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/cli/main.py` (MinimalCLI.run, process) | Parses CLI args, reads text or file, enforces length limits | 0 | Reusable with wrapper — entry builds request metadata |
| `fvafk/cli/main.py` (--input FILE) | Reads text from file; progress reporting | 0 | Reusable as-is |
| Scripts: `run_ayat_full_quran.py`, `run_full_quran_analysis.py` | Read Quran corpus (sura\|ayah\|text), iterate lines | 0 | Reusable with wrapper — different input format |

**Note:** No dedicated “input acquisition” module; logic lives inside CLI and scripts. Orchestrator can wrap CLI input handling or duplicate minimal file/string reading.

---

### Stage 1 — Normalization

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/orthography_adapter.py` | Orthography rules (ٱ→ا, ة→ت, ى→ي, همزة normalization), reversible encode/decode, optional strip diacritics | 1 | **Reusable as-is** — primary normalization entry |
| `fvafk/c2b/syllabifier.py` — `normalize_word()` | NFC, remove tatweel, U+0670→ا | 1 | Reusable with wrapper — used by syllabifier |
| `fvafk/c2b/operators_particles_db.py` — `normalize_arabic()` | Unicode NFC only | 1 | Partial — lightweight, used in several places |
| `fvafk/c2b/root_extractor.py` — `normalize_hamza_for_roots()` | Hamza normalization for root extraction (أ/إ/آ→ا, ؤ→ا, ئ→ي), NFD strip combining | 1 | Reusable with wrapper — domain-specific |
| `fvafk/c1/cv_pattern.py` — `normalize_word()` | Used in CV analysis path | 1 | Partial — may duplicate logic; prefer OrthographyAdapter or single canonical normalizer |
| `fvafk/c2b/operators_catalog.py` — `_strip_diacritics()` | Strip combining marks for operator matching | 1 | Partial — internal to catalog; not a global stage |

**Duplication note:** Several `normalize_*` / `_strip_diacritics` implementations exist (orthography_adapter, syllabifier, operators_catalog, root_extractor, cv_pattern, word-2-cv). Documented; do not delete until pipeline uses one canonical normalizer and adapters.

---

### Stage 2 — Tokenization

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/word_boundary.py` — `WordBoundaryDetector` | Regex over Arabic run; returns `TokenSpan`; `detect()`, `iter_tokens()` | 2 | **Reusable as-is** — main tokenizer |
| `fvafk/c2b/word_boundary_detector.py` | Plan B detector (from segments/syllables); not fully used | 2 | Partial / placeholder |
| `segmenter.py` — `segment_text()` | `text.split()` for words then per-word segment_word | 2 | Reusable with wrapper — simple space split; MASAQ segmenter is heavy |
| `word-2-cv.py` — `ARABIC_TOKEN_RE` | Regex `[\u0600-\u06FF]+` for unique word extraction | 2 | Reusable with wrapper — script-level |

**Note:** Main pipeline path uses `WordBoundaryDetector` (e.g. in CLI). Segmenter uses `text.split()`. Orchestrator should standardize on one tokenization contract (e.g. list of tokens + spans).

---

### Stage 3 — Segmentation

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `segmenter.py` — `ArabicSegmenter.segment_word()` | Per-word morphological segments (prefix/stem/suffix), MASAQ-style tags | 3 | Reusable with wrapper — heavy; output shape differs from fvafk |
| `fvafk/c2a` gates + `GateOrchestrator` | Segment stream into “units” (letter/diacritic), apply phonological gates | 3 | Reusable with wrapper — segment = list of units after gates |
| `fvafk/c2a/syllable.py` — `Segment`, SegmentKind | Segment kinds (LETTER, VOWEL, etc.) used in C2a | 3 | Reusable — part of C2a output |
| `fvafk/c2b/root_extractor.py` — `extract_with_affixes()` | Prefix/stem/suffix for root extraction (not full MASAQ segments) | 3 | Partial — affix-level segmentation for morphology |

**Note:** Two notions of “segmentation”: (1) MASAQ full morph segments, (2) fvafk C2a unit stream + C2b affix split. Pipeline stage 3 can wrap either or both; document which output is “segment” for downstream.

---

### Stage 4 — Particles / operators / functional gating

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/operators_catalog.py` — `OperatorsCatalog` | Load operators from CSV; classify(token) → operator metadata; direct/peel/compound match | 4 | **Reusable as-is** — primary operator gate |
| `fvafk/c2b/operators_particles_db.py` — `SpecialWordsDatabase` | Load particles/special words; tag types | 4 | Reusable with wrapper — overlaps with operators_catalog; used by special_words_catalog |
| `fvafk/c2b/special_words_catalog.py` — `SpecialWordsCatalog` | classify(token) → demonstrative, excluded_name, particle/special | 4 | **Reusable as-is** — used with OperatorsCatalog in WordClassifier |
| `fvafk/particle_loader.py` | Load particles from CSV; ParticleCategory; Node schema integration | 4 | Reusable with wrapper — different schema; can feed catalog or gate |
| `fvafk/c1/cv_pattern.py` — `should_exclude()` | Exclude list for CV (e.g. particles/pronouns) | 4 | Partial — gating for CV only |

**Note:** Operators and “special” words (demonstratives, names, particles) are used early in CLI to skip root extraction and set kind. Orchestrator stage 4 should call OperatorsCatalog + SpecialWordsCatalog and emit standardized “functional gate” result.

---

### Stage 5 — Word typing / routing

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/word_classifier.py` — `WordClassifier` | classify(token) → kind (operator, particle, pronoun, verb, noun, demonstrative, name, unknown); uses operators, special, prep+clitic, detached pronouns, verb heuristics | 5 | **Reusable as-is** — main word typing |
| `fvafk/c2b/mabni_rules.py` — `classify_mabni()` | Mabni detection (fixed list + patterns) | 5 | Reusable with wrapper — used before/alongside WordClassifier |
| `fvafk/c2b/word_form.py` — `PartOfSpeech` | Enum for POS | 5 | Reusable — schema only |
| `fvafk/c2b/pattern_analyzer.py` | Pattern type from pattern DB | 5 | Reusable with wrapper — feeds “type” for verb/noun |

**Note:** Word “routing” (operator vs content word, verb vs noun) is already implemented in WordClassifier + mabni + pattern_analyzer. Stage 5 wraps these and outputs a single “word_type” / “kind” for each token.

---

### Stage 6 — Phonology / CV extraction

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c1/cv_pattern.py` | `cv_pattern()`, `analyze_text_for_cv()`, `analyze_text_for_cv_after_phonology()`; C/V sequence; exclude list | 6 | **Reusable as-is** — main CV logic |
| `fvafk/c1/cv_pattern.py` — `analyze_text_for_cv_after_phonology()` | C2a gate pipeline then CV per token | 6 | Reusable — combines C2a + CV |
| `fvafk/phonology_v2/phonology_adapter.py` | Phonology V2: graphemes → segments → CV/cv_advanced | 6 | **Reusable with wrapper** — alternate engine; used when --phonology-v2 |
| `fvafk/phonology_v2/phonology_utils.py` — `text_to_graphemes()`, `segments_to_cv()` | Grapheme list; segment-to-CV | 6 | Reusable — used by phonology_adapter |
| `fvafk/c1/` — C1Encoder, units | Encode text to units (letter/diacritic) | 6 | Reusable — input to C2a and CV path |
| `word-2-cv.py` | Standalone CV from text (regex tokenize + normalize + CV) | 6 | Reusable with wrapper — script; duplicate of fvafk path |

**Note:** Two engines: “c2a” (gate-based) and “phonology_v2”. Both produce CV (and optionally cv_advanced). Stage 6 should accept normalized/tokenized input and call one engine (or both and merge); output = CV (+ cv_advanced) per token.

---

### Stage 7 — Syllabification

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/syllabifier.py` — `ArabicSyllabifier` | syllabify(word) → SyllabificationResult (syllables, cv_pattern, valid, error); uses normalize, word_to_cv_pattern, validate_cv_law, segment_cv_strict | 7 | **Reusable as-is** — single source of truth for syllabification |
| `fvafk/c2a/syllable.py` | Segment kinds; syllable-related types | 7 | Reusable — types used in C2a |
| `fvafk/c2a/gate_framework.py` — GateOrchestrator | Runs gates on unit stream; output can be interpreted as segment stream | 7 | Partial — upstream of syllabification in some flows |

**Note:** Syllabification in this codebase is word-level (ArabicSyllabifier). C2a does not produce syllable boundaries in the same way. Stage 7 = syllabifier per token; input = normalized word (and optionally CV from stage 6).

---

### Stage 8 — Root hypothesis extraction

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/root_extractor.py` — `RootExtractor` | extract_with_affixes(word) → RootExtractionResult (root, normalized_word, stripped_word, prefix, suffix) | 8 | **Reusable as-is** — primary root hypothesis |
| `fvafk/c2b/root_resolver/resolver.py` — `RootResolver` | resolve(word, stripped, cli_root, kind) → ResolverResult (root, source, confidence); tries special_jalala, CLI, wazn, heuristic | 8 | **Reusable as-is** — combines CLI root + wazn + heuristic |
| `fvafk/c2b/root_resolver/heuristic_version.py` — `heuristic_root()` | Fallback root from word/stripped when no wazn/CLI | 8 | Reusable — used by RootResolver |
| `fvafk/c2b/root_resolver/roots_db.py` — `RootsDB` | Load roots CSV; is_rootlike, normalize, canonicalize | 8 | Reusable — data layer for resolver |
| `fvafk/c2b/pattern_analyzer.py` | Uses RootExtractor; builds pattern + root for single word | 8 | Reusable with wrapper — orchestration over extractor |

**Note:** Root “extraction” (affixes + candidate root) and root “resolution” (pick among CLI/wazn/heuristic) are both needed. Stage 8 can wrap RootExtractor + RootResolver and emit root + source + confidence.

---

### Stage 9 — Wazn matching

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/root_resolver/wazn_matcher.py` | try_match_pattern_to_word(pattern, word); best_hit(); load_patterns(); FULLMATCH/WINDOW; ف/ع/ل placeholders | 9 | **Reusable as-is** — core wazn logic |
| `fvafk/c2b/root_resolver/wazn_adapter.py` — `WaznAdapter` | Load patterns from CSV; resolve(word, stripped) → WaznResult (pattern, root, match_type); get_pattern_for_word_root() | 9 | **Reusable as-is** — used by RootResolver |
| `fvafk/c2b/pattern_matcher.py` — `PatternMatcher` | Match word to pattern DB (awzan); returns Pattern with template, type, stem, etc. | 9 | Reusable with wrapper — different API; may duplicate wazn_matcher role |
| `fvafk/c2b/pattern_analyzer.py` | Uses PatternMatcher / pattern DB; returns pattern for word | 9 | Reusable with wrapper — combines root + pattern |

**Duplication note:** Wazn matching exists in root_resolver (wazn_matcher + wazn_adapter) and in pattern_matcher/pattern_analyzer. Both use pattern CSV. Document; orchestrator can standardize on one (e.g. WaznAdapter) and optionally map to Pattern shape.

---

### Stage 10 — Syntax / sentence relations

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/syntax/linkers/isnadi_linker.py` — `IsnadiLinker`, `find_isnadi_links()` | Find مبتدأ/خبر links (mubtada/khabar) over tokens | 10 | **Reusable with wrapper** — main syntax linker in fvafk |
| `fvafk/syntax/linkers/link.py` — `Link`, `LinkType` | Link type and structure | 10 | Reusable — schema |
| `fvafk/c2b/syntax/morph_syntax_bridge.py` — `MorphSyntaxBridge` | infer_i3rab_type(morph, context, position) → (i3rab_type_en, confidence) | 10 | Reusable with wrapper — syntax–morph bridge |
| `fvafk/c2b/syntax/syntax_features.py` | Syntax features from morphology | 10 | Reusable — features |
| `fvafk/c2d/sentence_classifier.py` — `SentenceClassifier` | classify(tokens) → SentenceType (خبرية, أمر, نهي, استفهام, نداء, تمني, قسم, شرط, توكيد, ترجي, …) + trigger word | 10 | **Reusable as-is** — sentence-level type |
| `engines/syntax/*` (mobtada_khabar, fael_engine, etc.) | Various syntactic relation engines | 10 | Reusable with wrapper — richer syntax; may not be wired in main CLI |

**Note:** Main pipeline uses IsnadiLinker and SentenceClassifier. Stage 10 wraps these and emits sentence_type + links. Mapped to real code. **L10 runs successfully** in tested paths. The prior runtime issue was a **minimal compatibility fix**: the CLI expected `from_multi_word_item` and `_word_form_to_syntax_dict`, which were missing; the failure was not due to the syntax engine itself. `from_multi_word_item(...)` now forwards to `from_c2b(...)`; `_word_form_to_syntax_dict(...)` was added only to expose syntax output in the CLI/orchestrator path. No analyzer logic was rewritten.

---

### Stage 11 — i3rab

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2e/i3rab_generator.py` — `generate_i3rab(WordInfo)` | Build full i3rab text from WordInfo (word_type, function, case, number, gender, …) | 11 | **Reusable as-is** — core i3rab text generation |
| `fvafk/c2e/enricher.py` — `_build_i3rab()` | Map c2e features + c2b to WordInfo; call generate_i3rab; handle verb/noun/particle; preposition prefix | 11 | **Reusable as-is** — integration with c2b/c2e |
| `fvafk/c2e/enricher.py` — `MorphEnricher.enrich()` | Enrich word with verb/noun features and i3rab_text | 11 | Reusable — calls _build_i3rab |
| `fvafk/c2b/syntax/i3rab_components.py` | i3rab-related components | 11 | Reusable — support |
| `fvafk/c2b/syntax/i3rab_parser.py` — `I3rabParser` | Parse i3rab from external source (e.g. gold) | 11 | Reusable with wrapper — input side, not generation |
| `fvafk/c2b/evaluation/i3rab_loader.py` | Load gold i3rab for evaluation | 11 | Reusable — evaluation only |

**Note:** i3rab **generation** is in c2e (i3rab_generator + enricher). CLI already calls enricher and attaches i3rab_text per word. **Currently observed payload location in live output:** **`c2b.c2e.i3rab_text`** (per-word i3rab string in morphology JSON). Stage 11 = explicit i3rab layer consuming prior stages and emitting structured i3rab (token_id, surface, case/mood, marker, reasoning, confidence, dependencies_used, status).

---

### Stage 12 — Semantic / rhetorical classification

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `engines/rhetoric/extractor.py` — `RhetoricSignalsExtractor` | extract(tokens, sentence_type, word_analyses, trigger_word) → List[RhetoricSignal] (interrogative, vocative, oath, emphasis, etc.) | 12 | **Reusable as-is** — rhetoric signals |
| `engines/rhetoric/types.py` — `RhetoricSignal` | type, label_ar, trigger, span, confidence, evidence | 12 | Reusable — schema |
| `fvafk/c2d/sentence_classifier.py` | Sentence type (including توكيد, ترجي, قسم, استفهام, نداء, …) | 12 | Reusable — overlaps with rhetoric; sentence-level |
| `fvafk/c2c/` (semantic_gates, assurance, evidence) | Semantic gates; evidence | 12 | Reusable with wrapper — different focus (semantic validation) |

**Note:** Rhetoric extractor consumes sentence_type and word_analyses (c2b). Stage 12 wraps rhetoric extractor (and optionally c2c) and emits semantic/rhetorical labels per sentence or span.

---

### Stage 13 — Validation / hypothesis pruning

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/c2b/root_resolver/evaluator.py` | evaluate(pred_rows, gold_rows) → accuracy, per-source stats | 13 | Reusable with wrapper — evaluation vs gold; not inline validation |
| `fvafk/c2c/semantic_gates.py` — `RootGate`, etc. | Semantic gates (e.g. root present) | 13 | Reusable with wrapper — gate-based validation |
| `fvafk/c2c/assurance.py`, `evidence.py` | Assurance and evidence types | 13 | Reusable — support |
| `fvafk/c2b/syllabifier.py` — `validate_cv_law()` | CV validity check | 13 | Reusable — local to syllabification |
| No dedicated “pipeline consistency” validator | — | 13 | **Missing** — to be added as lightweight stage that checks cross-stage consistency (e.g. wazn without root, i3rab without syntax, missing prerequisites) |

**Note:** Current code has local validation (CV law, semantic gates, evaluator vs gold) but no single “pipeline validation” stage. Stage 13 = new lightweight orchestrator component that runs consistency checks on accumulated outputs and emits global_validity, final_confidence, issues list.

---

### Stage 14 — Presentation / rendering

| Current module/file | Current responsibility | Target layer | Reuse status |
|---------------------|------------------------|--------------|--------------|
| `fvafk/cli/main.py` — `_print_human_readable()` | Print human-readable summary of result dict | 14 | Reusable with wrapper — current “presentation” |
| `fvafk/cli/main.py` — `_morphology_to_csv_rows()`, CSV write | Build CSV rows from result; write to file; --output-csv, --arabic-tags | 14 | Reusable with wrapper — CSV presentation |
| `fvafk/cli/main.py` — JSON output | result dict serialized to JSON (--json) | 14 | Reusable — JSON is the pipeline object; “presentation” can be a separate renderer that formats it |
| No dedicated “layer-by-layer report” or “debug report” | — | 14 | **Partial** — CLI prints mixed view; no explicit compact summary / detailed layer report / debug report modes |

**Note:** Presentation is currently inline in CLI (print, CSV, JSON). Stage 14 = separate presenter/renderer that takes the cumulative pipeline object and produces (1) compact summary, (2) detailed layer-by-layer report, (3) developer/debug report, and (4) i3rab section when present. No new analysis; only formatting of existing JSON.

---

## Summary

- **Stages with existing “as-is” reusable modules:** 1 (normalization — OrthographyAdapter), 2 (WordBoundaryDetector), 4 (OperatorsCatalog, SpecialWordsCatalog), 5 (WordClassifier, mabni), 6 (cv_pattern, phonology_v2), 7 (ArabicSyllabifier), 8 (RootExtractor, RootResolver), 9 (wazn_matcher, WaznAdapter), 10 (IsnadiLinker, SentenceClassifier), 11 (i3rab_generator, enricher), 12 (RhetoricSignalsExtractor).
- **Stages needing only wrappers/adapters:** 0 (input in CLI), 3 (segmenter or C2a units), 13 (lightweight validator to be added), 14 (presentation to be split out).
- **Duplication noted:** multiple normalizers; two wazn/pattern paths (root_resolver vs pattern_matcher). Do not remove until pipeline standardizes and adapters are in place.
