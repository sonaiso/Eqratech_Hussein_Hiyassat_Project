# Current Entry Points and Outputs

This document lists the main entry points into the linguistic pipeline and the outputs they produce. Used for orchestration design: the orchestrator will either wrap these or replace them with a single entry that runs stages in order.

---

## 1. Main CLI (Primary entry)

| Item | Location | Description |
|------|----------|-------------|
| Module | `src/fvafk/cli/main.py` | MinimalCLI |
| Invocation | `python3 -m fvafk.cli [OPTIONS] [TEXT]` or `--input FILE` |
| Entry | `__main__.py` → `MinimalCLI().run()` → `process()` or `_analyze_morphology_multi_word()` |

**Shell note:** In the verified macOS shell environment, the main CLI entrypoint works with `python3`, not `python`. Other environments may differ; use `python3 -m fvafk.cli` for consistency where applicable.

**Arguments (relevant):**
- Positional text or `--input FILE`
- `--json` — output full result as JSON (see Base vs Morphology JSON below)
- `--morphology` — run morphology (c2b + c2e); use with `--json` for morphology JSON flow
- `--multi-word` — run multi-word analysis (tokenize → per-word morphology + c2d + rhetoric)
- `--output-csv PATH` — write CSV (similar to out_with_sources)
- `--arabic-tags` — translate tag values to Arabic in CSV
- `--phonology-v2` — use phonology_v2 engine for CV
- `--limit-lines N` — when reading file, limit lines
- `--verbose` — include units, gate details

**Base JSON flow (`--json` without `--morphology`):**
- Output contains: `input`, `success` (true), `c1`, `c2a`, `stats`.
- No `c2b` (morphology not run).

**Morphology JSON flow (`--morphology --json`):**
- Output contains: `c1`, `c2a`, `c2b`, `syntax`, `c2d`, `rhetoric_signals`.
- i3rab-related output exists under **`c2b.c2e.i3rab_text`** (per-word i3rab string when enrichment runs).

**Flow (simplified):**
1. Parse args; read text (string or from file).
2. Optional: C1 encode (units); C2a gate orchestrator (phonology gates).
3. If morphology: tokenize via WordBoundaryDetector (multi-word) or single word; for each token: mabni check → operator/special/pronoun check → jalala check → RootExtractor + RootResolver (with WaznAdapter) + PatternAnalyzer → WordClassifier → features → c2e MorphEnricher (verb/noun analysis + i3rab).
4. If multi-word: c2d SentenceClassifier; rhetoric RhetoricSignalsExtractor.
5. Build result dict (c1, c2a, c2b.words, c2d, rhetoric_signals, etc.).
6. Output: JSON (print) or CSV (file) or human-readable print.

**Outputs:**
- **JSON:** `result` dict with keys: success, c1, c2a, c2b (words, each with word, kind, root, pattern, features, operator, c2e with i3rab_text, …), c2d (sentence_type, trigger_word), rhetoric_signals, optional error.
- **CSV:** Rows with word, root, kind, type, category, cv, cv_advanced, features (case, number, gender, …), i3rab, root_source, operator_effect, isnadi_role, etc.
- **Human-readable:** Printed summary (no standard schema).

---

## 2. Scripts (Batch / evaluation entry points)

| Script | Purpose | Input | Output |
|--------|---------|--------|--------|
| `scripts/run_ayat_full_quran.py` | Run pipeline on Quran corpus (sura\|ayah\|text per line) | `--roots`, `--output` CSV, optional limit | CSV: sura, ayah, word, root, kind, … |
| `scripts/run_full_quran_analysis.py` | Full Quran analysis | Similar | CSV / analysis output |
| `scripts/run_complete_snapshot.py` | Snapshot of pipeline on sample | Config / input file | Snapshot CSV or JSON |
| `scripts/eval_mishkat.py` | Evaluate root output vs Mishkat gold | `--pipeline-output` CSV, `--gold` CSV | Accuracy, per-source stats |
| `scripts/export_no_cv_no_wazn.py` | Analyze missing CV/wazn from pipeline CSV | Reads CSV (e.g. out.csv) | no_cv.csv, no_wazn.csv |
| `scripts/analyze_no_root_words.py` | Analyze words with no root in i3rab CSV | i3rab_out.csv | unique_words_no_root_expected.csv, unique_words_no_root_unexpected.csv |
| `scripts/run_ayat_al_dayn_snapshot.py` | Snapshot on specific verse(s) | Verse text / file | Snapshot output |

**Note:** These scripts typically construct a pipeline in code (import MinimalCLI or direct imports of RootExtractor, RootResolver, etc.) and write CSV/JSON. They are secondary entry points; the canonical user entry is the CLI.

---

## 3. Standalone modules (callable but not CLI)

| Module | Entry | Typical use |
|--------|--------|--------------|
| `fvafk.c2b.syllabifier` | `ArabicSyllabifier().syllabify(word)` | Tests; could be called from pipeline stage 7 |
| `fvafk.c2b.root_resolver.wazn_matcher` | `try_match_pattern_to_word()`, `best_hit()`, `load_patterns()` | Used by WaznAdapter; can be run as CLI for evaluation |
| `fvafk.c2b.root_resolver.evaluator` | `evaluate(pred_rows, gold_rows)` | Evaluation script |
| `fvafk.c2e.i3rab_generator` | `generate_i3rab(WordInfo)` | Used by enricher; has `__main__` for ad-hoc tests |
| `segmenter.py` | `ArabicSegmenter().segment_text(text)` | MASAQ segmentation; separate from fvafk CLI |
| `word-2-cv.py` | Script: unique words + CV from file | Standalone CV extraction |
| `fvafk.particle_loader` | Load particles; `__main__` | Data loading / one-off |
| `fvafk.c2b.operators_particles_db` | SpecialWordsDatabase; `__main__` | Data loading / one-off |

---

## 4. Existing JSON and CSV outputs (reusable)

| Output | Producer | Shape / location |
|--------|----------|-------------------|
| CLI `--json` | MinimalCLI.run() | Single JSON object: success, c1, c2a, c2b, c2d, rhetoric_signals, (error) |
| CSV from `--output-csv` | MinimalCLI._morphology_to_csv_rows() | Rows: word, root, kind, type, cv, cv_advanced, case, number, gender, i3rab, root_source, operator_effect, isnadi_*, … |
| out_with_sources.csv | run_ayat_full_quran.py (or similar) | Same kind of columns; used for evaluation |
| i3rab_out.csv | CLI with --output-csv i3rab/i3rab_out.csv | Same CSV format with i3rab column |
| Golden / evaluation | eval_mishkat.py, scripts | Gold CSV (word, root); pipeline CSV with root_source |

**Design note:** The pipeline orchestrator should accumulate a single “pipeline object” (JSON) that can be serialized as-is and fed to a separate presenter for JSON/CSV/human reports. Current CLI already builds a result dict; that dict is the natural “pipeline object” once we attach per-stage outputs (layer_outputs).

---

## 5. Data files used at runtime

| Data | Used by |
|------|--------|
| `data/operators_catalog_split_project_enriched.csv` | OperatorsCatalog |
| `data/awzan_merged_final.csv` | WaznAdapter, pattern loader |
| `data/merged_roots.csv` (or project roots CSV) | RootsDB, RootResolver |
| `data/mabniyat_display_roots.csv`, special/lexicon CSVs | SpecialWordsCatalog, mabni, etc. |
| `data/quran-simple-clean.txt`, `data/quran-uthmani.txt` | Scripts (input corpus) |

Entry points do not define a single “config” for data paths; they use defaults or script args. Orchestrator may introduce a small config or env for data paths.

---

## 6. Stage 1 live verification (documentation)

Live verification confirmed that the main CLI entrypoint works via `python3 -m fvafk.cli` in the current macOS shell environment.

- **Help command verified:** `python3 -m fvafk.cli --help` runs successfully.
- **Base JSON verified:** `python3 -m fvafk.cli "إِنَّ اللَّهَ غَفُورٌ" --json` produces output with input, `success: true`, c1, c2a, stats; no c2b when morphology is not enabled.
- **Morphology JSON verified:** `python3 -m fvafk.cli "كَاتِبٌ" --morphology --json` produces output with c1, c2a, c2b, syntax, c2d, rhetoric_signals; i3rab-related output exists under `c2b.c2e.i3rab_text`.
- **Syntax (L10):** The syntax stage is present and reachable. L10 now runs successfully in tested paths. The prior failure was caused by **missing integration helpers**, not by a confirmed failure of the syntax engine itself. A **minimal compatibility fix** was applied: `WordFormBuilder.from_multi_word_item(...)` was added and forwards to `from_c2b(...)`; `_word_form_to_syntax_dict(...)` was added in the CLI only to expose syntax output in the CLI/orchestrator path. No syntax analysis logic was redesigned or replaced.
- **i3rab observed:** i3rab-related payload is present in live output under `c2b.c2e.i3rab_text`; Stage 11 i3rab remains a first-class explicit pipeline stage for later wrapping.
