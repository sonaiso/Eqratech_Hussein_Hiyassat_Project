# Quran iʿrāb comparison pipeline

## Purpose

Compare `data/quran_i3rab.csv` (gold per word) to the orchestrator pipeline output for the same ayah, with **resumable** progress, **conservative** matching, and explicit **alignment** handling.

## Quran text source

Full ayah strings are loaded from `data/quran-uthmani.txt` (line format: `surah|ayah|text`). Override with `--quran-text`.

## Architecture

| Piece | Location |
| --- | --- |
| Ayah text index | `orchestrator/quran_gold/ayah_loader.py` |
| Gold/token alignment | `orchestrator/quran_gold/alignment.py` |
| L17/L11 extraction | `orchestrator/quran_gold/analyzer_extract.py` |
| Match levels + policy | `orchestrator/quran_gold/comparator.py` |
| Legacy row I/O helpers | `orchestrator/quran_gold/i3rab_compare_pipeline.py` |
| CLI | `scripts/run_quran_i3rab_comparison.py` |

## Alignment policy

Implemented in `orchestrator/quran_gold/alignment.py`:

- **Monotonic forward** greedy match: at each gold word, take the **first** pipeline token index `j ≥ cursor` that matches.
- **Surfaces**: NFC, ٱ→ا, tatweel removal, Quranic pause marks, **superscript alif (U+0670)** (Uthmani vs CSV), optional **ta marbuta → ha** at word end, then optional **consonant skeleton** (strip Arabic diacritics 064B–065F) as a last resort before declaring missing.
- **Prefixes**: one leading و / ف / ل / ب / ك may be stripped from **token** or **gold** (conservative).
- **Outcomes** per row: `aligned_unique`, `aligned_by_occurrence`, `alignment_ambiguous`, `alignment_missing_in_ayah`, `alignment_prefix_conflict`, `alignment_order_conflict`.
- **Confirmed wrong** (comparator mismatch) is recorded only when alignment is `aligned_unique` or `aligned_by_occurrence`.
- Rows that fail alignment are logged to `data/quran_i3rab_alignment_debug.csv` with `comparator_decision=skipped_alignment` and **do not** count toward `--max-wrong-rows`.

## Matching levels (conservative)

Defined in `comparator.MatchLevel`. Rows may be added to **`data/erqa_i3rab.csv` only** for levels **1–3** (`exact_text_match`, `normalized_text_match`, `structured_role_match`) when L17/L11 policy is satisfied.

- **L17** is preferred when `status == resolved` or `candidate` with `confidence >= 0.75`.
- **L11** `i3rab_text` is used for prose-level exact/normalized checks; if L11 matches but authoritative L17 **structurally conflicts**, the row is **rejected** for erqa (false positive avoidance).
- Levels **4–5** are diagnostic only (never alone justify erqa).

## Outputs

| File | Behavior |
| --- | --- |
| `data/erqa_i3rab.csv` | Cumulative **append**; dedupe by `(surah, ayah, ayah_word_index)` |
| `data/wrong_i3rab.csv` | **Overwrite** each run (confirmed mismatches only) |
| `data/quran_i3rab_progress.json` | Checkpoint / counters |
| `data/quran_i3rab_run_summary.json` | Last run summary |
| `data/quran_i3rab_alignment_debug.csv` | Ambiguous / missing alignment rows |

## Stop conditions

- **Success:** all gold rows have keys present in erqa (see `completed` in progress JSON).
- **Early:** confirmed `wrong` count in this run exceeds `--max-wrong-rows` (default **100**). Ambiguous rows do **not** count.
- **Writes refused** if `alignment_coverage < --alignment-min` (default **0.70**) unless `--force-below-alignment-threshold` is set. Coverage = `rows_aligned / rows_alignment_attempts` for the current run.

## Resume

- `--resume` reads `last_row_index` from `data/quran_i3rab_progress.json` and continues with the next gold row.
- Rows already in `erqa` are skipped via key load from `data/erqa_i3rab.csv`.

## Usage

```bash
# Mandatory first calibration (no CSV writes)
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py --limit 50 --dry-run

# Production batch (writes when alignment coverage ≥ 70%)
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py --max-wrong-rows 100 --resume
```

## Known limitations

- Gold orthography (i3rab CSV) may differ from Uthmani in `quran-uthmani.txt`; normalization mitigates but cannot fix all tokenizer/glyph splits.
- `structured_role_match` uses heuristic case buckets; borderline cases skew **false negative** by design.
