# Quran iʿrāb comparison pipeline (Batch 28.3–28.15)

## Purpose

Compare `data/quran_i3rab.csv` (gold per word) to the orchestrator pipeline output for the same ayah, with **ayah-bounded** execution, **strict** comparator tiers, **quarantine** outputs, and **resumable** progress. **Batch 28.4** adds a **conservative gold prose parser** and compares **structured grammatical facts** (gold vs L17) instead of long prose-vs-prose similarity. **Batch 28.5** adds **truth-source auditing** (row/ayah CSVs), **safe normalization** for exact L11 vs gold, **L11↔gold structured strict** agreement using the same parser on both sides, and narrow role bridges (e.g. `ism_majrur`, `naat`↔`ism_majrur` when both genitive) documented in `truth_audit.py`. **Batch 28.8** adds **discovery-ranked, surgical L17 resolutions** (fused حرف جر surfaces, و/ف عطف, اسم موصول) to raise **strict_structural_match** counts **without** changing comparator acceptance policy; see `orchestrator/l17_rule_based_i3rab.py` (`Batch 28.8` comments), `tests/quran_gold/test_batch_28_8_l17.py`, and `data/quran_i3rab_batch_28_8_pattern_ranking.json`. **Batch 28.9** adds **ayah-level unlock diagnostics** (`NEAR_PASS_1` / `NEAR_PASS_2` / `CORE_BLOCKED` / …), per-ayah blocker CSVs, unlock preview, best write candidates, and `batch_28_9` fields in the run summary JSON — **reporting only**; does not relax PASS_STRICT or comparator rules (`orchestrator/quran_gold/ayah_unlock_ranker.py`, `tests/quran_gold/test_batch_28_9_ayah_unlock.py`). **Batch 28.10** adds a **second surgical L17 pass** (`_apply_b28_10_targeted_resolutions`) for **fused لِل…** (single-surface حرف جر) and **واو+الموصول** surfaces (`والذ*` / `والتي*`) missed by Batch 28.8’s `الذ`-initial mawsul rule; `gold_rule_refs` `B28_10_LAM_AL_FUSED` / `B28_10_WAW_AL_MAWSUL`; reporting in `orchestrator/quran_gold/batch_28_10_reporting.py`, `batch_28_10` summary keys, and `data/quran_i3rab_batch_28_10_*.csv|json`; tests `tests/quran_gold/test_batch_28_10_l17.py`. Comparator acceptance unchanged.

**Batch 28.11** targets **ayah-level completion**: Stage15 **IDAFA** is prioritized over **PRED** in `_stage15_relation_and_head`, L17 resolves **مضاف إليه** for IDAFA dependents (`B28_11_IDAFA_MUDAF_ILAYH`), plus a narrow **بِسْمِ + اللَّهِ** surface fallback (`B28_11_BISMILLAH_MUDAF_ILAYH`) when the construct appears without an IDAFA link — unlocking **1:1** as an additional **PASS_STRICT** ayah in gold_csv runs. Diagnostics: `ayah_completion_ranker`, `data/quran_i3rab_batch_28_11_*.csv`, summary key `batch_28_11`; tests `tests/quran_gold/test_batch_28_11_l17.py`.

**Batch 28.12** hardens **accepted-row serialization** for `erqa_i3rab.csv`: `system_i3rab` must match the **accepted comparator basis** (e.g. strict L17 **مضاف إليه** must not store stale L11 «خبر مرفوع» prose). Implementation: `orchestrator/quran_gold/accepted_row_serializer.py` (`build_accepted_erqa_row`, `render_structured_i3rab_ar`, `raw_system_i3rab_before_hardening`); `ayah_batch_runner` builds extended erqa dicts; tests `tests/quran_gold/test_batch_28_12_serialization.py`. Comparator acceptance logic is unchanged.

**Batch 28.13** refines **modifier-aware** accepted display: for `strict_structural_match` rows where gold resolves **نعت** (including **ثانٍ** / **ثالثٌ** from gold prose), `system_i3rab` is built from **gold-structured** templates instead of generic L11 «اسم مجرور»; `normalize_accepted_structured_metadata` keeps `accepted_role`, `accepted_structured_signature`, and `system_i3rab` consistent (e.g. drops spurious `mudaf_ilaih` in signature when the authoritative role is `naat`). Tests: `tests/quran_gold/test_batch_28_13_modifier_serialization.py`. Comparator acceptance unchanged.

**Batch 28.14** — L17 only: **مبتدأ** for sentence-initial tokens that Stage15 marks as **head** of `PRED` + `KHABAR` (`nominal_mubtada_to_khabar`), fixing unresolved L17 on e.g. Fatiha **1:2** `الْحَمْدُ` so gold `mubtada` ↔ L17 strict agreement (`_apply_b28_14_mubtada_pred_head`, `gold_rule_refs` `B28_14_MUBTADA_PRED_HEAD`). Scope: `head_id == 0` only. Tests: `tests/quran_gold/test_batch_28_14_alhamdu.py`. Comparator unchanged.

**Batch 28.15** — **Accepted-row metadata only** (no comparator/orchestrator/stage-order change): for each row appended to `erqa_i3rab.csv`, authoritative columns `accepted_role`, `accepted_case_bucket`, `accepted_marker`, `accepted_structured_signature`, `accepted_governing_factor`, and `system_i3rab` are derived from the **final accepted role + canonical display line** via `canonicalize_accepted_metadata` in `orchestrator/quran_gold/accepted_row_serializer.py`. Legacy multi-code signatures (e.g. `ism_majrur,mubtada`) and stale L17 case/marker traces no longer leak into accepted fields; `raw_system_i3rab_before_hardening` keeps pre-canonical analyzer text. Invariants helper: `validate_accepted_row_invariants`. Tests: `tests/quran_gold/test_batch_28_15_metadata_canonicalization.py` (unit + optional `@pytest.mark.slow` CLI subprocess checks for 1:1–1:3 writes).

## Partition A — ERQA integrity (`--verify-erqa`)

**Do not** approximate “finished work” with a contiguous Quran prefix (e.g. `--from-surah 1 --from-ayah 1 --max-ayahs 140`): accepted ayahs in `erqa_i3rab.csv` are **not** guaranteed to be the first *N* ayahs of the mushaf.

**Mandatory gate (before upstream patch work that could regress accepted rows):**

```bash
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py --verify-erqa data/erqa_i3rab.csv
```

**Patch 19:** `--verify-erqa` **always** builds ayah text from **gold CSV** (`gold_csv` reconstruction). You do not need `--canonical-ayah-source gold_csv` for Partition A; the JSON report’s `canonical_ayah_source` field is **`gold_csv`** for this subcommand.

**Behavior:**

1. Read **all** data rows from the given ERQA CSV.
2. Collect the **exact** finished ayah set `{(surah, ayah)}` implied by those rows (plus `(surah, ayah, ayah_word_index)` keys; duplicate keys are a data defect).
3. Re-run **only** those ayahs through `run_pipeline` + gold alignment + comparator (with **no** “already in ERQA” short-circuit — every accepted key is re-checked).
4. Print JSON: `total_finished_rows`, `total_finished_ayahs`, `duplicate_key_rows`, `corrupted_rows`, `corrupted_ayahs`, `status` (`PASS` / `FAIL`), `failure_sample`, `failure_count`.
5. Exit code **1** if `status` is `FAIL` (any degradation, duplicate key rows, missing gold row, alignment failure, or loss of `strict_acceptance_eligible` after `--max-repair-attempts`).

Implementation: `orchestrator/quran_gold/ayah_batch_runner.py` (`verify_erqa_integrity`, `ErqaIntegrityReport`), CLI `scripts/run_quran_i3rab_comparison.py` (`_run_verify_erqa`). Tests: `tests/quran_gold/test_verify_erqa_integrity.py`.

**Batch summary (normal runs):** `batch_summary.json` / printed JSON include **`newly_added_rows_this_patch`** and **`newly_added_ayahs_this_patch`** (same counters as new ERQA payloads queued this run — use in patch reports).

## Quran text source

**Default (unchanged):** full ayah strings are loaded from `data/quran-uthmani.txt` (line format: `surah|ayah|text`). Override with `--quran-text`.

**Batch 28.7 — gold-CSV-only mode:** set `--canonical-ayah-source gold_csv`, or use `--discovery-only` / `--emit-discovery-csvs`. The runner builds the ayah string by joining `word` fields from `data/quran_i3rab.csv` in CSV row order for each `(surah, ayah)` — **no** `quran-uthmani.txt` read on that path. Use this for discovery expansion and reporting when the gold file must be the single canonical surface source.

## Architecture

| Piece | Location |
| --- | --- |
| Ayah text index | `orchestrator/quran_gold/ayah_loader.py` |
| Canonical ayah from gold CSV (28.7) | `orchestrator/quran_gold/gold_csv_ayah.py` |
| Discovery buckets / trapped rows / ranked unlockable (28.7) | `orchestrator/quran_gold/discovery_reporting.py` |
| Ayah unlock / near-pass / write candidates (28.9) | `orchestrator/quran_gold/ayah_unlock_ranker.py` |
| Batch 28.10 metrics / promoted & blocked CSVs | `orchestrator/quran_gold/batch_28_10_reporting.py` |
| Batch 28.11 ayah completion ranking / targets | `orchestrator/quran_gold/ayah_completion_ranker.py`, `batch_28_11_reporting.py` |
| Gold/token alignment | `orchestrator/quran_gold/alignment.py` |
| Gold prose → structured facts | `orchestrator/quran_gold/gold_prose_parser.py`, `gold_structured.py` |
| L17/L11 extraction | `orchestrator/quran_gold/analyzer_extract.py` |
| Comparator tiers | `orchestrator/quran_gold/comparator.py` (`ComparatorTier`, `strict_acceptance_eligible`, `normalize_i3rab_for_exact_compare`, `structured_strict_gold_vs_l11_prose`) |
| Truth-source audit (28.5) | `orchestrator/quran_gold/truth_audit.py` |
| PASS_STRICT discovery / isolated writes (28.6) | `orchestrator/quran_gold/pass_strict_batch.py` |
| Ayah evaluation | `orchestrator/quran_gold/ayah_batch_runner.py` |
| Quarantine I/O helpers | `orchestrator/quran_gold/batch_quarantine.py` |
| Legacy row I/O helpers | `orchestrator/quran_gold/i3rab_compare_pipeline.py` |
| CLI | `scripts/run_quran_i3rab_comparison.py` |

## Comparator tiers (strict acceptance)

The comparator assigns each aligned word one of:

| Tier | Meaning | Appended to `erqa_i3rab.csv`? |
| --- | --- | --- |
| `exact_text_match` | L11 text matches gold (NFC and/or safe orthographic normalization). | **Yes** (if ayah `PASS_STRICT` and `--write-mode`) |
| `strict_structural_match` | Structured agreement: (a) authoritative L17 vs parsed gold; (b) **or** parsed gold vs parsed **L11** (`L11_structured` / `strict_structured_gold_vs_l11_prose`); (c) legacy prose heuristic only as a narrow fallback when structured parse misses. | **Yes** |
| `partial_structured_match` | Some structured overlap (e.g. case) without full strict agreement; diagnostic. | **No** |
| `coarse_match` | Stripped-diacritics similarity only. | **No** |
| `mismatch` | No acceptable match (includes clear family/role conflict when gold is confidently parsed). | **No** |

**Anti-false-positive rule:** A row is **never** accepted only because `analyzer_source == L17` or confidence is high. Acceptance requires **confirmed alignment** and **`strict_acceptance_eligible`** (`exact_text_match` or `strict_structural_match` only).

**Skipped alignment** is not a comparator tier; the runner records `comparator_decision=skipped_alignment` when alignment fails.

### Structured debug CSV

`data/quran_i3rab_structured_debug.csv` (override `--structured-debug`) records per-word gold/L17 structured fields, comparator tier, parser confidence/limitations, and reasons. Written by `batch_quarantine.write_structured_debug_csv`.

## Ayah decision engine

For each ayah the runner computes one of:

| Status | Meaning |
| --- | --- |
| `PASS_STRICT` | Every gold word is either already in cumulative erqa **or** newly passes alignment + strict comparator. |
| `FAIL_ALIGNMENT` | At least one word could not be aligned. |
| `FAIL_COMPARATOR` | Aligned, but at least one pending word fails strict acceptance. |
| `FAIL_ANALYSIS` | Missing ayah text or empty pipeline tokens/snapshots. |
| `REVIEW_NEEDED` | Internal inconsistency (e.g. row count mismatch after evaluation). |

**Policy:** No partial ayah writes. Only `PASS_STRICT` ayahs contribute **new** rows to `erqa_i3rab.csv`.

## Repair loop

- Default `--max-repair-attempts 2`.
- Attempt *n* uses `repair_pass = n-1` for alignment (`strip_match_noise` on gold surfaces) and comparator (whitespace collapse on gold iʿrāb text).
- Each attempt is logged to `repair_log.csv`.

## Quarantine files

| File | Semantics |
| --- | --- |
| `data/erqa_i3rab.csv` | Cumulative **append** of **strict-accepted** rows only when `--write-mode` and policy allows. Dedupe by `(surah, ayah, ayah_word_index)`. **Batch 28.12:** `system_i3rab` is the **canonical accepted display**; legacy analyzer prose that contradicted acceptance is preserved in `raw_system_i3rab_before_hardening`; provenance columns (`accepted_analysis_source`, `accepted_structured_signature`, `accepted_role`, `accepted_case_bucket`, `accepted_marker`, `accepted_governing_factor`, `accepted_confidence`, `decision_basis`). **Batch 28.13:** when gold resolves **نعت** (incl. ordinal), prefer that specificity over generic L11 «اسم مجرور»; normalize role vs signature. |
| `data/wrong_i3rab.csv` | **Batch-scoped** (overwrite): rejected comparator rows for the current run when `--write-mode` (not in `--dry-run`). |
| `data/repair_log.csv` | Append-only repair attempts (`timestamp`, `surah`, `ayah`, `attempt_no`, …). |
| `data/ayah_review_queue.csv` | One row per ayah that did not `PASS_STRICT` (merged by surah/ayah). |
| `data/progress_state.json` | Resume checkpoint: `last_completed_ayah`, `last_processed_row_index`, counters, `batch_id`, branch, git head. |
| `data/batch_summary.json` | Compact summary of the last run (includes nested `progress`). |
| `data/quran_i3rab_structured_debug.csv` | Per-word structured comparison debug (Batch 28.4). |
| `data/quran_i3rab_truth_audit.csv` | Row-level truth buckets, blockers, best-possible tier (Batch 28.5). |
| `data/quran_i3rab_unlockable_ayahs.csv` | Per-ayah unlockability summary (Batch 28.5). |
| `data/quran_i3rab_real_accept_preview.csv` | Rows that reached strict tiers; `safe_to_accept_now` is true only if the whole ayah `PASS_STRICT` (Batch 28.5). |
| `data/quran_i3rab_pass_strict_candidates.csv` | Per-ayah discovery scan: decision, tier counts, Batch 28.5 blockers, unlockability (Batch 28.6). |
| `data/quran_i3rab_pass_strict_scan_summary.json` | Aggregates: counts by decision, first 10 `PASS_STRICT` / unlockable ayahs, top blockers (Batch 28.6). |
| `data/write_batches/<batch_id>/` | **Isolated** bounded writes: `erqa_i3rab.csv`, `wrong_i3rab.csv`, `repair_log.csv`, `batch_summary.json`, `accepted_ayahs.csv`, `rejected_ayahs.csv`, `manifest.json`, `review_sample.csv` (Batch 28.6). Does **not** append to repo `data/erqa_i3rab.csv` by default. |
| `data/quran_i3rab_batch_28_10_pattern_selection.json` | Batch 28.10: evidence shortlist and chosen L17 families (fixed schema). |
| `data/quran_i3rab_batch_28_10_before_after.json` | Batch 28.10: baseline vs current-run metrics (`batch_28_10` summary snapshot). |
| `data/quran_i3rab_batch_28_10_promoted_examples.csv` | Batch 28.10: strict-tier rows whose surfaces match 28.10 families (run-inferred). |
| `data/quran_i3rab_batch_28_10_still_blocked_examples.csv` | Batch 28.10: sample L17-core–blocked and conflict rows from truth audit. |
| `data/quran_i3rab_batch_28_10_family_effects.csv` | Batch 28.10: per-family rollout notes. |
| `data/quran_i3rab_batch_28_11_ayah_completion_ranking.csv` | Batch 28.11: per-ayah completion scores / blockers. |
| `data/quran_i3rab_batch_28_11_target_ayahs.csv` | Batch 28.11: top target ayahs (max 5). |
| `data/quran_i3rab_batch_28_11_before_after.json` | Batch 28.11: baseline vs run metrics. |
| `data/quran_i3rab_batch_28_11_promoted_ayahs.csv` | Batch 28.11: ayahs that improved vs baseline status map. |
| `data/quran_i3rab_batch_28_11_still_blocked_ayahs.csv` | Batch 28.11: targets still not PASS_STRICT. |
| `data/quran_i3rab_batch_28_11_blocker_token_examples.csv` | Batch 28.11: token-level examples for targets. |

Legacy `data/quran_i3rab_progress.json` is **not** written by default; use `--progress` to point at `progress_state.json`.

### Batch summary `batch_28_5` (JSON)

`batch_summary.json` includes a `batch_28_5` object with counters such as `rows_unlockable_now`, `rows_blocked_by_l17_core`, `rows_blocked_by_gold_parser_limits`, `rows_blocked_by_true_conflict`, `candidate_real_accept_rows`, and `candidate_real_pass_strict_ayahs` (same value as `pass_strict_ayahs` for the run).

### Batch summary `batch_28_10` (JSON)

Printed JSON and `batch_summary.json` include `batch_28_10`: selected families, before/after metrics vs `BATCH_28_10_BASELINE_LIMIT200` (primary `--limit 200` gold_csv reference), `skipped_probe_families`, `promoted_rows_inferred_b28_10_surface_match`, and `still_core_blocked_top_families`.

### Batch summary `batch_28_11` (JSON)

`batch_28_11` includes `target_ayahs`, `pass_strict_ayahs_before/after`, `near_pass_*_before/after`, `promoted_ayahs_count`, `alignment_coverage_before/after`, and `still_blocked_reasons_summary` (vs `BATCH_28_11_BASELINE_LIMIT200`).

## Batch 28.7 — Discovery expansion (CSV-only ayah option, reporting only)

**Goal:** Better visibility into unlockability, conflicts, tooling-only blockers, and **strict rows trapped in non-`PASS_STRICT` ayahs**, without weakening comparator acceptance.

**Flags:**

- `--discovery-only` — forces `--dry-run`, `--emit-discovery-csvs`, and `--canonical-ayah-source gold_csv` (no uthmani).
- `--emit-discovery-csvs` — write discovery outputs; uses gold-CSV ayah reconstruction (does not load uthmani).
- `--discovery-limit N` — caps gold rows processed (overrides `--limit` / `--max-rows`).
- Optional output overrides: `--discovery-rows-out`, `--discovery-ayah-summary-out`, `--trapped-strict-rows-out`.

**Outputs (defaults under `data/`):**

| File | Role |
| --- | --- |
| `quran_i3rab_discovery_rows.csv` | Per-row discovery bucket, blockers, recommended next action |
| `quran_i3rab_discovery_ayah_summary.csv` | Per-ayah roll-up counts and `recommended_action` |
| `quran_i3rab_unlockable_ayahs.csv` | **Ranked** ayahs by `unlock_score` (replaces legacy unlockable schema for that run) |
| `quran_i3rab_trapped_strict_rows.csv` | Rows strict-eligible in isolation but ayah not `PASS_STRICT` |

`batch_summary.json` includes `batch_28_7_discovery` when discovery CSVs are emitted.

**Quarantine unchanged:** whole-ayah `PASS_STRICT` still required for ERQA append; `exact_text_match` / `strict_structural_match` unchanged.

## Batch 28.6 — `PASS_STRICT` discovery and bounded isolated writes

**Discovery (dry-run for acceptance; writes only CSV + JSON + progress):**

- `--scan-pass-strict` — scan by ayah; merge results into `--pass-strict-candidates-out` (default `data/quran_i3rab_pass_strict_candidates.csv`).
- `--resume-scan` — continue after `pass_strict_scan_last_completed_ayah` in `--progress` (same file as other tooling; keys are merged).
- `--pass-strict-scan-summary-out` — default `data/quran_i3rab_pass_strict_scan_summary.json`.

**Bounded write (only ayahs with `decision_status=PASS_STRICT` in the candidate CSV; default output under `data/write_batches/<batch_id>/`):**

- `--write-mode-pass-strict-only`
- `--candidate-source` — default `data/quran_i3rab_pass_strict_candidates.csv`
- `--max-write-ayahs` — cap (optional; default = all `PASS_STRICT` rows in file after resume filter)
- `--resume-write` — continue using `pass_strict_write_batch_id` / `pass_strict_write_last_completed_ayah` in `--progress`
- `--write-batch-id` / `--write-batch-root` — layout: `<write-batch-root>/<batch_id>/` (default root `data/write_batches`)
- `--allow-non-isolated-output` — required if `--write-batch-root` is not under `data/write_batches/` (safety gate)

Pre-write checks: candidate file exists; at least one `PASS_STRICT` ayah; batch directory is empty (new batch) or an existing resume target; isolated path unless `--allow-non-isolated-output`.

Acceptance policy is unchanged: only `exact_text_match` and `strict_structural_match` via existing comparator / ayah `PASS_STRICT` gate.

## CLI (Batch 28.3–28.6)

| Flag | Default | Notes |
| --- | --- | --- |
| `--verify-erqa PATH` | off | **Partition A:** full ERQA re-validation only (see section above); exit **1** on degradation; no ERQA writes. |
| `--dry-run` | off | When set: no erqa/wrong append; debug/audit/summary/progress still written. |
| `--write-mode` | off | Required to append erqa / write batch wrong file. |
| `--from-surah`, `--from-ayah` | none | Lower bound on ayah keys. |
| `--max-ayahs` | none | Cap number of ayahs. |
| `--max-rows` / `--limit` | none | Stop before an ayah if total gold rows would exceed cap (ayahs are not split). |
| `--max-repair-attempts` | 2 | Bounded repair. |
| `--stop-on-first-unsafe-ayah` | **on** | Stop when first ayah is not `PASS_STRICT`. Use `--no-stop-on-first-unsafe-ayah` to continue. |
| `--require-strict-comparator` | **on** | |
| `--resume` | off | Skip ayahs at or before `last_completed_ayah` in `--progress`. |
| `--alignment-min` | 0.70 | Blocks erqa **append** when run alignment coverage is below threshold (unless `--force-below-alignment-threshold`). |
| `--structured-debug` | `data/quran_i3rab_structured_debug.csv` | Structured gold vs L17 debug rows. |
| `--truth-audit` | `data/quran_i3rab_truth_audit.csv` | Row-level truth audit (28.5). |
| `--unlockable-ayahs` | `data/quran_i3rab_unlockable_ayahs.csv` | Ayah unlockability (28.5). |
| `--real-accept-preview` | `data/quran_i3rab_real_accept_preview.csv` | Strict-tier candidates + `safe_to_accept_now` (28.5). |
| `--scan-pass-strict` | off | Batch 28.6: write candidates CSV + scan summary; no erqa. |
| `--resume-scan` | off | With `--scan-pass-strict`, resume ayah scan. |
| `--write-mode-pass-strict-only` | off | Batch 28.6: isolated batch writes from candidate CSV. |
| `--candidate-source` | `data/quran_i3rab_pass_strict_candidates.csv` | Pass-strict write mode input. |
| `--max-write-ayahs` | none | Cap ayahs in pass-strict write mode. |
| `--resume-write` | off | Resume pass-strict batch from `--progress`. |
| `--write-batch-id`, `--write-batch-root` | auto / `data/write_batches` | Isolated batch folder layout. |
| `--allow-non-isolated-output` | off | Allow non-default batch root (explicit override). |
| `--discovery-only` | off | Batch 28.7: gold CSV ayah only, discovery CSVs, dry-run. |
| `--emit-discovery-csvs` | off | Emit discovery/trapped/ranked-unlockable CSVs (gold CSV ayah). |
| `--discovery-limit` | none | Max gold rows (overrides `--limit`). |
| `--canonical-ayah-source` | `uthmani` | `gold_csv` = join words from gold CSV only. |
| `--discovery-rows-out` / `--discovery-ayah-summary-out` / `--trapped-strict-rows-out` | defaults in `data/` | Optional path overrides. |

## Validation note (Batch 28.4)

On the real `data/quran_i3rab.csv`, **accepted rows often stay at zero** when L17 stays `unresolved` and L11 text does not exactly match the long gold string — that is expected. To confirm that the runner can still **count strict accepts** end-to-end, use the small fixture where gold iʿrāb equals the pipeline L11 string for `بِسْمِ` in Al-Fātiḥah 1:1:

```bash
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py \
  --gold tests/fixtures/quran_i3rab_batch284_l11_exact_smoke.csv \
  --from-surah 1 --from-ayah 1 --max-ayahs 1 --dry-run \
  --max-wrong-rows 500 --no-stop-on-first-unsafe-ayah
```

Expect `accepted_rows_this_batch` ≥ 1 and `pass_strict_ayahs` ≥ 1 (`exact_text_match`).

## Usage examples

```bash
# Dry-run one ayah (no erqa writes)
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py \
  --from-surah 1 --from-ayah 1 --max-ayahs 1 --dry-run \
  --max-wrong-rows 100 --max-repair-attempts 2 --no-stop-on-first-unsafe-ayah

# Small batch dry-run
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py \
  --from-surah 1 --from-ayah 1 --max-ayahs 10 --dry-run \
  --max-wrong-rows 100 --max-repair-attempts 2 --no-stop-on-first-unsafe-ayah

# Explicit write (bounded); use isolated --erqa in experiments
PYTHONPATH=src python3 scripts/run_quran_i3rab_comparison.py \
  --from-surah 1 --from-ayah 1 --max-ayahs 1 --write-mode \
  --max-wrong-rows 100 --max-repair-attempts 2 --no-stop-on-first-unsafe-ayah
```

## Known limitations

- Gold orthography may still differ from Uthmani; alignment normalization mitigates but cannot fix all tokenizer splits.
- The gold parser only emits facts it can justify from phrasing; sparse or allusive gold prose yields **low `parser_confidence`** and fewer strict matches.
- `strict_structural_match` is intentionally conservative; borderline cases skew **false negative**.
