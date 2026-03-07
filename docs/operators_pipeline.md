# Operators catalog pipeline

This document describes the operators catalog generation pipeline: canonical output, what is generated vs committed, typed Quran evidence, and how defaulting works.

## Canonical output

- **Canonical path:** `data/operators_catalog_split_project_enriched.csv`
- **Backward-compatibility alias:** The generator copies the canonical file to `data/operators_catalog_split_enriched.csv` so existing code that expects the legacy path still works.
- **Loaders:** Code that loads the operators catalog (e.g. `OperatorsCatalog`, `SpecialWordsDatabase`, `run_complete_snapshot.load_operators_catalog`) **prefers the enriched canonical file**, then falls back to `operators_catalog_split_enriched.csv`, then `operators_catalog_split.csv`. Set **`FVAFK_OPERATORS_CSV`** to a path to override (e.g. for tests or a custom CSV).
- **One command:** From repo root, run:
  ```bash
  bash scripts/generate_operators_catalog_enriched.sh
  ```
  Then run QA:
  ```bash
  python3 scripts/qa_operators_enriched.py
  ```

## What is generated vs committed

| Artifact | Generated | Typically committed |
|----------|-----------|----------------------|
| `data/operators_catalog_split_project.csv` | Yes (from JSONL) | No (build artifact) |
| `data/operators_catalog_split_project_with_evidence.csv` | Yes | No |
| `data/operators_catalog_split_project_with_evidence.jsonl` | Yes | No (debug/traceability) |
| `data/operators_catalog_split_project_enriched.csv` | Yes | Optional (if you version datasets) |
| `data/operators_catalog_split_enriched.csv` | Yes (copy of canonical) | Optional |
| `scripts/*.py`, `scripts/*.sh` | — | Yes |
| `src/fvafk/c2b/read_inputs_for_enrichment_pipeline.py` | — | Yes |

If the repo treats `data/*.csv` as build artifacts, keep them out of version control and regenerate with the script above. If it version-controls the canonical dataset, commit `data/operators_catalog_split_project_enriched.csv` (and optionally ignore intermediate evidence files).

## Typed Quran evidence

Evidence is taken from `data/quran_i3rab.csv` (surah, ayah, word, i3rab) and attached per operator.

- **No diacritic stripping:** Matching uses vowelized forms only (exact and prefix/clitic rules).
- **Types:** Each evidence line is labeled by an i3rab-derived type (e.g. JAR, NEG, NIDA, ACC_TAWKID, MUQATTAAT). Types are detected from keywords in the i3rab text (see `TYPE_RULES` in `scripts/build_operator_evidence_from_quran_i3rab.py`).
- **Caps:** Up to **5 types** per operator and up to **2 evidence lines per type** (configurable via `MAX_TYPES_PER_OPERATOR` and `MAX_EVIDENCE_PER_TYPE`).
- **Matching order:** (1) Exact and prefixed word forms (operator as token, or و/ف/ب/ك/ل/س + operator), (2) clitic-attached forms (e.g. بِسْمِ for بِ) for a fixed set of clitics, (3) strict prefix+operator endswith (prefix only from a fixed set, length 1–2).
- **Output:** Evidence is stored in `project_quran_evidence_phrases` as tagged strings (`TYPE=JAR::surah:ayah:word -> i3rab ...`) and in the JSONL as `project_quran_evidence_by_type` for debugging.

## Defaulting (effect signature, usage, template)

Many rows in the source JSONL do not have `project_effect_signature`, `project_usage_universal_ar`, or `project_i3rab_template`. These are filled in **scripts/jsonl_to_operators_csv.py** before evidence and enrichment run.

- **When:** During JSONL → project CSV conversion. Defaults are applied only when a field is empty.
- **Sources:** (1) **Arabic Group Name** → effect signature via `GROUP_TO_SIGNATURE`. (2) **Note** overrides: if the Note contains phrases like “حرف قسم”, “حرف جر”, “حرف عطف”, “حرف توكيد”, the signature is set from that instead of the group. (3) **DEFAULTS_BY_SIGNATURE**: for each signature, a generic Arabic usage line and an i3rab template (optional for e.g. MUQATTAAT).
- **Signatures:** GEN, OATH_GEN, CONJ, ISTITHNA, ACC_TAWKID, NEG, COND, NIDA, NASB, JAZM, MAIYYA, MUQATTAAT, AMR_TA3AJJUB, MUQARABA, MADH_DHAMM (see `DEFAULTS_BY_SIGNATURE` and `GROUP_TO_SIGNATURE` in the script).

### How to add a new group signature

1. **Add usage and template** in `scripts/jsonl_to_operators_csv.py`:
   - In `DEFAULTS_BY_SIGNATURE`, add an entry for the new signature, e.g.:
     ```python
     "MY_SIG": {
         "project_usage_universal_ar": "…",
         "project_i3rab_template": "…",  # or "" if no template
     },
     ```
2. **Map the group** in `GROUP_TO_SIGNATURE`:
   - Add `"Arabic Group Name exact string": "MY_SIG"`.
3. **Optional:** If the same group can be identified from Note text, add a pair to `NOTE_OVERRIDES`: `("needle in Note", "MY_SIG")`.
4. **Optional:** If the signature may have a blank template (like MUQATTAAT), add it to the `template_optional` check in `scripts/qa_operators_enriched.py` so QA does not require a template for that signature.
5. Re-run `bash scripts/generate_operators_catalog_enriched.sh` and `python3 scripts/qa_operators_enriched.py`.

## Pipeline steps (high level)

1. **jsonl_to_operators_csv.py**  
   Reads `data/operators_catalog_split_enriched.jsonl`, skips header-artifact rows, applies project defaults, writes `data/operators_catalog_split_project.csv`.

2. **build_operator_evidence_from_quran_i3rab.py**  
   Reads the project CSV and `data/quran_i3rab.csv`, attaches typed evidence per operator (5 types × 2 lines/type), writes `data/operators_catalog_split_project_with_evidence.csv` and `.jsonl`.

3. **read_inputs_for_enrichment_pipeline.py**  
   Reads the with-evidence CSV, adds mechanical columns (operator_has_diacritics, operator_prefixes, operator_stem, etc.) and derived columns (schema_version, row_id, project_quran_evidence_list_json, project_quran_evidence_count, etc.), writes `data/operators_catalog_split_project_enriched.csv`.

4. **Copy**  
   The generator script copies the enriched CSV to `data/operators_catalog_split_enriched.csv` for backward compatibility.

5. **QA**  
   `scripts/qa_operators_enriched.py` checks: row count > 0 and row_id unique; clitic evidence counts; فِي not peeled; no header-artifact row; and that every row with a signature has usage (and template except when allowed blank).
