# Stage 4 — Smoke Tests

## Command used

```bash
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py "إِنَّ اللَّهَ غَفُورٌ"
# or
PYTHONPATH=src python3 -c "from orchestrator import run; p = run('...'); print(p['layer_outputs']['L11_I3RAB'])"
```

Or with summary:

```bash
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --summary "إِنَّ اللَّهَ غَفُورٌ"
```

---

## Which stages are real vs placeholder

| Stage | Status | Notes |
|-------|--------|--------|
| L0_INPUT | Placeholder | Input capture; no adapter change. |
| L1_NORMALIZATION | **Real** | OrthographyAdapter.normalize() |
| L2_TOKENIZATION | **Real** | From c2b.words (WordBoundaryDetector path) |
| L3_SEGMENTATION | **Real** | From c2b.words affixes (prefix/suffix/stripped) |
| L4_OPERATORS | **Real** | From c2b.words (kind, operator) |
| L5_WORD_TYPING | **Real** | From c2b.words (kind) |
| L6_PHONOLOGY | **Real** | From c1, c2a, cv_analysis |
| L7_SYLLABIFICATION | **Real** | From c2a.syllables |
| L8_ROOT_EXTRACTION | **Real** | From c2b.words (root) |
| L9_WAZN_MATCHING | **Real** | From c2b.words (pattern, word_wazn) |
| L10_SYNTAX | **Real** | From syntax (word_forms, links); **often fails** (see below) |
| L11_I3RAB | **Real** | From c2b.c2e.i3rab_text per word |
| L12_SEMANTIC_RHETORICAL | **Real** | From c2d, rhetoric_signals |
| L13_VALIDATION | Placeholder | pass_through |
| L14_PRESENTATION | Placeholder | pass_through |

---

## Smoke run results (four inputs)

| Input | Label | L11 status | L10 status | Token count |
|-------|--------|------------|------------|-------------|
| إِنَّ اللَّهَ غَفُورٌ | verse | success | failed | 3 |
| كَاتِبٌ | single | success | failed | 1 |
| هَلْ تَعْلَمُ؟ | question | success | failed | 2 |
| يَا رَبِّ | vocative | success | failed | 2 |

- **Orchestrator** completes for all inputs.
- **L11 i3rab** is explicit and returns `token_results` with `i3rab_text` from existing c2e output (success).
- **L10 syntax** returns `status: failed` with an error message in `errors` (e.g. `WordFormBuilder ... from_multi_word_item`). This matches the known runtime limitation documented in Stage 1; the adapter captures it structurally instead of crashing the pipeline.

---

## Warnings / errors observed

1. **L10_SYNTAX**: Consistently fails with a runtime error from the syntax layer (`WordFormBuilder` / `from_multi_word_item`). Documented in `docs/current_entrypoints.md` and `docs/gap_analysis.md`. The Stage 4 adapter sets `status: "failed"` and stores the exception text in `errors`; the rest of the pipeline continues.
2. **FVAFK run**: If the initial `run_fvafk_once(text)` fails, `_fvafk_result` has `success: false` and adapters emit partial/missing; no uncaught exception.

---

## Verification checklist

- [x] Orchestrator runs end-to-end on all four smoke inputs.
- [x] Real stages (L1–L12) produce non-placeholder outputs where FVAFK provides data.
- [x] Syntax errors are captured in L10 (status=failed, errors list).
- [x] L11 i3rab is explicit and populated from `c2b.c2e.i3rab_text` (no longer “missing” when enrichment runs).
- [x] Internal key `_fvafk_result` is removed from the final pipeline object (Stage 2 contract preserved).
