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
| L10_SYNTAX | **Real** | From syntax (word_forms, links). Runs successfully in tested paths. See *L10 classification* below. |
| L11_I3RAB | **Real** | From c2b.c2e.i3rab_text per word |
| L12_SEMANTIC_RHETORICAL | **Real** | From c2d, rhetoric_signals |
| L13_VALIDATION | Placeholder | pass_through |
| L14_PRESENTATION | Placeholder | pass_through |

---

## Smoke run results (four inputs)

| Input | Label | L11 status | L10 status | Token count |
|-------|--------|------------|------------|-------------|
| إِنَّ اللَّهَ غَفُورٌ | verse | success | **success** | 3 |
| كَاتِبٌ | single | success | **success** | 1 |
| هَلْ تَعْلَمُ؟ | question | success | **success** | 2 |
| يَا رَبِّ | vocative | success | **success** | 2 |

- **Orchestrator** completes for all inputs.
- **L11 i3rab** is explicit and returns `token_results` with `i3rab_text` from existing c2e output (success).
- **L10 syntax** now returns `status: success` in tested paths.

---

## L10 syntax — classification (minimal compatibility fix)

The L10 syntax runtime issue is **fixed**. This was a **minimal compatibility/stability fix**, not a rewrite of analyzer logic.

- **Cause of prior failure:** Missing integration helpers in the CLI/orchestrator path. The CLI expected `WordFormBuilder.from_multi_word_item(...)` and `_word_form_to_syntax_dict(...)`, which were not implemented. The failure was **not** due to a confirmed failure of the syntax engine itself (IsnadiLinker / find_isnadi_links, SentenceClassifier).
- **What was done:** (1) `from_multi_word_item(...)` was added to `WordFormBuilder` and **forwards to** `from_c2b(...)` only, restoring the existing integration path. (2) `_word_form_to_syntax_dict(...)` was added in the CLI **only to expose syntax output** (word_forms) in the CLI/orchestrator path. No syntax analysis logic was redesigned or replaced.
- **Result:** L10 syntax now runs successfully in the tested morphology path; pipeline architecture focus is unchanged.

---

## Warnings / errors observed

1. **L10_SYNTAX (resolved):** Prior failure was due to missing integration helpers (`from_multi_word_item`, `_word_form_to_syntax_dict`), not the syntax engine. Resolved by the minimal compatibility fix above.
2. **FVAFK run**: If the initial `run_fvafk_once(text)` fails, `_fvafk_result` has `success: false` and adapters emit partial/missing; no uncaught exception.

---

## Verification checklist

- [x] Orchestrator runs end-to-end on all four smoke inputs.
- [x] Real stages (L1–L12) produce non-placeholder outputs where FVAFK provides data.
- [x] L10 syntax runs successfully in tested paths (minimal compatibility fix: missing integration helpers restored; no analyzer rewrite).
- [x] L11 i3rab is explicit and populated from `c2b.c2e.i3rab_text` (no longer “missing” when enrichment runs).
- [x] Internal key `_fvafk_result` is removed from the final pipeline object (Stage 2 contract preserved).
