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
| L10_SYNTAX | **Real** | From syntax (word_forms, links). Fixed: WordFormBuilder.from_multi_word_item + _word_form_to_syntax_dict. |
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
- **L10 syntax** now returns `status: success` (fixed: added `WordFormBuilder.from_multi_word_item` and `_word_form_to_syntax_dict` in CLI).

---

## Warnings / errors observed

1. **L10_SYNTAX (fixed)**: Previously failed with `WordFormBuilder` object has no attribute `from_multi_word_item` and `_word_form_to_syntax_dict` not defined. Fix: (1) Added `from_multi_word_item(item, word_id)` to `WordFormBuilder` delegating to `from_c2b`. (2) Added `_word_form_to_syntax_dict(wf, index)` in `fvafk/cli/main.py` returning `wf.to_dict()` with `id` set.
2. **FVAFK run**: If the initial `run_fvafk_once(text)` fails, `_fvafk_result` has `success: false` and adapters emit partial/missing; no uncaught exception.

---

## Verification checklist

- [x] Orchestrator runs end-to-end on all four smoke inputs.
- [x] Real stages (L1–L12) produce non-placeholder outputs where FVAFK provides data.
- [x] L10 syntax runs successfully (WordFormBuilder.from_multi_word_item + _word_form_to_syntax_dict fix).
- [x] L11 i3rab is explicit and populated from `c2b.c2e.i3rab_text` (no longer “missing” when enrichment runs).
- [x] Internal key `_fvafk_result` is removed from the final pipeline object (Stage 2 contract preserved).
