# Stage 15 core-link restoration + canonical root/stem/wazn (batch)

**Date:** 2026-03-19 (log-aligned)  
**Scope:** Generalized morphology and Stage 15 dependency rules — **no sentence-specific hardcoding** in `analyze_sentence.py` beyond additive display that reads `ARABIC_WORD_STATE`.

## Goals addressed

1. **Canonical morphology in `ARABIC_WORD_STATE`**  
   Fields: `canonical_stem`, `canonical_root`, `canonical_wazn`, `wazn_inference_rule` (plus existing `root`, `raw_l8_root`, `stem`, L9 templates). Rebuild applies `canonical_derivation.apply_canonical_derivation_to_word_state_entry` after hollow and L8/L9 alignment.

2. **Stem-based derivational wazn**  
   Module: `src/orchestrator/canonical_derivation.py`  
   - Hollow active participle shape / confirmed hollow → `فَاعِل` on canonical stem.  
   - Geminate triliteral verb stem (e.g. Form IV surface `أَفْعَلَ` stripped to `عَدَّ`) → `فَعَّ` (overrides bad L9 `فَعَلَّ`-style spellings when root is C-C-C with C₂=C₃).  
   - `مت…` stems with safe length → `مُتَفَعِّل` heuristic.

3. **Downstream consumers**  
   - **L14:** morphology bridge prefers `canonical_*` from word state before raw L8/L9.  
   - **L17:** reasoning prefers canonical root/stem/wazn when present.  
   - **`scripts/analyze_sentence.py`:** root/wazn table rows prefer `build_root_wazn_display_rows` / canonical state when available.

4. **Stage 15 (`dependency_syntax/builder.py`)**  
   - **Pass E2:** strong finite verb → local SUBJ/OBJ (with clitic skip, lone indefinite object cue, APPOS loop skips strong verb tokens).  
   - **Pass E3:** `ISM_FAIL` governor → immediate following noun-like token → `OBJ`; **supersedes** weak `nominal_mubtada_to_khabar` `PRED` on the same pair when participial object evidence applies.  
   - **`_has_pp_prefix`:** uses **multi-letter** preposition-like clusters (`كال`, `في`, `من`, …) instead of single-letter starts, so tokens like **فُرُوجَهُمْ** are not mistaken for **في**-prefixed forms.

## Tests

- `tests/orchestrator/test_stage15_canonical_morphology_batch.py` — hollow صائم tokens, `أَعَدَّ`, non-reference `قَائِلٌ`, minimal Stage 15 shells for verbal clause + `ISM_FAIL` object.  
- `tests/orchestrator/test_hollow_ism_fail.py` — tolerates `wazn_ism_fail_pattern` when canonical wazn already fills `فَاعِل`.

## Related docs

- `docs/architecture/PIPELINE_MASTER_MEMORY.md` — Section 4, 8 Change Log.  
- `docs/research/FVAFK_MASTER_EVOLUTION.md` — Engine Evolution Log.  
- `docs/architecture/SCIENTIFIC_NEXT_PHASES.md` — Phase Delta/Epsilon status.  
- `docs/dependency_syntax_builder.md` — Stage 15 builder overview.
