# Root Extraction RCA and Fix Plan (Mishkat)

## Context

- Module: `src/fvafk/c2b/root_extractor.py`
- Current benchmark (reported): `F1 = 0.718` on Mishkat gold corpus (`16,421` words)
- High-error patterns include:
  - attached single-letter prefixes not stripped in some paths
  - alif/hamza normalization ambiguity
  - suffix handling gaps (especially feminine plural and dual+pronoun forms)

## Pipeline Observation

- C2a phonology gates run in parallel and **do not** feed C2b morphology root extraction.
- Root extraction in C2b is based on the raw input string through:
  - normalization
  - affix stripping
  - consonant extraction
  - root validity checks.

## Root Causes (summarized)

1. **Nun al-niswa gap**  
   Bare suffix `ن` is excluded from generic suffix stripping to avoid ambiguity, but this leaves many verb feminine-plural forms unstripped (e.g. `...ْنَ` patterns).

2. **Dual + pronoun suffix combinations not covered**  
   Suffixes like `يه` / `يهما` / `يهم` / `يهن` are common in Arabic (especially Quranic forms), but not fully covered in pronominal stripping.

3. **Genitive lam (`لِـ`) ambiguity**  
   Existing lam stripping focuses on lam of purpose/command (`ل + imperfect prefix`) and misses some genitive `لِـ` cases before nouns (especially hamza/alif-initial stems).

## Fixes to implement (step-by-step)

### Fix 1 — Conditional `ن` stripping for feminine plural verbs

- File: `src/fvafk/c2b/root_extractor.py`
- In `_strip_affixes`, after pronoun stripping and before inflectional suffix stripping:
  - If `original_word` ends with `ْنَ`
  - and normalized `text` ends with `ن`
  - and at least 3 letters remain after removal
  - then strip trailing `ن`.

This keeps the fix linguistic (verb morphology) and avoids global over-stripping.

### Fix 2 — Add dual+pronoun suffix forms to pronominal set

- File: `src/fvafk/c2b/root_extractor.py`
- Extend `PRONOUN_SUFFIXES` with compound forms:
  - `يهم`, `يهن`, `يهما`, `يه`, `يها`, `يك`.

These are stripped in stage 4a (already protected with minimum-remain checks).

### Fix 3 — Detect and strip genitive `لِـ` using diacritized surface

- File: `src/fvafk/c2b/root_extractor.py`
- Add a conservative helper for lam-genitive using `original_word`:
  - detect starts like `لِ...` (and attached with `وَ` / `فَ` forms when applicable)
  - strip lam only when enough letters remain.

This complements existing lam-of-imperfect logic without replacing it.

## Safety and Regression Notes

- Fixes are additive and localized to `_strip_affixes` behavior.
- Priority remains:
  - no-split protections
  - guarded affix stripping
  - minimum length constraints before peel.
- Validate via:
  - `tests/c2b/test_root_extractor.py`
  - full test suite (`846` passing baseline mentioned).

## Execution Status

- This document is the implementation baseline.
- Next steps are code changes in `root_extractor.py`, followed by targeted and full test runs.
