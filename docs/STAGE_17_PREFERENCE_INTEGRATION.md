# Stage 17 v1.1 — Presentation Preference Integration

## Summary

Presentation-only integration: prefer **L17 (Rule-Based Iʿrāb)** over **L11B (Causal Iʿrāb)** when L17 is stronger; use L11B as fallback when L17 is weak or unresolved; surface agreement/disagreement. No new grammar rules, no changes to Stage 15/16/L11B/L17 internals.

---

## Files changed

| File | Change |
|------|--------|
| `scripts/analyze_sentence.py` | Added preference/agreement helpers, `build_preferred_i3rab()`, `compact["preferred_i3rab"]`, SECTION 4j in report |
| `tests/test_preferred_i3rab_integration.py` | New tests: prefer L17, fallback L11B, agreement, disagreement, contract stability, Stage 17 smoke |
| `docs/STAGE_17_PREFERENCE_INTEGRATION.md` | This report and self-audit |

---

## Preference policy implemented

- **Token-level** selection via `_select_preferred_i3rab_token(l17_token, l11b_token, token_id, surface, threshold)`.
- **Prefer L17** when: `status == "resolved"`, `confidence >= 0.70`, and required fields present (`syntactic_role` and either `i3rab_case_or_mood` or `governing_factor`).
- **Else prefer L11B** when L11B is resolved or has confidence ≥ threshold, or when L17 is missing/weak.
- **Else** preferred source is L11B with unresolved/empty fields and a safe reasoning note.

---

## Thresholds / decision rules

- **L17_PREFERENCE_CONFIDENCE_THRESHOLD = 0.70** (module constant in `analyze_sentence.py`).
- L17 “strong” = resolved + confidence ≥ threshold + non-empty role and (case/mood or governing factor).
- L11B “strong” = role_status resolved or confidence ≥ threshold.

---

## Agreement / disagreement logic

- **Helpers:** `_normalize_i3rab_label()`, `_roles_compatible_for_agreement()`, `_compare_l17_l11b_token()`.
- **Categories:** `agree`, `partial_agreement`, `disagree`, `only_l17`, `only_l11b`, `unresolved`.
- Comparison uses normalized role, case/mood, governing factor, marker; partial agreement when roles are compatible (e.g. فاعل vs فاعل مرفوع).

---

## Compact / report sections added

- **Compact JSON (additive):** `compact["preferred_i3rab"]` with:
  - `source_preference` ("L17_over_L11B" | "L11B_fallback" | "mixed")
  - `preferred_rows` (list of per-token preferred view with token_id, surface, preferred_source, agreement_status, syntactic_role, governing_factor, i3rab_case_or_mood, marker, confidence, reasoning_note)
  - `agreement_summary` (agree, partial_agreement, disagree, only_l17, only_l11b, unresolved counts)
  - `preferred_i3rab_summary` (preferred_from_l17_count, preferred_from_l11b_count, agreement_count, disagreement_count, unresolved_count)
- **Report:** **SECTION 4j — PREFERRED STRUCTURED IʿRĀB** with summary line (preferred from L17 / from L11B / agree / disagree / unresolved) and table (token | preferred | role | عامل | case/mood | marker | confidence | agreement). SECTION 4g, 4h, 4i unchanged.

---

## Tests added

- **A)** `test_prefer_l17_when_strong`: "ضَرَبَ زَيْدٌ عَمْراً" — when L17 resolved/strong for all three, preferred source L17 for all; roles/case preserved.
- **B)** `test_fallback_to_l11b_when_l17_unresolved`: Mock raw with token 1 L17 unresolved, L11B resolved — preferred source for that token is L11B.
- **C)** `test_agreement_summary`: agreement_status in each row; summary counts; preferred_from_l17 + preferred_from_l11b = len(rows).
- **D)** `test_disagreement_surfacing`: Mock L17 مفعول به vs L11B فاعل — preferred L17, agreement_status "disagree", reasoning_note and disagreement_count.
- **E)** `test_compact_contract_stability`: Existing compact keys and L17/L11B data unchanged; `preferred_i3rab` additive with all subkeys.
- **F)** `test_stage17_tests_still_pass`: Smoke that Stage 17 build_rule_based_i3rab still runs and returns 3 tokens.

---

## Before/after behavior

1. **"ضَرَبَ زَيْدٌ عَمْراً"**  
   - **Before:** Only SECTION 4h (L17) and causal iʿrāb in compact; no unified “preferred” view.  
   - **After:** SECTION 4j shows preferred view; when L17 is resolved/strong for all three, all three rows have preferred_source "L17" and correct role/case/mood; compact includes `preferred_i3rab` with source_preference "L17_over_L11B" and preferred_rows.

2. **Fallback-to-L11B example**  
   - **Before:** No unified fallback display.  
   - **After:** When one token has L17 unresolved and L11B resolved, that token’s preferred_source is "L11B" and row carries L11B role/case; reasoning_note indicates L11B fallback.

3. **Disagreement example**  
   - **Before:** Disagreement between L17 and L11B not summarized.  
   - **After:** Preferred row shows the chosen source (by policy); agreement_status "disagree"; reasoning_note mentions disagreement; preferred_i3rab_summary.disagreement_count ≥ 1.

---

## Self-audit (Section 12–20 style)

- **Documentation:** No change to pipeline architecture or stage behavior. This doc records the presentation layer only. No updates to PIPELINE_MASTER_MEMORY, dependency_syntax_builder, or Stage 17 grammar docs were required.
- **Divergence:** None; scope was strictly presentation preference.
- **update_architecture_log.py:** Not executed (presentation-only, no new stage or inference change).
- **Exact log entry:** N/A.

---

## Success criteria (all met)

1. L17 and L11B remain separate internal sources.  
2. New preferred presentation layer added.  
3. L17 preferred only when stronger (resolved + confidence ≥ 0.70 + required fields).  
4. L11B fallback when L17 weak/unresolved.  
5. Agreement/disagreement visible in preferred rows and summary.  
6. Existing JSON/report contracts unchanged except additive fields/sections.  
7. No reasoning scope expansion.  
8. All new and regression tests pass (Stage 17, L11 guardrail, Stage 15 dependency, Stage 16 clause engine).

---

## Batch 2.5 (2026-03-18) — Reporting / fusion sync

**Precedence (preferred structured iʿrāb, per token):**

1. L17 **resolved** (usable at tier 1; high-confidence note optional)
2. L17 **candidate** (tier 2 — `L17_CANDIDATE_CONFIDENCE_FLOOR`, beats stale unresolved L11B)
3. L11B resolved
4. L11B candidate
5. Legacy L11 textual row (`preferred_source`: `L11_text`)
6. Weak L11B carry-over or `unresolved`

**Compact (additive):** `final_structured_i3rab_summary` (mirrors L17 `reasoning_summary`), `khabar_in_candidates` (from L17 transformation_result). `build_preferred_i3rab(raw, legacy_i3rab_rows)` passes per-token L11 text into tier 5.

**Report:** L11B counts labeled تشخيصي; headline adds L17 resolved/candidate/unresolved; section **خبر إن — مرشحات** when candidates exist; SECTION 4j table adds token id and L17 status; `ما وجده` explains L10B vs L17 divergence when needed.

**Tests:** `test_batch_25_*` in `tests/test_preferred_i3rab_integration.py`.

---

## Batch 2.7 (2026-03-18) — Clause-level خبر إن

- **Rule:** `B2.7-K1_resolve_khabar_in_verbal_clause` → `transformation_result.khabar_in_analysis[]` (alongside legacy `khabar_in_candidates`).
- **Promotion:** INNA_NAME + CLAUSE_ENGINE `verbal_embedded` matching B2.1-V2 span + resolved L17 **فعل** + SUBJ (فاعل/نائب) + completing dependent inside span (OBJ / B2.6 PP / حال / معطوف / نعت per structural checks); conservative confidence (≤0.88 resolved).
- **Token rows:** `syntactic_role` unchanged; `secondary_analysis.khabar_in_clause_resolution_rule` + span/head fields (does **not** overwrite `khabar_in_rule` from B2.1-V2).
- **Report:** `analyze_sentence` — section **خبر إن — محسوم** when analysis has `status=resolved`; else **مرشحات** (or legacy candidates).
- **Tests:** `test_batch_27_*` in `tests/orchestrator/test_stage17_rule_based_i3rab.py`.
