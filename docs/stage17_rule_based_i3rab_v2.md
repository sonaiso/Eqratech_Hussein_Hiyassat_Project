# Stage 17 v2 — Agreement-Aware and Derivational Refinement

Stage 17 v2 builds on v1 by consuming **L12_GENDER_NUMBER** and **L14_JAMID_MUSHTAQ** to refine iʿrāb decisions. v1 rules remain the baseline; v2 adds confidence/ambiguity refinement and evidence annotations when L12/L14 are present.

## Evidence sources (v2)

1. **L12_GENDER_NUMBER**
   - `gender`, `number`, `number_type`
   - `agreement_status`, `agreement_candidates`
   - `tamyiz_relation`

2. **L14_JAMID_MUSHTAQ**
   - `derivational_class` (ISM_FAIL, ISM_MAFUUL, MASDAR, JAMID, VERB, PARTICLE, etc.)
   - `jamid_or_mushtaq`

Used to enrich `reasoning_steps`, `evidence_sources`, and optional additive fields: `agreement_evidence`, `derivational_evidence`, `refinement_applied`.

## Refinement rules (V2-1 to V2-9)

| Rule | Description |
|------|-------------|
| **V2-1** | SIFA + L12 agreement → strengthen confidence for adjective-compatible interpretation; add "Stage15:SIFA + L12:agreement". |
| **V2-2** | SIFA + L12 conflict → reduce confidence, set agreement_evidence = SIFA_conflict, add to ambiguity_log. |
| **V2-3** | L14 derivational class → ISM_FAIL supports noun-agent; ISM_MAFUUL supports patient/object-like; add derivational_evidence. |
| **V2-4** | OBJ + L14 MASDAR → lower confidence, do not blindly force مفعول به; add ambiguity note. |
| **V2-5** | L14 JAMID → add "syntax/dependency first"; do not over-derive from mushtaq patterns. |
| **V2-6** | L12 tamyiz_relation → record "L12:tamyiz_relation — counted/quantity relation" in reasoning_steps. |
| **V2-7** | SUBJ + L12 agreed → increase فاعل confidence; if conflict → lower confidence and log. |
| **V2-8** | NAIB_SUBJ + L12 agreed → strengthen نائب فاعل confidence. |
| **V2-9** | L12 number_type dual/plural → add "plural/dual aware" step; do not force singular logic. |

## Output (backward compatible)

- All v1 keys retained: `token_reasoning[]`, `reasoning_summary`, `coverage`, `ambiguity_log`.
- Per-token additive fields when applicable: `agreement_evidence`, `derivational_evidence`, `refinement_applied`.
- No renames or removals.

## Non-goals

- No full naʿt engine, tamyiz iʿrāb engine, mubtada/khabar agreement engine, semantic roles, or rhetorical reasoning.
- Refinement only; v1 remains the authority for role assignment.

## Confidence / ambiguity policy

- Agreement support → small confidence boost (capped at CONF_GOOD or CONF_STRONG).
- Conflict → confidence reduced, entry in `ambiguity_log`.
- MASDAR vs OBJ → confidence capped at CONF_CANDIDATE when MASDAR.

## Files

- `src/orchestrator/l17_rule_based_i3rab.py` — `_l12_features_by_token_id`, `_l14_classification_for_token`, `_apply_v2_refinement`, integration in `build_rule_based_i3rab`.
- `tests/orchestrator/test_stage17_rule_based_i3rab_v2.py` — v2 tests (subject/SIFA/JAMID/MASDAR/tamyiz/naib fa'il, schema, regressions, v1 baseline when L12/L14 missing).

## When L12 or L14 missing

Stage 17 runs as v1 only; no refinement step. Output schema unchanged; optional v2 fields simply absent.
