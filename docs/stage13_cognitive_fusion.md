# Stage L13 — Cognitive Fusion Layer

## Fusion Is Arbitration, Not Inference

The Cognitive Fusion stage **reconciles**, **prioritizes**, **stabilizes**, and **reduces ambiguity** across upstream evidence. It does **not** infer new linguistic facts. It does **not** override structural evidence from higher-priority sources. It only:

* Combines evidence from L4 (operators), L5 (word typing), L8 (root), L9 (wazn), L10 (syntax), L11 (i3rab), L12 (rhetorical), L12B (analogical) and the pre_stage13_audit.
* Applies a fixed **hierarchy**: Root+Wazn > Operator > Morpho > Syntax > I3rab > Analogical > Rhetorical. If a lower layer contradicts a higher one, the lower is ignored.
* Produces per-token **fusion_state** (stable_pos, stable_role, confidence, evidence_stack, conflicts_resolved, ambiguities_remaining) and a global summary.

## Difference Between Reasoning and Hallucination

* **Reasoning** — Using only what upstream stages produced: e.g. “L5 says noun, L8 says root ك-ت-ب, L9 says wazn فاعل → stable_pos noun, evidence_stack [ROOT, WAZN, WORD_TYPING].” No new root or wazn is invented.
* **Hallucination** — Would be: inventing a root not in L8, or a wazn not in L9, or a syntactic role with no L10 evidence, or upgrading a weak rhetorical hint to a grammatical fact. The fusion layer **must not** do this. If it did, the token would be marked `fusion_error_flag = true`.

## Scientific Limitation of Current Syntax Depth

Current L10 (syntax) provides light-weight links (e.g. isnadi) and word forms, not a full dependency tree. Therefore:

* **stable_role** is only set when there is explicit syntax evidence (e.g. role/syntax_role in word_forms or links). Fusion does not assign roles without evidence.
* In **conservative** mode (when pre_stage13_audit readiness_band is LOW), fusion does not resolve syntactic roles, does not infer tense shifts, and does not apply analogical expansion. It only confirms stable_pos, root_consistency, and basic definiteness.

## Confidence Computation

Confidence is deterministic:

`confidence = sum(weight of supporting sources) / sum(weight of all available sources)`

clamped to [0.05, 0.98]. The stage never outputs 1.0 or 0.0. Global confidence is the mean of per-token confidence.

## Output Shape

* **pipeline["cognitive_fusion"]**: fusion_mode, token_states, global_confidence, tokens_high_confidence, tokens_low_confidence, unresolved_ambiguities.
* **Per-token**: stable_pos, stable_role, tense_final, definiteness_final, number_final, gender_final, confidence, evidence_stack, conflicts_resolved, ambiguities_remaining, fusion_error_flag.

## Roadmap for Probabilistic Fusion Later

The current fusion is deterministic and rule-based. A future evolution could:

* Replace or extend with a **probabilistic fusion** model that assigns confidence from a learned model while still respecting the same safety rules (no invention, hierarchy).
* Use **pre_stage13_audit** source weights and availability as features.
* Keep the same output schema (token_states, global_confidence) so that presentation and downstream stages do not need to change.
