# PIPELINE MASTER MEMORY

**Single authoritative architectural memory for the FVAFK Arabic Linguistic Reasoning Engine.**  
Prevents context drift, preserves architectural continuity, and orients agents and developers.

---

## 1. PROJECT IDENTITY

FVAFK is evolving from:

- **From:** Arabic Morphological Analyzer (root, wazn, textual iʿrāb)

**Into:**

- **To:** Arabic Linguistic Reasoning Engine (layered reasoning, causal grammar, structural semantics, explainability)

The system remains deterministic and rule-based; it is not a statistical parser.

---

## 2. PIPELINE PHILOSOPHY

Pipeline direction (conceptual flow):

1. **Phonology** — sound/unit modeling (L6, L7)
2. **Morphology** — segmentation, operators, word typing, root extraction, wazn (L2–L5, L8, L9)
3. **Syntax** — shallow syntax (L10), deep dependency graph (L10B)
4. **Causal grammar** — textual iʿrāb (L11), causal iʿrāb reasoning (L11B)
5. **Reasoning** — rhetorical signals (L12), analogical reasoning (L12B), cognitive fusion (L13)
6. **Validation** — stage consistency and confidence (L13_VALIDATION)
7. **Explainability** — evidence trace and presentation (L14, evidence_trace)

Additive enrichment layers (no pipeline stage number): L8B verb bab governance, L8C valency seed, SEMANTIC_ROLE_PROJECTION, connectives knowledge, DISCOURSE_FRAME_BUILDER. They run at defined points but do not extend the fixed STAGE_ORDER.

---

## 3. STAGE EVOLUTION HISTORY

| Stage | Name | Role |
|-------|------|------|
| L0 | INPUT | Raw sentence ingestion. |
| L1 | NORMALIZATION | Text normalization. |
| L2 | TOKENIZATION | Token list from normalized text. |
| L3 | SEGMENTATION | Segmentation. |
| L4 | OPERATORS | Operator/particle detection (e.g. حرف جر، أداة شرط). |
| L5 | WORD_TYPING | Basic word typing (kind: verb, noun, etc.). |
| L6 | PHONOLOGY | Phonological modeling (CV, units). |
| L7 | SYLLABIFICATION | Syllabification. |
| L8 | ROOT_EXTRACTION | Root extraction (جذر). |
| L8B | VERB_BAB_GOVERNANCE | Verb bab governance, passive detection, transitivity, expected_subject_role. |
| L8C | (Valency seed) | Valency matrix seed layer (data + lookup); consumed by L8B, not a pipeline stage. |
| L9 | WAZN_MATCHING | Wazn/pattern matching (وزن صرفي). |
| L10 | SYNTAX | Shallow syntax (e.g. isnadi links). |
| L10B | DEEP_SYNTAX | Deep dependency graph: nodes, edges, harf_jar, idafa, passive→naib_faʾil, valency-aware alignment, weak idafa suppression. |
| L11 | I3RAB | Textual iʿrāb (نصي). |
| L11B | CAUSAL_I3RAB | Causal iʿrāb reasoning: role, governing_factor, case/mood, marker; passive-aware; idafa guard. |
| L12 | SEMANTIC_RHETORICAL | Sentence classification, rhetoric signals. |
| L12B | ANALOGICAL_REASONING | Analogical inferences, ambiguity resolutions, discourse hints (e.g. connectives). |
| L13 | COGNITIVE_FUSION | Fusion arbitration over token states and evidence. |
| L13 | VALIDATION | Validation engine: global_validity, issues, final_confidence. |
| L14 | PRESENTATION | Rendered output, sections, evidence_trace, profiling. |

After L11B, the orchestrator runs **SEMANTIC_ROLE_PROJECTION** (additive only): performs heuristic semantic role projection based on resolved syntactic functions and seed valency frames; this layer does not implement full semantic event reasoning. It stores result under `layer_outputs["SEMANTIC_ROLE_PROJECTION"]`. This projection layer is non-blocking and confidence-agnostic; it enriches interpretation without modifying syntactic, valency, or iʿrāb decisions.

---

## 4. CURRENT ARCHITECTURE SNAPSHOT

**Implemented in code (factual):**

- Real orchestrator: `src/orchestrator/pipeline_orchestrator.py`; runs STAGE_ORDER via stage registry.
- Root extraction (L8), wazn matching (L9), basic word typing (L5).
- Shallow syntax (L10), deep syntax (L10B) with dependency_nodes, dependency_edges, clause_units.
- Textual iʿrāb (L11), causal iʿrāb (L11B) with token_i3rab_reasoning, i3rab_summary.
- Sentence classification (L12), analogical reasoning (L12B).
- Validation engine (L13_VALIDATION), cognitive fusion (L13_COGNITIVE_FUSION).
- Explainability: `build_evidence_trace()` in explainability.py; evidence_trace in rendered_output.
- Profiling: per-stage timing, total_time_ms.
- Tests: `tests/orchestrator/` (contract, stages, L8B, L10B, L11B, valency, connectives, semantic_role_projection, etc.).
- CI: GitHub Actions (tests, coverage, quality gates).
- Passive-aware tightening: L10B/L11B use L8B passive evidence; naib_faʾil edges; idafa guard.
- Weak idafa suppression: L10B downgrades idafa when mudaf follows passive verb; L11B prefers نائب فاعل over مضاف إليه when upstream passive exists.
- Connectives shared layer: `src/orchestrator/connectives/`; loaded from data/connectives_api/; used by L4, L10B, L12B as hints.
- Valency seed layer: `src/orchestrator/valency/` + `data/valency_seed.json`; L8B enriches profiles with valency_class, valency_required_roles, etc.
- Semantic role projection: `src/orchestrator/semantic_roles/`; runs after L11B; writes SEMANTIC_ROLE_PROJECTION (semantic_roles, projection_coverage). This projection layer is non-blocking and confidence-agnostic; it enriches interpretation without modifying syntactic, valency, or iʿrāb decisions.
- SECTION 3 legacy marking when causal iʿrāb is strong; SECTION 6 final_confidence rendering with syntax/iʿrāb unresolved penalty and realism_note.

---

## 5. ACTIVE EXPERIMENTAL LAYERS

**Currently active / recently introduced (additive only):**

- **Connectives knowledge layer** — Loader/lookup from connectives_api JSON; L4/L10B/L12B consume as hints; explainability reports connective recognition.
- **Valency matrix seed** — data/valency_seed.json; L8B profiles get valency_class, valency_required_roles; L10B uses for alignment.
- **Passive-aware wiring** — L8B voice/expected_subject_role; L10B naib_faʾil edges and L10 subject→naib_faʾil remap; L11B Rule A0 and Rule B L8B check; idafa guard in L11B.
- **Weak idafa suppression** — L10B: no idafa from L8B verb; no idafa to token already naib_faʾil; downgrade idafa when mudaf follows passive verb.
- **Semantic role projection** — Implemented (experimental heuristic layer). Runs after L11B; projects PATIENT, AGENT, GOAL, SOURCE, LOCATION, INSTRUMENT, STATE from syntactic roles and valency; SECTION 4d in presentation and analyze_sentence. PP roles (إلى، من، في، بـ، على) use **operator catalog** via `operators_semantics` loader (enriched CSV); "على" does not default to LOCATION (e.g. "على الله" → GOAL or unprojected). This projection layer is non-blocking and confidence-agnostic; it enriches interpretation without modifying syntactic, valency, or iʿrāb decisions.
- **Discourse frame builder** — Additive layer after L12B; builds frames from connectives (via shared layer), L10B clause hints, L12B discourse inferences. Conditional/adversative/explanation vs causation/negation with tightened confidence (strong only with clause/discourse support); scope_hint (token-local, phrase-level, clause-level, sentence-level); weak-frame limitation strings. SECTION 4e in presentation and analyze_sentence; explainability reflects evidence quality. Does not override syntax or iʿrāb. See `docs/discourse_frame_builder.md`.

---

## 6. VALIDATION PHILOSOPHY

- The system is a **deterministic layered reasoning engine**, not a statistical parser.
- **Confidence** is structurally grounded: weighted by parse strength, governance alignment, and unresolved counts; SECTION 6 applies a display penalty for syntax_unresolved and i3rab_unresolved.
- **Validity** is logical stage consistency (required keys, status values, no schema violations). It does not assert linguistic correctness of the sentence.
- Validation does not block on single-stage failure; partial results are allowed.

---

## 7. AGENT OPERATING RULES

1. **Read this file** (`docs/architecture/PIPELINE_MASTER_MEMORY.md`) before any major change to orchestration, stages, or linguistic behavior.
2. **Update the Change Log** (Section 8) after any meaningful architectural or linguistic modification (new stage, new enrichment layer, tightening pass, validation/confidence logic change). Use `scripts/update_architecture_log.py --target architecture --components "..." --intent "..." --risk low|medium|high` to append entries.
3. **Do not introduce** a new numbered pipeline stage or major reasoning pass without documenting intention first (e.g. in this file or in docs/research/FVAFK_MASTER_EVOLUTION.md).
4. Keep documentation **factual and technical**; no marketing or speculative hype.
5. **Documentation update is part of task completion.** Every non-trivial implementation task is **INCOMPLETE** unless documentation status is checked and reported. Treat documentation maintenance as a **required completion criterion**, not an optional follow-up.
6. **Required post-task check.** At the end of every meaningful implementation, refactor, tightening pass, additive layer, validation change, semantic change, or architectural change, the final report MUST include this exact section:
   ```
   Documentation update check:
   - PIPELINE_MASTER_MEMORY.md: updated / not updated
   - FVAFK_MASTER_EVOLUTION.md: updated / not updated
   - SCIENTIFIC_NEXT_PHASES.md: updated / not updated
   - update_architecture_log.py executed: yes / no
   - exact log entry added: ...
   - if any document was not updated, explain why
   ```
7. **When documents MUST be updated.** The relevant document(s) MUST be updated **in the same task** if the work affects:
   - **Architecture:** new additive layer, new stage, changed integration point, changed orchestration behavior, new loader/helper that changes architectural understanding.
   - **Scientific status:** feature moves planned→implemented or experimental→tightened/stabilized; major limitation removed or discovered.
   - **Roadmap / future plan:** priority or sequence changes; new phase introduced; previously planned feature no longer recommended.
   - **Active experimental layers:** new experimental layer; existing one significantly tightened; new dependency between layers.
   - **Documentation truthfulness:** current docs no longer match current code reality.
8. **Minimum expectations.** If architecture changed → update PIPELINE_MASTER_MEMORY.md and append architecture log entry. If scientific evolution/roadmap changed → update FVAFK_MASTER_EVOLUTION.md and append research log entry. If phase planning changed → update SCIENTIFIC_NEXT_PHASES.md.
9. **Failure condition.** If you implement meaningful code changes and do NOT (a) report documentation update status, OR (b) update the relevant documents when required, OR (c) explain why no update was needed, then the task must be treated as **NOT FULLY COMPLETE**.
10. **Logging rule.** When required, execute `python3 scripts/update_architecture_log.py --target architecture --components "..." --intent "..." --risk low|medium|high` and/or the research target. Always quote the exact entry intent in your report.
11. **Integrity.** Do not claim documents were updated unless they were actually updated. Do not update documents mechanically if nothing meaningful changed. But if the change is meaningful, documentation update is **mandatory**.

**Documentation consistency self-audit (mandatory after every non-trivial task):**

12. **Self-audit required.** Every meaningful implementation must include not only a documentation status report but also a **self-audit** comparing code reality against architectural memory. Goal: prevent silent divergence between current code and PIPELINE_MASTER_MEMORY.md, FVAFK_MASTER_EVOLUTION.md, SCIENTIFIC_NEXT_PHASES.md.
13. **Required self-audit section.** At the end of every meaningful task, the final report MUST include this exact section:
   ```
   Documentation consistency self-audit:
   - code reality reviewed against PIPELINE_MASTER_MEMORY.md: yes / no
   - code reality reviewed against FVAFK_MASTER_EVOLUTION.md: yes / no
   - code reality reviewed against SCIENTIFIC_NEXT_PHASES.md: yes / no
   - divergence detected: yes / no
   - if divergence detected, where: ...
   - action taken: updated docs / logged discrepancy / deferred with reason
   - authoritative source used: architecture memory / research plan / current code / investigated mismatch
   - update_architecture_log.py executed: yes / no
   - exact log entry added: ...
   ```
14. **What counts as divergence.** A divergence exists if: (1) code implements something docs still describe as planned; (2) docs describe as implemented what code does not contain; (3) docs describe stage order / integration points incorrectly; (4) docs omit an active experimental layer present in code; (5) docs describe an old limitation that was removed; (6) docs fail to mention a new architectural dependency; (7) roadmap priority no longer matches current direction; (8) an additive layer exists in code but is missing from memory docs; (9) code behavior materially changed but docs imply old behavior.
15. **Authoritative source rule.** If code and docs clearly match → report "no divergence". If they diverge → do NOT silently trust assumption; investigate; if code is intentional and correct, update docs; if docs are intended source of truth and code drifted, log discrepancy clearly. Default: architecture memory is authoritative for intended structure unless a newly implemented, verified code change has intentionally superseded it. Explicitly state which source you treated as authoritative.
16. **Required actions when divergence is found.** In the same task: (A) update the relevant docs immediately, OR (B) add a log entry documenting the mismatch and why it was not resolved now. Do NOT leave divergence unreported.
17. **Minimum checklist.** After each meaningful task, explicitly verify: (1) Did stage architecture change? (2) Did any additive layer appear/disappear? (3) Did any stage become tighter / more conservative / more experimental? (4) Did any feature move from planned → implemented? (5) Did presentation semantics change enough to require doc update? (6) Did roadmap priority change? (7) Did limitations change?
18. **Self-audit failure condition.** A task is NOT fully complete if: code changed meaningfully AND (no documentation consistency self-audit was reported OR a divergence existed and was not documented OR docs were claimed updated without actually checking consistency). **If self-audit was not performed, the task is considered INCOMPLETE regardless of code quality.**
19. **Recommended.** If practical, before the final report: inspect modified files; inspect the relevant doc sections; reason explicitly whether the docs still match reality. This is a reasoning requirement, not a blind file-touch.
20. **Self-audit integrity.** Do not invent divergence where none exists. Do not update documents mechanically. Do not claim consistency unless you actually checked it. This rule exists to make the project self-auditing and architecturally stable.

---

## 8. CHANGE LOG

| Date | Components | Change |
|------|------------|--------|
| (Initial) | — | PIPELINE_MASTER_MEMORY created; snapshot reflects L0–L14, L8B, valency seed, connectives, semantic role projection, passive-aware tightening, weak idafa suppression. |

| 2026-03-14 | SEMANTIC_ROLE_PROJECTION | documentation scientific tightening (heuristic clarification) (risk: low) |

| 2026-03-14 | SEMANTIC_ROLE_PROJECTION,operators_semantics | PP semantic role tightening via operator catalog; على no longer LOCATION default (risk: low) |

| 2026-03-15 | DISCOURSE_FRAME_BUILDER | discourse frame builder tightening: conditional/adversative/explanation vs causation, scope, weak-frame suppression (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | mandatory documentation check and same-task doc updates in agent operating rules (Section 7) (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | documentation update as task completion criterion; required post-task check; when/where to update; failure condition; logging rule (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | self-auditing documentation consistency check; mandatory self-audit section; divergence definition; authoritative source; actions when divergence found (risk: low) |

---

*End of PIPELINE_MASTER_MEMORY*
