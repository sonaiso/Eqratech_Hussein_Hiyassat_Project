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

Additive enrichment layers (no pipeline stage number): L8B verb bab governance, L8C valency seed, SEMANTIC_ROLE_PROJECTION, connectives knowledge. They run at defined points but do not extend the fixed STAGE_ORDER.

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

After L11B, the orchestrator runs **SEMANTIC_ROLE_PROJECTION** (additive only): maps syntactic roles and valency into abstract semantic roles (AGENT, PATIENT, GOAL, etc.) and stores result under `layer_outputs["SEMANTIC_ROLE_PROJECTION"]`.

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
- Semantic role projection: `src/orchestrator/semantic_roles/`; runs after L11B; writes SEMANTIC_ROLE_PROJECTION (semantic_roles, projection_coverage).
- SECTION 3 legacy marking when causal iʿrāb is strong; SECTION 6 final_confidence rendering with syntax/iʿrāb unresolved penalty and realism_note.

---

## 5. ACTIVE EXPERIMENTAL LAYERS

**Currently active / recently introduced (additive only):**

- **Connectives knowledge layer** — Loader/lookup from connectives_api JSON; L4/L10B/L12B consume as hints; explainability reports connective recognition.
- **Valency matrix seed** — data/valency_seed.json; L8B profiles get valency_class, valency_required_roles; L10B uses for alignment.
- **Passive-aware wiring** — L8B voice/expected_subject_role; L10B naib_faʾil edges and L10 subject→naib_faʾil remap; L11B Rule A0 and Rule B L8B check; idafa guard in L11B.
- **Weak idafa suppression** — L10B: no idafa from L8B verb; no idafa to token already naib_faʾil; downgrade idafa when mudaf follows passive verb.
- **Semantic role projection** — Implemented. Runs after L11B; projects PATIENT, AGENT, GOAL, SOURCE, LOCATION, INSTRUMENT, STATE from syntactic roles and valency; SECTION 4d in presentation and analyze_sentence.

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

---

## 8. CHANGE LOG

| Date | Components | Change |
|------|------------|--------|
| (Initial) | — | PIPELINE_MASTER_MEMORY created; snapshot reflects L0–L14, L8B, valency seed, connectives, semantic role projection, passive-aware tightening, weak idafa suppression. |

---

*End of PIPELINE_MASTER_MEMORY*
