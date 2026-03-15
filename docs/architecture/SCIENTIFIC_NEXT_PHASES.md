# SCIENTIFIC NEXT PHASES

**Future phase tracker for the FVAFK Arabic Linguistic Reasoning Engine.**  
Organised by scientific hypothesis, required layers, risk, and expected capability.

---

## Phase Alpha — Syntax realism tightening

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Tighter dependency and role assignment (passive, valency, idafa) improves structural coherence and reduces false role leakage. |
| **Required layers** | L8B (passive, governance), L10B (naib_faʾil, valency alignment, weak idafa suppression), L11B (idafa guard, نائب فاعل prioritisation). |
| **Risk analysis** | Low–medium: additive changes; risk of over-suppressing valid idafa in edge cases. |
| **Expected emergence** | More realistic subject/object/naib_faʾil assignment; SECTION 4b/4c and confidence reflect structure. |

*Status: Implemented (tightening pass completed).*

---

## Phase Beta — Valency expansion

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Richer valency frames (required/optional roles, prepositions) improve attachment and role prediction. |
| **Required layers** | L8C valency seed expansion; L10B/L11B consumption of valency_required_roles, required_prepositions. |
| **Risk analysis** | Low: data-driven; risk of sparse coverage for rare roots. |
| **Expected emergence** | Better object/preposition expectations; fewer spurious attachments. |

*Status: Seed in place; expansion is incremental.*

---

## Phase Gamma — Semantic projection

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Mapping syntactic roles to abstract semantic roles (AGENT, PATIENT, GOAL, etc.) supports interpretation without full semantic inference. |
| **Required layers** | SEMANTIC_ROLE_PROJECTION (after L11B); deterministic rules from syntax + valency. |
| **Risk analysis** | Low: additive, no change to syntax/iʿrāb; over-attribution if rules too permissive. |
| **Expected emergence** | SECTION 4d semantic roles; explainability claims; basis for future semantic engine. |

*Status: Implemented.*

---

## Phase Delta — Discourse cognition

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Connectives and clause structure support discourse-level interpretation (condition, cause, contrast). |
| **Required layers** | Connectives layer (in place); DISCOURSE_FRAME_BUILDER (in place); L16 Clause Engine (planned); L12B discourse hints. |
| **Risk analysis** | Medium: clause boundaries and attachment are hard; connectives are hints only. |
| **Expected emergence** | Clause typing; connective-aware attachment; discourse coherence hints; SECTION 4e discourse frames. |

*Status: Connectives and DISCOURSE_FRAME_BUILDER in place; Clause Engine planned (Stage 16).*

---

## Phase Epsilon — Narrative reasoning

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Combined syntax, iʿrāb, semantics and rhetoric support narrative/argument structure. |
| **Required layers** | L15 Dependency Builder, L17 Rule-Based Iʿrāb, L18 Semantic Role Engine, L20 Rhetorical Structures. |
| **Risk analysis** | High: multiple new engines; integration and evaluation critical. |
| **Expected emergence** | End-to-end narrative-level analysis; explainable argument structure. |

*Status: Planned (Priority 1–3 in FVAFK_MASTER_EVOLUTION).*

---

## Phase Zeta — Arabic cognitive simulation

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Full pipeline (morphology → syntax → iʿrāb → semantics → rhetoric → evaluation) approximates a cognitive model of Arabic grammatical reasoning. |
| **Required layers** | L12–L25 (Gender/Number, Verb Transformation, Jamid/Mushtaq, Dependency, Clause, Iʿrāb Reasoner, Semantic Roles, Sentence Modes, Rhetoric, Lexical Ontology, Gold Eval, Error Taxonomy, Reporting, Optimization). |
| **Risk analysis** | High: long roadmap; depends on gold data and evaluation discipline. |
| **Expected emergence** | Reproducible, evaluable, explainable Arabic linguistic reasoning engine. |

*Status: Long-term roadmap; see FVAFK_MASTER_EVOLUTION.md.*

---

*End of SCIENTIFIC_NEXT_PHASES*
