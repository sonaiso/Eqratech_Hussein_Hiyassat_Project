# FVAFK MASTER EVOLUTION

**Scientific strategy and long-range evolution document.**  
Single reference for engineering state, achievements, and roadmap.

---

## A. PROJECT IDENTITY

FVAFK is evolving from an **Arabic Morphological Analyzer** into an **Arabic Linguistic Reasoning Engine**.

**Goals:**

- Reasoning-based grammar (dependency, causal iʿrāb, fusion).
- Semantic interpretation (structural semantic projection; future: deeper semantic roles).
- Structural iʿrāb derivation (governing factor, case/mood, marker from pipeline evidence).
- Cognitive linguistic modeling (fusion arbitration, explainability trace).

The system remains deterministic and rule-based.

---

## B. CURRENT ENGINEERING STATE

**Factual — implemented in code:**

- L0 → L14 layered pipeline with fixed STAGE_ORDER.
- Real orchestrator; FVAFK run once; adapters populate L1–L12.
- Root extraction (L8), wazn matching (L9), basic word typing (L5).
- Shallow syntax (L10), deep syntax (L10B) with dependency graph.
- Textual iʿrāb (L11), causal iʿrāb (L11B).
- Sentence classification (L12), analogical reasoning (L12B).
- Cognitive fusion (L13), validation (L13_VALIDATION), presentation (L14).
- Explainability trace; profiling; tests; CI.
- Additive layers: L8B verb bab governance, valency seed (L8C data), connectives layer, SEMANTIC_ROLE_PROJECTION, DISCOURSE_FRAME_BUILDER.
- Tightening: passive-aware wiring, valency-aware syntax, weak idafa suppression.

**Summary:**

- **Engineering structure:** strong.
- **Linguistic depth:** medium (morphology and dependency in place; full rule-based iʿrāb and semantic depth still to expand).

---

## C. ARCHITECTURAL ACHIEVEMENTS SO FAR

**Factual achievements only:**

- Passive voice detection and alignment (L8B voice, L10B naib_faʾil, L11B نائب فاعل prioritisation).
- Valency seed semantic layer (data/valency_seed.json, L8B enrichment, L10B alignment).
- Guarded deep syntax dependency edges (harf_jar, idafa, naib_faʾil, clause_units).
- Causal iʿrāb override/display logic (L11B role, governing_factor, case/mood; SECTION 3 legacy marking when causal is strong).
- Confidence realism penalty display (SECTION 6: syntax_unresolved, i3rab_unresolved, realism_note).
- Fusion arbitration engine (L13 cognitive fusion, pre-stage-13 audit, post-stage-13 audit).
- Explainability trace pipeline (evidence_trace from L4 through L13 and SEMANTIC_ROLE_PROJECTION).
- Tightening passes: passive-aware wiring; valency-aware syntax; weak idafa suppression (documented in docs/tightening_pass_passive_valency_idafa.md).
- Structural semantic role projection (SEMANTIC_ROLE_PROJECTION after L11B; SECTION 4d).
- Discourse frame builder (DISCOURSE_FRAME_BUILDER after L12B; SECTION 4e; conditional/adversative/explanation vs causation, scope, weak-frame tightening; see docs/discourse_frame_builder.md).

---

## D. NEW SCIENTIFIC MASTER PLAN

**Planned stages (from project roadmap). Not yet implemented unless stated.**

| Stage | Name | Purpose | Core features | Expected outputs | Why it matters |
|-------|------|---------|---------------|------------------|----------------|
| 12 | Gender & Number Engine | Tawkiir/ta’niith, ʿadad, agreement. | Gender, number, agreement_status, counted noun relation. | gender, number, number_type, agreement_status. | Needed for agreement and iʿrāb. |
| 13 | Verb Transformation Engine | Convert verb across tense/voice. | Past↔present, active↔passive, masdar. | base_past_form, present_form, imperative_form, passive_form. | Moves from analyzer to generator. |
| 14 | Jamid vs Mushtaq Engine | Derivational classification. | Jamid, mushtaq, ism faʿil, ism mafʿul, etc. | derivational_class, jamid_or_mushtaq. | Critical for iʿrāb and semantics. |
| 15 | Dependency Syntax Builder | Full dependency tree. | Head-dependent, subject-verb, idafa, jar-majrur, clause. | dependency_links, relation_type, clause_boundaries. | Core for rule-based iʿrāb. |
| 16 | Clause Engine | Subordinate and embedded clauses. | Condition, answer, ḥāl, sila, etc. | clause_type, clause_start/end, parent_clause. | Required for complex sentences. |
| 17 | Rule-Based Iʿrāb Reasoner | Iʿrāb from reasoning, not only text. | ʿāmil, function, case, marker, reasoning_steps. | governing_factor, i3rab_case_or_mood, reasoning_steps. | Replaces template-only iʿrāb. |
| 18 | Semantic Role Engine | Thematic/semantic roles (full). | Agent, patient, goal, instrument, etc. | semantic_role, event_structure. | Deep semantic interpretation. |
| 19 | Advanced Sentence Modes | Injunctive, interrogative, exclamatory, etc. | Order, prohibition, question, exclamation. | sentence_mode, mode_trigger. | Richer sentence classification. |
| 20 | Rhetorical Structures Engine | Structural rhetoric. | Tashbih, istiʿāra, kināya, majāz. | rhetorical_device, trigger_span. | Formal rhetoric layer. |
| 21 | Lexical Ontology Layer | Fixed lexical classes and behavior. | Sound nouns, ʾasmāʾ afʿāl, time/place adverbs. | lexical_class, fixed_behavior. | Stable behavior for special lemmas. |
| 22 | Gold Evaluation Framework | Benchmark against gold data. | Accuracy, precision, recall, F1. | accuracy, precision, recall, error_buckets. | Scientific evaluation. |
| 23 | Error Taxonomy Engine | Classify error types. | Root, wazn, iʿrāb, syntax error types. | error_type, source_stage, severity. | Interpret failures. |
| 24 | Research Reporting Layer | Publishable reports. | JSON/Markdown, benchmarks, stage tables. | Reports, comparison tables. | Reproducibility and reporting. |
| 25 | Optimization Strategy Layer | Post-evaluation optimization. | Caching, memoization, selective execution. | Performance and cost tuning. | After evaluation exists. |

---

## E. EXECUTION PRIORITY ORDER

**Priority 1:**  
Stage 12 (Gender & Number), Stage 14 (Jamid vs Mushtaq), Stage 15 (Dependency Syntax Builder), Stage 17 (Rule-Based Iʿrāb Reasoner).

**Priority 2:**  
Stage 13 (Verb Transformation), Stage 16 (Clause Engine), Stage 21 (Lexical Ontology), Stage 19 (Advanced Sentence Modes).

**Priority 3:**  
Stage 18 (Semantic Role Engine), Stage 20 (Rhetorical Structures), Stage 22 (Gold Evaluation), Stage 23 (Error Taxonomy), Stage 24 (Research Reporting), Stage 25 (Optimization Strategy).

---

## F. ENGINE EVOLUTION LOG

| Date | Change | Notes |
|------|--------|------|
| (Initial) | FVAFK_MASTER_EVOLUTION created | Snapshot and roadmap recorded; evolution log initialised. |
| 2026-03-15 | discourse frame builder additive layer (conditional/adversative/explanation, scope, weak-frame tightening) (risk: low) | DISCOURSE_FRAME_BUILDER |


---

## AUTO-UPDATE RULE

Whenever Cursor (or any agent/developer):

- creates a new pipeline stage or major enrichment layer
- modifies orchestration logic
- adds a projection or knowledge layer
- changes validation or confidence behaviour
- introduces new semantic or linguistic reasoning
- performs a tightening pass affecting linguistic behaviour

**it MUST append an entry to:**

- `docs/architecture/PIPELINE_MASTER_MEMORY.md` (Change Log, Section 8), and/or
- `docs/research/FVAFK_MASTER_EVOLUTION.md` (Engine Evolution Log, Section F),

and may use `scripts/update_architecture_log.py` to do so.

---

*End of FVAFK_MASTER_EVOLUTION*
