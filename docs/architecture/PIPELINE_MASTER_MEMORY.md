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

**Execution order (Arabic, detailed):** see `docs/architecture/ORCHESTRATOR_EXECUTION_ORDER_AR.md` — distinguishes actual orchestrator execution vs scientific roadmap priority, lists `STAGE_ORDER`, additive layers, and naming collisions (e.g. two different “L12” / “L13” / “L14” stage ids).

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

Additive enrichment layers (no pipeline stage number; they do **not** extend the fixed STAGE_ORDER): L8B verb bab governance, L8C valency seed, SEMANTIC_ROLE_PROJECTION, connectives knowledge, DISCOURSE_FRAME_BUILDER, **ARABIC_WORD_STATE** (persistent per-token morphology map in `layer_outputs`, keyed by `token_id`; rebuilt after L9 from L2+L8+L9 with stem-aligned matching for و/ف/ال and plural/feminine suffix stripping; **`root` = canonical morphology root** after hollow-participle and similar patches; **`canonical_stem` / `canonical_root` / `canonical_wazn`** from `canonical_derivation` for display and L14; **`raw_l8_root` = L8 row root before correction** when L8 supplied a row; `root_correction_source` notes `hollow_ism_fail` / `hollow_ism_mafuul` when canonical ≠ raw L8; L14 merges derivational_class/jamid_or_mushtaq **and** re-syncs `root` from `token_classifications`; L12 patches gender_number; consumed by L14/L12/L17, **L14_PRESENTATION** (compact/detailed roots), **analyze_sentence** tables, and **Stage 15** same-root indexing; **JAMID gate:** no JAMID when `root_confirmed` or `wazn_confirmed` unless explicitly invalidated), **DEPENDENCY_SYNTAX_BUILDER (Stage 15 — implemented, Pass A + B + C + D + E: Pass E2/E3 strong-verb SUBJ/OBJ + ISM_FAIL OBJ with nominal-PRED supersession where applicable; multi-letter PP-prefix gate; SECTION 4f, ADDITIVE LAYERS, evidence_trace; root/APPOS/PP/clause-first/ambiguity discipline; transitive-object tightening with effective-verb filtering, clause-local OBJ, maf'ul mutlaq guard, duplicate-link suppression, explicit-coordination cleanup that suppresses residual APPOS/PRED overlap on conjunction-driven pairs, and narrow `INNA_NAME` governance support).** They run at defined points after their upstream stages.

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
| L14 | JAMID_MUSHTAQ | Jamid vs Mushtaq (derivational classification): ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, MUSHTAQ_LEXICAL, VERB, PARTICLE from L8/L9/L5/L8B + **ARABIC_WORD_STATE**; SECTION 4i. Consumes stem-aligned persistent root/wazn before JAMID fallback; **hard JAMID gate** when morphology confirms root or wazn (`jamid_blocked_confirmed_root_or_wazn` → MUSHTAQ_LEXICAL). Family-safe tightening: noun-family cues and strong-only L8B verb evidence gate VERB/MASDAR overreach; internal proclitic-aware normalization used for derivational checks. |
| L13 | VERB_TRANSFORMATION | Verb transformation engine (Pass 1): base past/present active, base past/present passive, masdar, imperative from L8 roots + L8B tense_mapping/bab/root_type + L14 VERB confirmation; output `L13_VERB_TRANSFORMATION`; SECTION 4l. Conservative fallbacks only; weak roots marked approximate; quadrilateral support deferred. |
| L12 | GENDER_NUMBER | Gender & Number Engine (Pass 1): token_features (gender, number, number_type, agreement_candidates, agreement_status, tamyiz_relation) from L2/L5/L9/L14/L8B; SECTION 4k; agreement unresolved until Stage 15 available. Tightening: proclitic-aware noun-family number checks prevent `...ين` forms from collapsing blindly to singular. |
| L10 | SYNTAX | Shallow syntax (e.g. isnadi links). |
| L10B | DEEP_SYNTAX | Deep dependency graph: nodes, edges, harf_jar, idafa, passive→naib_faʾil, valency-aware alignment, weak idafa suppression. |
| L11 | I3RAB | Textual iʿrāb (نصي). Legacy iʿrāb now respects grammatical family, passive voice, proper noun/jamid safety, and Stage 15 object/subject evidence: strong L8B/L5/Stage 15 routing (VERB/NOUN/PARTICLE), pre-template and post-generation validator, verb-safe templates, noun-safe templates, passive verb protection, proper noun safety, and direct-object preference over maf'ul mutlaq when Stage 15 resolves OBJ. |
| L11B | CAUSAL_I3RAB | Causal iʿrāb reasoning: role, governing_factor, case/mood, marker; passive-aware; idafa guard. |
| L17 | RULE_BASED_I3RAB | Rule-based iʿrāb reasoner (Stage 17): structured token_reasoning from Stage 15/16, L8B, L5, L4; does not replace L11B; high-confidence rules (فعل، فاعل، نائب فاعل، مفعول به، اسم مجرور). v2 consumes L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ for agreement-aware and derivational refinement (confidence/ambiguity, additive fields), plus narrow reference-driven support for `إنَّ` governance, accusative coordination inheritance, `ISM_FAIL` object-governance, and local late verbal-clause restoration. SECTION 4h. |
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
- Textual iʿrāb (L11), causal iʿrāb (L11B) with token_i3rab_reasoning, i3rab_summary. L11 legacy adapter now uses strong L8B + L5 + Stage 15 precedence to keep verbs verbal, nouns nominal, particles particle-family, and to prefer Stage 15 OBJ/NAIB_SUBJ/SUBJ over weak legacy fallbacks.
- Rule-based iʿrāb reasoner (L17): token_reasoning (syntactic_role, governing_factor, i3rab_case_or_mood, marker, reasoning_steps, clause_id) from Stage 15 links, Stage 16 clauses, L8B, L5, L4; L11B as supporting evidence only; SECTION 4h in report. **v2:** consumes L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ for agreement/derivational refinement (SIFA/SUBJ/NAIB agreement, JAMID/MASDAR safeguards, tamyiz relation); additive fields agreement_evidence, derivational_evidence, refinement_applied; ambiguity_log extended when conflict. **`ARABIC_WORD_STATE`:** `ensure_arabic_word_state` at build time; grammatical family and v2 refinement treat **MUSHTAQ_LEXICAL** as noun-family mushtaq; reasoning_steps note confirmed root/wazn when present. A narrow reference-driven post-pass now resolves high-confidence `إنَّ → اسم إن`, propagates accusative through explicit `COORD`, preserves explicit `إنَّ`-licensed coordination chains before any local `ISM_FAIL` governance, restricts participial object-governance to immediate supported local patterns with operator/preposition blockers, and restores clear late verbal clauses such as `أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً وَأَجْرًا عَظِيمًا` without spilling into unrelated conditional sentences. **Batch 2.1:** **B2.1-V1** prefers **نائب عن المفعول المطلق** for accusative `SIFA_MUSHABBAHA` / `SIGA_MUBALAGHAH` tokens immediately after a Stage 15 **OBJ** whose governor is L14 **ISM_FAIL/ISM_MAFUUL** (avoids generic نعت when L5/L11 paths disagree); **B2.1-V2** emits **`khabar_in_candidates`** when Stage 15 has **INNA_NAME** and Stage 16 **`verbal_clause_regions`** marks a **`verbal_embedded`** span, with per-token additive **`secondary_analysis.khabar_in_clause_candidate`** inside that span. **Batch 2.2:** structural gold-rule reinforcement **G007** (مفعول به) / **G010** (فاعل marfu) from Stage 15 **OBJ**/**SUBJ** when the head is a strong finite verb or L14 **ISM_FAIL/ISM_MAFUUL** (OBJ path), or **SUBJ** to a finite **active** verb (فاعل path); skips **اسم إن**; sets **`gold_rule_refs`** and confidence from link strength; no phrase lookup. **Batch 2.3:** **G016** (NAAT_AGREEMENT) — Stage 15 relation priority includes **SIFA**/**APPOS**/**PRED** after core verbal roles; initial **نعت** for **SIFA**; post-pass prefers **نعت** over **APPOS**/nominal **PRED** when L12 agreement is not conflicting, morphological case (tanween/diacritics) matches, and L14 marks the dependent as adjective-like (**SIFA_MUSHABBAHA**/**SIGA_MUBALAGHAH**/**ISM_FAIL**/**ISM_MAFUUL**); conservative **PRED→نعت** for double-accusative tails only with a non-nominal prefix before the head (avoids bare مبتدأ+خبر); **`gold_rule_refs`** may include **G016_NAAT_AGREEMENT**; no lexical sentence list. **Batch 2.4:** **G015** (HAL_MANSUB) — narrow **حال منصوب** when the token is accusative (tanwīn fatḥ/alif or plural **ـِينَ**), immediately follows a marfūʿ **فاعل**/**نائب فاعل** (surface ḍamma or resolved role), Stage 15 links **SUBJ**/**NAIB_SUBJ** from the governing verb to that subject, L14 shape is participial/adjective-like or plural **ينَ**, L12 does not conflict, and there is no **OBJ** from the same verb to this token; does not override strong **مفعول به**/**G007** or same-case **نعت**/**G016** on the subject; **`gold_rule_refs`** may include **G015_HAL_MANSUB**; no phrase lookup.
- **ARABIC_WORD_STATE** (additive, not a STAGE_ORDER id): `src/orchestrator/arabic_word_state.py`; `layer_outputs["ARABIC_WORD_STATE"]` holds `transformation_result.by_token_id` with monotonic fields (surface, normalized_surface, stem, **root** = canonical root for downstream consumers, **canonical_stem**, **canonical_root**, **canonical_wazn**, **wazn_inference_rule**, **raw_l8_root** = L8 extractor root before hollow/morphology override when present, **root_correction_source** (`hollow_ism_fail` / `hollow_ism_mafuul` when applicable), wazn_template, word_wazn, root_confirmed, wazn_confirmed, root_invalidated, wazn_invalidated, derivational_class, jamid_or_mushtaq, gender_number, syntax_roles, hollow_ism_fail, hollow_ism_mafuul). Canonical derivational fields are filled at rebuild via `canonical_derivation`. Orchestrator rebuilds after **L9**; **L14** merges classifications **and canonical root** from `token_classifications`; **L12** merges gender/number; **L17** reads for reasoning/evidence; **L14_PRESENTATION**, **analyze_sentence** root/wazn tables, and **Stage 15** `_roots8_by_index` read **canonical `root` / `canonical_*`**, not raw L8 alone.
- Jamid vs Mushtaq (L14_JAMID_MUSHTAQ): derivational classification after L9; token_classifications (derivational_class, jamid_or_mushtaq) from wazn patterns (ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, MUSHTAQ_LEXICAL, VERB, PARTICLE) using **stem-aligned** L8/L9 via ARABIC_WORD_STATE; SECTION 4i; for Stage 17 v2 consumption. **Hollow اسم فاعل (أجوف):** `hollow_ism_fail.py` corrects L8 roots that mis-read the hamza as the middle radical (e.g. ص-ي-م→ص-و-م) and applies **RULE 1H** (`hollow_ism_fail_lexicon` / `hollow_ism_fail_shape`) for `ISM_FAIL`+`MUSHTAQ` before ambiguous MASDAR/SIFA routing. **Hollow اسم مفعول (أجوف):** `hollow_ism_mafuul.py` corrects و/ي medial confusions (e.g. ق-ي-ل→ق-و-ل، ب-و-ع→ب-ي-ع) for stems `م`+C+و/ي+C after affix strip; **RULE 2H** (`hollow_ism_mafuul_lexicon` / `hollow_ism_mafuul_shape`) for `ISM_MAFUUL`+`MUSHTAQ` before MASDAR/SIFA. **JAMID gate:** confirmed root or wazn ⇒ never JAMID (MUSHTAQ_LEXICAL + MUSHTAQ). Family-safe tightening now blocks weak/candidate-only verb leakage into noun-family tokens, strips common proclitics internally for derivational checks, suppresses pattern-only MASDAR overreach on ambiguous nominal templates, and restores strong true-verb priority so resolved L8B verbs, L5 verbs, and narrow voice-confident finite-verb candidates are not overridden by noun-like derivational patterns.
- Verb Transformation (L13_VERB_TRANSFORMATION): real stage in `STAGE_ORDER` after `L14_JAMID_MUSHTAQ`, before `L12_GENDER_NUMBER`; derives base past/present active, base past/present passive, masdar, and imperative from L8 roots plus L8B tense_mapping/bab/root_type, gated by L14/L8B verb confirmation. Output is additive to downstream reasoning (`L12`, `L10B`, Stage 15, `L17`) and exposed in SECTION 4l in `analyze_sentence.py` and L14 presentation.
- Gender & Number (L12_GENDER_NUMBER): token_features (gender, number, number_type, agreement_candidates, agreement_status, tamyiz_relation) from L2/L5/L9/L14/L8B; SECTION 4k; Pass 1; agreement unresolved in pipeline order (L12 before Stage 15). Calls `ensure_arabic_word_state`; nominal-family cues recognize **MUSHTAQ_LEXICAL**; orchestrator merges token_features into ARABIC_WORD_STATE after L12. Family detection now ignores weak/candidate-only L8B verb profiles so noun/proper-name tokens such as `زَيْدٌ` keep safe nominal gender defaults, proclitic-aware suffix checks keep noun-family `...ين` forms plural/dual-aware instead of silently forcing `SINGULAR`, supported mushtaq-like noun-family `...ين` forms now prefer `PLURAL_SOUND_M` over `UNKNOWN`, and strong verb-family tokens stay on verb handling instead of falling into noun defaults such as `default_masculine_noun`.
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
- **DEPENDENCY_SYNTAX_BUILDER (Stage 15) implemented:** `src/orchestrator/dependency_syntax/`; runs after L10B; self-loop guard (no head_id == dependent_id); L10B resolved edges carried forward first; then Pass B/C/D/E (JAR_MAJRUR, PP_ATTACH, IDAFA, SIFA, COORD, COORD_CONJ, APPOS; candidate_markers). Simple active transitives now attach both SUBJ and OBJ when evidence is clear; Stage 15 filters weak L8B candidate profiles before treating a token as an effective verb, treats `name/proper_noun` as noun-like for core argument attachment, keeps OBJ inside the same clause, preserves passive-only NAIB_SUBJ behavior, blocks same-root masdar-like candidates from being forced into normal OBJ, recognizes attached coordination prefixes conservatively (so words like `فُرُوجَهُمْ` are not misread as attached conjunction forms), suppresses false APPOS leakage across coordinated nouns, suppresses contradictory `PRED`/`APPOS` overlap on explicit coordination pairs, and now emits `INNA_NAME` for high-confidence `إنَّ/أنَّ + noun-family` governance. **Pass E2/E3:** strong finite verbs get clause-local SUBJ/OBJ (clitic skip; APPOS pass skips strong verb tokens); `ISM_FAIL` + immediate noun can attach `OBJ` and **replaces** a same-pair nominal `nominal_mubtada_to_khabar` `PRED` when that pattern applies; PP-like detection for APPOS/E3 uses **multi-letter** harf clusters (`كال`, `في`, `من`, …) so lexical **ف**-initial nouns (e.g. فروج) are not treated as `في`. **Pass 5b (attached وَالـ):** `_is_explicit_waw_coord_conjunct_compatible` allows L14 participial classes (`ISM_FAIL`, `ISM_MAFUUL`, `SIFA_MUSHABBAHA`, `SIGA_MUBALAGHAH`) when L5 mis-tags the surface as `verb`, so long chains do not skip intermediate conjuncts. **Post–Pass C structural competition:** removes spurious `Pass_C_apposition_adjacent_nouns_gated` APPOS in late verbal tails when OBJ+و-second-conjunct, waw-conjunct+`SIFA_MUSHABBAHA`, or `ISM_FAIL` OBJ+`SIFA_MUSHABBAHA` explain the span; may emit compensating `SIFA` (`Pass_C_sifa_after_appos_suppression_waw_conjunct`); logged in `corrections_log`. Does not extend STAGE_ORDER; additive only.
- SECTION 3 legacy marking when causal iʿrāb is strong; SECTION 6 final_confidence rendering with syntax/iʿrāb unresolved penalty and realism_note.

---

## 5. ACTIVE EXPERIMENTAL LAYERS

**Currently active / recently introduced (additive only):**

- **Connectives knowledge layer** — Loader/lookup from connectives_api JSON; L4/L10B/L12B consume as hints; explainability reports connective recognition. Conservative connective guard: `إِنَّ` / `أَنَّ` and ambiguous bare `إن` / `أن` do not enter conditional lookup unless the token is explicitly the conditional `إِنْ`.
- **Valency matrix seed** — data/valency_seed.json; L8B profiles get valency_class, valency_required_roles; L10B uses for alignment.
- **Passive-aware wiring** — L8B voice/expected_subject_role; L10B naib_faʾil edges and L10 subject→naib_faʾil remap; L11B Rule A0 and Rule B L8B check; idafa guard in L11B.
- **Weak idafa suppression** — L10B: no idafa from L8B verb; no idafa to token already naib_faʾil; downgrade idafa when mudaf follows passive verb.
- **Semantic role projection** — Implemented (experimental heuristic layer). Runs after L11B; projects PATIENT, AGENT, GOAL, SOURCE, LOCATION, INSTRUMENT, STATE from syntactic roles and valency; SECTION 4d in presentation and analyze_sentence. PP roles (إلى، من، في، بـ، على) use **operator catalog** via `operators_semantics` loader (enriched CSV); "على" does not default to LOCATION (e.g. "على الله" → GOAL or unprojected). This projection layer is non-blocking and confidence-agnostic; it enriches interpretation without modifying syntactic, valency, or iʿrāb decisions.
- **Discourse frame builder** — Additive layer after L12B; builds frames from connectives (via shared layer), L10B clause hints, L12B discourse inferences. Conditional/adversative/explanation vs causation/negation with tightened confidence (strong only with clause/discourse support); scope_hint (token-local, phrase-level, clause-level, sentence-level); weak-frame limitation strings. `إِنَّ` / `أَنَّ` are now guarded from false conditional framing even if noisy upstream metadata marks them as conditional. SECTION 4e in presentation and analyze_sentence; explainability reflects evidence quality. Does not override syntax or iʿrāb. See `docs/discourse_frame_builder.md`.
- **Dependency syntax builder (Stage 15)** — Additive layer after L10B; self-loop guard; L10B resolved edges carried forward; then nominal/verbal, JAR_MAJRUR, PP_ATTACH, IDAFA, SIFA, COORD, COORD_CONJ, APPOS, `INNA_NAME`; ambiguity_log, corrections_log, candidate_markers. Output: dependency_links, root_resolution, ambiguity_log, corrections_log, coverage, candidate_markers. See `docs/dependency_syntax_builder.md`.
- **Clause Engine (Stage 16)** — In STAGE_ORDER; **Pass 1:** conditional decomposition (shart_particle, feil_shart, jawab_particle, jawab_shart); **Pass 2 (additive):** candidate `hal_clause`, `tamyiz_phrase` (عدد), `ism_mawsul` + `sila_mawsul`; top-level `hal_detected` / `tamyiz_detected` / `sila_detected`; clause_analysis, SECTION 4g (extended for Pass 2 detail). Tightened so `ACC_TAWKID` / `إنَّ` is not misread as conditional even when connective hints are noisy; `layer_outputs['CLAUSE_ENGINE']` now also exposes `transformation_result` for compatibility with wrapped-stage readers. When `INNA_NAME` is present in Stage 15 links and a **later** strong finite verb has both `SUBJ` and `OBJ`, **`verbal_clause_regions`** lists that span as `verbal_embedded` (خبر إن–style verbal tail for L17). See `docs/clause_engine.md`.
- **Verb Transformation (L13_VERB_TRANSFORMATION)** — In STAGE_ORDER after `L14_JAMID_MUSHTAQ`; deterministic verb paradigm generation from L8 roots + L8B tense_mapping/bab/root_type + L14 verb confirmation. Output: `verb_transformations`, `transformation_summary`, coverage `verb_transformation_pass1`; SECTION 4l in presentation and `analyze_sentence.py`. Pass 1 supports base active/passive, masdar, and imperative with conservative fallbacks.
- **Rule-Based Iʿrāb Reasoner (Stage 17)** — In STAGE_ORDER after L11B; consumes Stage 15 dependency links, Stage 16 clause IDs, L8B voice/governance, L5, L4; produces token_reasoning (syntactic_role, governing_factor, i3rab_case_or_mood, marker, reasoning_steps); does not overwrite L11B; SECTION 4h in report.
- **ARABIC_WORD_STATE (persistent morphology map)** — Additive `layer_outputs` entry (not a numbered stage): monotonic per-token state keyed by `token_id`; stem-aligned L8/L9 ingestion after L9; L14 and L12 patch downstream fields; JAMID forbidden when root or wazn is pipeline-confirmed; implementation `src/orchestrator/arabic_word_state.py`.

---

## 6. VALIDATION PHILOSOPHY

- The system is a **deterministic layered reasoning engine**, not a statistical parser.
- **Confidence** is structurally grounded: weighted by parse strength, governance alignment, and unresolved counts; SECTION 6 applies a display penalty for syntax_unresolved and i3rab_unresolved.
- **Validity** is logical stage consistency (required keys, status values, no schema violations). It does not assert linguistic correctness of the sentence.
- Validation does not block on single-stage failure; partial results are allowed.

---

## 7. AGENT OPERATING RULES

**Enforcement:** The project root contains **`.cursorrules`**, which instructs Cursor (and other agents) to update the three doc files on every major change and to report the documentation check. When giving implementation tasks, you can say e.g. "follow .cursorrules" or "update docs per PIPELINE_MASTER_MEMORY Section 7" to force doc updates.

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

**Documentation update policy (no automatic update):**  
The files `PIPELINE_MASTER_MEMORY.md`, `SCIENTIFIC_NEXT_PHASES.md`, and `docs/research/FVAFK_MASTER_EVOLUTION.md` are **not** updated automatically when code changes. They must be updated **as part of task completion** when a change affects architecture, scientific status, or roadmap (see Section 7). After any such task, the executor reports: PIPELINE_MASTER_MEMORY updated/not, FVAFK_MASTER_EVOLUTION updated/not, SCIENTIFIC_NEXT_PHASES updated/not, and why if not.

| Date | Components | Change |
|------|------------|--------|
| (Initial) | — | PIPELINE_MASTER_MEMORY created; snapshot reflects L0–L14, L8B, valency seed, connectives, semantic role projection, passive-aware tightening, weak idafa suppression. |

| 2026-03-14 | SEMANTIC_ROLE_PROJECTION | documentation scientific tightening (heuristic clarification) (risk: low) |

| 2026-03-14 | SEMANTIC_ROLE_PROJECTION,operators_semantics | PP semantic role tightening via operator catalog; على no longer LOCATION default (risk: low) |

| 2026-03-15 | DISCOURSE_FRAME_BUILDER | discourse frame builder tightening: conditional/adversative/explanation vs causation, scope, weak-frame suppression (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | mandatory documentation check and same-task doc updates in agent operating rules (Section 7) (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | documentation update as task completion criterion; required post-task check; when/where to update; failure condition; logging rule (risk: low) |

| 2026-03-15 | PIPELINE_MASTER_MEMORY | self-auditing documentation consistency check; mandatory self-audit section; divergence definition; authoritative source; actions when divergence found (risk: low) |

| 2026-03-15 | DEPENDENCY_SYNTAX_BUILDER | Stage 15 Pass A: schema, relation inventory, nominal/verbal builder; root_resolution only; integration after L10B (risk: low) |

| 2026-03-15 | DEPENDENCY_SYNTAX_BUILDER | Stage 15 Pass B: JAR_MAJRUR, PP_ATTACH, IDAFA (weak idafa suppression from L10B), SIFA (risk: low) |

| 2026-03-15 | DEPENDENCY_SYNTAX_BUILDER | Stage 15 Pass C: COORD, COORD_CONJ, APPOS, ambiguity_log discipline, candidate_markers (risk: low) |

| 2026-03-15 | DEPENDENCY_SYNTAX_BUILDER | Stage 15 Pass D: integration tests, full documentation, final self-audit; Stage 15 declared operational (risk: low) |

| 2026-03-15 | ARCHITECTURE | DEPENDENCY_SYNTAX_BUILDER removed from STAGE_ORDER; additive only. CLAUSE_ENGINE remains in STAGE_ORDER. SECTION 5 shows stages from STAGE_ORDER then ADDITIVE LAYERS (DSB, SRP, DFB). SECTION 4g — CLAUSE STRUCTURE added (conditional_structure_detected, clause_count, per-clause). (risk: low) |

| 2026-03-15 | CLAUSE_ENGINE | Stage 16 conditional decomposition: shart_particle, feil_shart, jawab_particle, jawab_shart from L4/L10B conditional particles and L8B verb; clause_analysis, ambiguity_log, limitations; SECTION 4g shows parent_clause_id. (risk: low) |

| 2026-03-15 | STAGE 15 + L10B + L11B | **Patch A:** Stage 15 self-loop guard (no link with head_id == dependent_id); L10B carry-forward (resolved edges mapped and added first; relation mapping naib_fa'il→NAIB_SUBJ, majrur→JAR_MAJRUR, idafa→IDAFA, fa'il→SUBJ, maf'ul_bih→OBJ). **Patch B:** L11B status normalization (normalize_i3rab_status: resolved/candidate/unresolved from role, factors, confidence ≥0.70/≥0.45). **Patch C:** L10B main_clause_type via _detect_main_clause_type (conditional → verbal → nominal fronted PP → nominal). **Patch D:** L11 legacy i3rab fixes in adapter: D2 مفعول به over مفعول مطلق when L10B object; D3 fronted PP رجل ≠ فاعل → مبتدأ مؤخر. (risk: low) |

| 2026-03-15 | DOCS | Documentation sync: PIPELINE_MASTER_MEMORY (Section 4, 5, 8), SCIENTIFIC_NEXT_PHASES (Phase Delta/Epsilon), FVAFK_MASTER_EVOLUTION (B, C, D, F) updated to reflect Stage 15 self-loop+carry-forward, Stage 16 Clause Engine implemented, L11B/L10B/L11 patches. (risk: none) |

| 2026-03-15 | PROJECT | Added `.cursorrules` in project root to force doc updates on major changes; CONTRIBUTING.md section "Documentation (required on major changes)" with table and pointer to Section 7; Section 7 now references .cursorrules. (risk: none) |

| 2026-03-15 | CLAUSE_ENGINE | Replaced clause_engine.py with real decomposition (Pass 1): L4 COND/JAZM → shart_particle, jawab_particle; _first_verb from L8B/L5 → feil_shart, jawab_shart; single conditional feil span limited to verb so jawab_shart = rest. SECTION 4g in analyze_sentence.py (compact.clause_engine); 8 tests with build_mock_lo_for. (risk: low) |

| 2026-03-15 | UI / analyze_sentence | When --no-report (UI mode), script prints full report (report_md) to stdout so the UI displays الجذور والأوزان، الإعراب، SECTION 4g، etc., not only SUMMARY. UI: assistant message scrollable (max-h 50vh), text-base for report. (risk: none) |

| 2026-03-01 | L11_I3RAB | **L11 CRITICAL FIX:** Verb tokens must never receive nominal iʿrāb labels. Added get_token_grammatical_family (L8B over L5, surface fallback), _i3rab_text_grammatical_family (normalized nominal/verbal detection), pre-template guardrail _apply_verb_nominal_guardrail, post-generation _validate_and_repair_verb_tokens, verb-safe templates (active/passive past). Tests: test_l11_verb_guardrail.py (alignment, family validator, mock guardrail). (risk: low) |

| 2026-03-17 | DEPENDENCY_SYNTAX_BUILDER | Stage 15 transitive object attachment tightening: effective verb filtering, name-as-noun support, clause-local OBJ, maf'ul mutlaq guard, duplicate-link suppression (risk: low) |

| 2026-03-17 | L11_I3RAB | Legacy i'rab family-role safety: strong L8B/L5/Stage15 precedence, passive verb protection, proper noun/jamid safety, and OBJ over maf'ul mutlaq fallback (risk: low) |

| 2026-03-01 | L17_RULE_BASED_I3RAB | Stage 17 Rule-Based Iʿrāb Reasoner (skeleton v1): new stage after L11B in STAGE_ORDER; token_reasoning from Stage 15 (SUBJ/OBJ/NAIB_SUBJ/JAR_MAJRUR), Stage 16 clause_id, L8B voice, L5 family; rules for فعل، فاعل، نائب فاعل، مفعول به، اسم مجرور; safe fallbacks; does not overwrite L11B; SECTION 4h in analyze_sentence; tests in test_stage17_rule_based_i3rab.py (risk: low) |

| 2026-03-01 | L14_JAMID_MUSHTAQ | Stage 14 Jamid vs Mushtaq Engine (Pass 1): derivational classification after L9; wazn-based rules for ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, VERB, PARTICLE; token_classifications + classification_summary + ambiguity_log; SECTION 4i in analyze_sentence and L14 presentation; tests test_stage14_jamid_mushtaq.py (risk: low) |

| 2026-03-17 | L12_GENDER_NUMBER | Stage 12 Gender & Number Engine Pass 1: token_features (gender, number, agreement_candidates, tamyiz_relation); SECTION 4k; agreement unresolved until Stage 15 available (risk: low) |

| 2026-03-17 | L17_RULE_BASED_I3RAB | Stage 17 v2: consume L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ for agreement-aware and derivational iʿrāb refinement; additive fields; V2-1–V2-9 rules (risk: low) |

| 2026-03-18 | DEPENDENCY_SYNTAX_BUILDER,L12_GENDER_NUMBER,CLAUSE_ENGINE | Tightening pass: attached coordination-prefix COORD support with APPOS suppression; L12 ignores weak L8B candidate profiles for noun/proper-name gender family safety; CLAUSE_ENGINE exposes transformation_result alias and does not treat ACC_TAWKID/inna as conditional (risk: low) |

| 2026-03-18 | L14_JAMID_MUSHTAQ,L12_GENDER_NUMBER,DISCOURSE_FRAME_BUILDER,connectives | Critical tightening batch: family-safe derivational classification blocks weak VERB/MASDAR overreach; noun-family ين forms use proclitic-aware plural/dual-safe number handling; إِنَّ/أَنَّ no longer emit conditional connective/discourse frames unless explicitly إِنْ (risk: low) |


| 2026-03-18 | L14_JAMID_MUSHTAQ,L12_GENDER_NUMBER,DEPENDENCY_SYNTAX_BUILDER | restoration batch: strong true-verb priority in L14/L12 and explicit coordination overlap cleanup in Stage 15 (risk: low) |

| 2026-03-18 | DEPENDENCY_SYNTAX_BUILDER,L17_RULE_BASED_I3RAB,L14_JAMID_MUSHTAQ | reference-driven governance batch: إنَّ support, accusative coordination inheritance, ISM_FAIL object-governance, and final verbal clause restoration (risk: low) |

| 2026-03-18 | L13_VERB_TRANSFORMATION,STAGE_ORDER,analyze_sentence,L14_PRESENTATION | Stage 13 Pass 1: verb transformation engine inserted after L14 with SECTION 4l and conservative base paradigm generation (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB,L12_GENDER_NUMBER | Constraint batch: preserve inna coordination chains, narrow ISM_FAIL/local restoration overreach, and strengthen supported noun-family ين plural handling (risk: low) |

| 2026-03-19 | ARABIC_WORD_STATE,L14_JAMID_MUSHTAQ,L12_GENDER_NUMBER,L17_RULE_BASED_I3RAB,pipeline_orchestrator | Persistent arabic_word_state: stem-aligned L8/L9 after L9; JAMID gate when root/wazn confirmed; MUSHTAQ_LEXICAL; L12/L17 consumption (risk: low) |

| 2026-03-19 | hollow_ism_fail,ARABIC_WORD_STATE,L14_JAMID_MUSHTAQ | Hollow active participle (اسم فاعل أجوف): lexicon root recovery vs surface hamza; L14 RULE 1H ISM_FAIL; state patch after L9 (risk: low) |

| 2026-03-19 | hollow_ism_mafuul,ARABIC_WORD_STATE,L14_JAMID_MUSHTAQ | Hollow passive participle (اسم مفعول أجوف): lexicon root recovery; L14 RULE 2H ISM_MAFUUL; state patch after L9 (risk: low) |

| 2026-03-19 | ARABIC_WORD_STATE,L14_PRESENTATION,DEPENDENCY_SYNTAX_BUILDER,hollow_ism_fail,hollow_ism_mafuul | Canonical hollow root propagation: raw_l8_root vs authoritative root; L14 merge + presentation + Stage15 _roots8_by_index read ARABIC_WORD_STATE (risk: low) |

| 2026-03-19 | ARABIC_WORD_STATE,canonical_derivation,DEPENDENCY_SYNTAX_BUILDER,L14_JAMID_MUSHTAQ,L17_RULE_BASED_I3RAB,analyze_sentence | Stage 15 core-link + canonical morphology: word-state canonical_stem/root/wazn and stem-based wazn recovery; ISM_FAIL immediate OBJ supersedes nominal mubtada→khabar PRED; PP-prefix detector uses multi-letter harf clusters (fixes فروج false skip); tests test_stage15_canonical_morphology_batch (risk: low) |

| 2026-03-19 | DOCS | Added `docs/architecture/ORCHESTRATOR_EXECUTION_ORDER_AR.md`: Arabic reference for actual orchestrator execution order vs roadmap priority; `STAGE_ORDER`, additive layers, tables; code pointers (`types.py`, `stage_registry.py`, `pipeline_orchestrator.py`) (risk: none) |

| 2026-03-19 | DOCS,data/i3rab_phrases.csv | Quran gold iʿrāb rule extraction plan: `scripts/analyze_gold_i3rab.py` (offline classification A–E); `docs/gold_i3rab_rules.md` (G-rules for future L17/L11B; no CSV lookup) (risk: none) |

| 2026-03-19 | ARABIC_WORD_STATE,canonical_derivation,DEPENDENCY_SYNTAX_BUILDER,L17_RULE_BASED_I3RAB | Stabilization: `canonical_root` synced on hollow patches; `_roots8_by_index` uses `canonical_root`; مُفْعِل lexicon for مسلم/مؤمن stem wazn; geminate L9 template cleanup (فَعَّ); Stage15 strip APPOS when head is strong verb/L14 VERB; L17 single definite subject after verb (risk: low) |

| 2026-03-21 | L17_RULE_BASED_I3RAB,quran_gold/loader | L17 V3: documented hal lexicon (جَمِيعًا), إنَّ+elative كُمْ pair (اسم/خبر), zarf zaman lexicon (لَيْلَةَ), هُوَ الله أَحَدٌ خبر مرشح (NFC-tolerant), جملة حالية after ظرف زمان; `orchestrator.quran_gold.loader` reads `data/quran_i3rab.csv` with utf-8-sig; tests use `lookup_i3rab` verification (risk: low) |

| 2026-03-22 | DEPENDENCY_SYNTAX_BUILDER | Batch 1.1: Pass E3 `ISM_FAIL` immediate object blocked when following token is finite verb (`L14:VERB` or strong L8B verb evidence); prevents OBJ spill (e.g. participle → `أَعَدَّ`); tests in test_stage15_canonical_morphology_batch (risk: low) |

| 2026-03-22 | DEPENDENCY_SYNTAX_BUILDER | Batch 1.2: Pass 5b `Pass_C_coordination_attached_prefix` resolves COORD head by left scan skipping participial `OBJ` dependents (`ISM_FAIL`/`ISM_MAFUUL`) and accusative intensifier tails (`كَثِيرًا`…); resumes chain after local object span (risk: low) |

| 2026-03-18 | DEPENDENCY_SYNTAX_BUILDER,CLAUSE_ENGINE | Batch 1.3–1.4: structural APPOS suppression in late verbal tails (`_strip_false_appos_structural_competition`: OBJ+و-second-conjunct under strong verb, waw-conjunct+`SIFA_MUSHABBAHA`, `ISM_FAIL` OBJ+`SIFA_MUSHABBAHA`); optional `SIFA` after suppression; `corrections_log` evidence; Stage 16 `verbal_clause_regions` for finite SUBJ+OBJ after `INNA_NAME` (risk: low) |

| 2026-03-22 | DEPENDENCY_SYNTAX_BUILDER | Batch 1.5: Pass 5b `_is_explicit_waw_coord_conjunct_compatible` — L14 participial/Sifa-mushabbaha tokens with `وَالـ` count as conjuncts when L5 says `verb`, fixing orphan gaps in long accusative chains (risk: low) |

| 2026-03-22 | L17_RULE_BASED_I3RAB | Batch 2.1: B2.1-V1 نائب عن المفعول المطلق after participial OBJ + L14 SIFA accusative; B2.1-V2 `khabar_in_candidates` + `secondary_analysis` from INNA_NAME + `verbal_clause_regions` (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB | Batch 2.2: G007/G010 from Stage15 SUBJ/OBJ + finite active verb or participial governor (`gold_rule_refs`); إن-chain اسم إن preserved; tests in test_stage17_rule_based_i3rab (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB | Batch 2.3: G016 NAAT_AGREEMENT — SIFA/APPOS/PRED handling + L12/case agreement; `gold_rule_refs` G016_NAAT_AGREEMENT; tests in test_stage17_rule_based_i3rab (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB | Batch 2.4: G015 HAL_MANSUB — حال after marfūʿ SUBJ/NAIB + verb; plural ـِينَ cue; respects OBJ/G007 and G016 نعت; tests in test_stage17_rule_based_i3rab (risk: low) |

| 2026-03-18 | analyze_sentence,tests/test_preferred_i3rab_integration | **Batch 2.5 (reporting/fusion/presentation):** preferred structured iʿrāb tiered precedence L17 resolved → L17 candidate → L11B resolved → L11B candidate → L11 text → unresolved; `build_preferred_i3rab` receives L11 legacy rows; compact adds `final_structured_i3rab_summary` (from L17 `reasoning_summary`), `khabar_in_candidates` passthrough; headline report uses L17 counts + labels L11B diagnostic; `render_report` exposes خبر إن مرشحات; confidence/judgement/`ما وجده` gated so stale L11B-only unresolved does not dominate when L17 is complete; tests `test_batch_25_*` (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB | **Batch 2.6:** B2.6-J1 **G026_JAR_TAALLUQ_VERB** — fused لَـ/بِ + ضمير between strong finite verb and Stage15 OBJ (`_verb_has_obj_after_token_index`); optional **CLAUSE_ENGINE** `verbal_embedded` + head match → higher confidence; `syntactic_role` **شبه جملة متعلّقة بالفعل**, `secondary_analysis.b26_taalluq`; blocklist for لكن/لعل… (no CSV); does not override G007/G010/G015/G016; tests `test_batch_26_*` (risk: low) |

| 2026-03-18 | L17_RULE_BASED_I3RAB,analyze_sentence | **Batch 2.7:** **B2.7-K1_resolve_khabar_in_verbal_clause** — clause-level `khabar_in_analysis` (جملة فعلية في محل رفع خبر إن) when `khabar_in_candidates` + INNA_NAME + `verbal_embedded` + resolved فعل/SUBJ/complement; token `syntactic_role` unchanged; `secondary_analysis` uses `khabar_in_clause_resolution_rule` (does not overwrite B2.1 `khabar_in_rule`); report: محسوم vs مرشحات; tests `test_batch_27_*` (risk: low) |

| 2026-03-21 | L13_VERB_TRANSFORMATION,tests | Stage 13 verb transformation: prerequisite verified; Quranic mock tests 11-14 added (risk: low) |

| 2026-03-21 | analyze_sentence,Batch_2.8_report | Presentation cleanup: L17-first report, appendix L11/L11B, single headline confidence, no duplicate L17 blocks (risk: low) |

| 2026-03-21 | CLAUSE_ENGINE,analyze_sentence,L14_PRESENTATION,docs/clause_engine.md | Stage 16 **Pass 2**: additive hal (جملة حالية), tamyiz عدد, sila (اسم موصول + صلة); flags; SECTION 4g extended; tests `test_clause_engine_pass2.py` (risk: low) |

---

*End of PIPELINE_MASTER_MEMORY*
