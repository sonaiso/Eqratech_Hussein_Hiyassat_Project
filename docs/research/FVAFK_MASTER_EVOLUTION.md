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
- Additive layers: L8B verb bab governance, valency seed (L8C data), connectives layer, SEMANTIC_ROLE_PROJECTION, DISCOURSE_FRAME_BUILDER, DEPENDENCY_SYNTAX_BUILDER (Stage 15: self-loop guard, L10B carry-forward, Pass B/C/D/E, effective-verb filtering for core verbal arguments, clause-local OBJ, maf'ul mutlaq guard, explicit-coordination overlap cleanup for APPOS/PRED vs COORD, narrow `INNA_NAME` support, stricter attached-prefix coordination detection, **Pass E2/E3** strong-verb SUBJ/OBJ and `ISM_FAIL` immediate OBJ that can supersede nominal mubtada→khabar `PRED`, **multi-letter PP-prefix** gating so lexical ف-initial nouns are not treated as `في`, and **post–Pass C structural competition** stripping false adjacent-noun APPOS in late verbal tails in favor of OBJ+coordination, `ISM_FAIL`+صيغة صفتية, or waw-conjunct+نعت). CLAUSE_ENGINE in STAGE_ORDER (Stage 16: conditional decomposition; SECTION 4g; **`verbal_clause_regions`** for embedded finite tails after `INNA_NAME`). **L14_JAMID_MUSHTAQ** in STAGE_ORDER after L9: derivational classification (ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, VERB, PARTICLE); SECTION 4i; family-safe tightening now blocks weak verb/MASDAR overreach, uses proclitic-aware internal normalization, and restores strong true-verb priority when real verbal evidence exists. **L13_VERB_TRANSFORMATION** in STAGE_ORDER after `L14_JAMID_MUSHTAQ`: base past/present active, past/present passive, masdar, and imperative from L8 roots + L8B tense mapping/bab/root type + L14 verb confirmation; SECTION 4l; conservative weak-root and quadrilateral fallbacks. **L12_GENDER_NUMBER** in STAGE_ORDER after `L13_VERB_TRANSFORMATION`: gender, number, number_type, agreement_candidates, agreement_status, tamyiz_relation; SECTION 4k; Pass 1; noun-family `...ين` forms are now handled with plural/dual-aware caution rather than blind singular fallback, supported mushtaq-like `...ين` noun-family forms now prefer `PLURAL_SOUND_M` over `UNKNOWN`, and genuine verbs stay on the verb-family path instead of noun defaults. **L17 Rule-Based Iʿrāb Reasoner** in STAGE_ORDER after L11B: token_reasoning from Stage 15/16, L8B, L5, L4; does not replace L11B; SECTION 4h. The targeted reference pass is now constrained so explicit `إنَّ` coordination chains remain accusative conjunct chains, `ISM_FAIL` governance only fires in immediate supported local patterns with blockers, and local strong-verb restoration no longer overreaches into unrelated conditional sentences. **Batch 2.2** adds structural **G007** (مفعول به) / **G010** (فاعل) reinforcement from Stage 15 **OBJ**/**SUBJ** when governors are structurally licensed (finite active verb or participial **ISM_FAIL/ISM_MAFUUL** for OBJ), with **`gold_rule_refs`** and without phrase lookup. **Batch 2.3** adds **G016** (نعت agreement): Stage 15 **SIFA** in relation priority, **APPOS**/**PRED** upgrades when L12 and tanween/case cues align with L14 adjective-like dependents. **Batch 2.4** adds **G015** (حال منصوب): accusative circumstantial after marfūʿ **SUBJ**/**NAIB_SUBJ**, with OBJ/G007 and G016 نعت safeguards; plural **ـِينَ** morph cue.
- Tightening: passive-aware wiring, valency-aware syntax, weak idafa suppression; L11B status normalization (resolved/candidate/unresolved); L10B main_clause_type (conditional → verbal → nominal); L11 legacy i3rab fixes (مفعول به over مفعول مطلق, fronted PP مبتدأ مؤخر). **L11 CRITICAL FIX:** legacy iʿrāb now respects grammatical family, passive voice, proper noun/jamid safety, and Stage 15 core roles: strong L8B/L5/Stage 15 precedence, pre-template and post-generation validators, verb-safe and noun-safe fallbacks, passive verb protection, and direct-object preference over maf'ul mutlaq when Stage 15 resolves OBJ.

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
- Discourse frame builder (DISCOURSE_FRAME_BUILDER after L12B; SECTION 4e; conditional/adversative/explanation vs causation, scope, weak-frame tightening; see docs/discourse_frame_builder.md). Shared connective lookup now treats `إِنَّ` / `أَنَّ` conservatively as non-conditional unless the token is explicitly the conditional `إِنْ`, preventing false conditional discourse frames.
- Dependency syntax builder (Stage 15, additive: self-loop guard, L10B carry-forward, Pass B–E; dependency_links, root_resolution, JAR_MAJRUR, PP_ATTACH, IDAFA, SIFA, COORD, COORD_CONJ, APPOS, `INNA_NAME`; SECTION 4f, ADDITIVE LAYERS, evidence_trace; docs/dependency_syntax_builder.md). Simple active transitives now attach direct objects more reliably: weak L8B candidate profiles no longer hide noun arguments, proper names are treated as noun-like, object attachment stays inside the clause, passive clauses keep NAIB_SUBJ, same-root masdar-like nouns are not forced into OBJ, attached coordination prefixes such as `وَالـ` map to COORD instead of leaking into APPOS, words such as `فُرُوجَهُمْ` are no longer misread as attached coordinators, explicit coordination pairs suppress residual `APPOS`/`PRED` overlap, and high-confidence `إنَّ/أنَّ + noun-family` sequences now get explicit governance support.
- Clause Engine (Stage 16, in STAGE_ORDER: conditional decomposition — shart_particle, feil_shart, jawab_particle, jawab_shart; clause_analysis, SECTION 4g). Tightened so emphasis operators such as `إنَّ` (`ACC_TAWKID`) are not treated as conditional from connective hints alone; pipeline output now also exposes `transformation_result` for schema-compatible readers.
- **ARABIC_WORD_STATE** (additive morphology accumulator in `layer_outputs`, not a stage id): rebuilt after L9 with stem-aligned L8/L9 matching (و/ف/ال and plural/feminine suffix stripping); **`root` is canonical** after hollow-participle (and similar) morphology patches, with **`raw_l8_root`** preserving the pre-correction L8 value for transparency; **`canonical_root`** is explicitly set together with **`root`** when hollow/mafʿūl patches apply; additive **`canonical_stem` / `canonical_root` / `canonical_wazn`** (plus `wazn_inference_rule`) come from `canonical_derivation` for downstream display and L14 gating (including **مُفْعِل** for lexicon stems such as مسلم/مؤمن when L9 wazn is missing on long surfaces); L14 merges derivational_class/jamid_or_mushtaq **and** syncs `root` from classifications; L12 merges gender_number; L17 consumes for evidence; **L14 presentation**, **analyze_sentence tables**, and **Stage 15** `_roots8_by_index` consume **`canonical_root` or `root`**, not raw L8 rows alone; **JAMID gate** blocks JAMID when root or wazn is confirmed (`MUSHTAQ_LEXICAL` fallback). **Stage 15** strips spurious **APPOS** edges whose head is a strong finite verb or L14 **VERB**, so verbal clauses are not nominalized as badal/apposition. See `src/orchestrator/arabic_word_state.py`.
- Jamid vs Mushtaq (L14_JAMID_MUSHTAQ, in STAGE_ORDER after L9: token_classifications with derivational_class and jamid_or_mushtaq from wazn patterns; SECTION 4i; for Stage 17 v2). Consumes persistent word state for morphology; stem-aligned layer rows attach to surface-divergent tokens (e.g. وَالْمُؤْمِنِينَ vs الْمُؤْمِنِينَ). **Hollow active participle (اسم الفاعل الأجوف):** `hollow_ism_fail.py` + ARABIC_WORD_STATE patch wrong triliteral roots from surface hamza (e.g. صائم→ص-و-م not ص-ي-م); L14 RULE 1H forces ISM_FAIL+MUSHTAQ for documented/شكل فَائِل candidates ahead of MASDAR/SIFA overlap. **Hollow passive participle (اسم المفعول الأجوف):** `hollow_ism_mafuul.py` + state patch for مقول/مبيع/مخوف-type stems (ق-و-ل، ب-ي-ع، خ-و-ف); L14 RULE 2H forces ISM_MAFUUL+MUSHTAQ ahead of ambiguous nominal patterns. Family-safe tightening now uses strong-family evidence before pattern selection, strips common nominal proclitics internally, avoids pattern-only MASDAR/VERB overreach on noun-family tokens such as `الْمُسْلِمِينَ`, `وَالْمُتَصَدِّقِينَ`, and `أَحَداً`, and restores VERB for genuine verbs such as `ظَلَمَ`, `أَعَدَّ`, and `ضُرِبَ` when strong verbal evidence is present.
- Rule-Based Iʿrāb Reasoner (Stage 17, in STAGE_ORDER after L11B: token_reasoning with syntactic_role, governing_factor, i3rab_case_or_mood, marker, reasoning_steps, clause_id; evidence from Stage 15 links, Stage 16 clauses, L8B, L5, L4; L11B as support only; high-confidence rules for فعل، فاعل، نائب فاعل، مفعول به، اسم مجرور; SECTION 4h). **v2:** consumes L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ for agreement-aware and derivational refinement (SIFA/SUBJ/NAIB agreement, JAMID/MASDAR safeguards, tamyiz relation); also reads **ARABIC_WORD_STATE** for confirmed morphology notes and treats **MUSHTAQ_LEXICAL** as mushtaq noun-family; additive fields agreement_evidence, derivational_evidence, refinement_applied; see docs/stage17_rule_based_i3rab_v2.md. A narrow reference-driven post-pass now upgrades `إِنَّ` to emphatic governance, resolves `اسم إن` and accusative conjuncts, preserves explicit `إنَّ` coordination chains before any local noun-governor reanalysis, allows `ISM_FAIL` governors to license object readings only in immediate supported local patterns without forcing verbhood, supports a targeted `نائب عن المفعول المطلق` note after `ISM_FAIL + object + intensifier`, blocks unsupported noun-governor/prepositional overreach, and restores final verbal clauses like `أَعَدَّ اللَّهُ ...` locally when strong evidence exists. **Batch 2.2** reinforces **G007**/**G010** from Stage 15 structural **OBJ**/**SUBJ** (skips `اسم إن`; passive verbs do not license **G010** فاعل on dependents). **Batch 2.3** reinforces **G016** — prefer **نعت** when Stage 15 **SIFA** or agreement-strong **APPOS**/**PRED** pairs license it over badal/khabar readings (L12 + morphological case; L14 adjective-like class). **Batch 2.4** adds **G015** **حال منصوب** when accusative hal follows marfūʿ subject per Stage 15 **SUBJ**/**NAIB_SUBJ**, with OBJ/نعت safeguards.
- Verb Transformation Engine (Stage 13, in STAGE_ORDER after `L14_JAMID_MUSHTAQ`: `L13_VERB_TRANSFORMATION` with `verb_transformations`, `transformation_summary`, coverage `verb_transformation_pass1`; SECTION 4l). Pass 1 derives base active/passive, masdar, and imperative from L8 roots and L8B tense mapping/bab/root type, while keeping conservative fallbacks for unknown bab, weak roots, and unsupported quadrilaterals.
- L11B status normalization (normalize_i3rab_status: resolved/candidate/unresolved); L10B main_clause_type detection (conditional → verbal → nominal); L11 adapter legacy fixes (مفعول به vs مفعول مطلق, fronted PP مبتدأ مؤخر). **L11 family/role safety:** grammatical-family validation (VERB/NOUN/PARTICLE from strong L8B, then L5, then Stage 15/L10B hints); nominal iʿrāb never applied to verbs; noun rows no longer inherit verbal text; passive verbs stay verbal while noun dependents become نائب فاعل; proper nouns/jamid nouns are not forced into unsafe مبني fallbacks; Stage 15 OBJ keeps noun rows in direct-object interpretation instead of weak maf'ul mutlaq fallbacks. L12 now follows the same strong-profile discipline, so weak/candidate-only L8B matches do not flip noun/proper-name gender classification into verb-family UNKNOWN, strong verb-family tokens do not fall into `default_masculine_noun`, and proclitic-aware suffix checks prevent noun-family `...ين` forms from collapsing to false singular defaults.

---

## D. NEW SCIENTIFIC MASTER PLAN

**Planned stages (from project roadmap). Not yet implemented unless stated.**

| Stage | Name | Purpose | Core features | Expected outputs | Why it matters |
|-------|------|---------|---------------|------------------|----------------|
| 12 | Gender & Number Engine | Tawkiir/ta’niith, ʿadad, agreement. | Gender, number, agreement_status, counted noun relation. | gender, number, number_type, agreement_status. | Needed for agreement and iʿrāb. |
| 13 | Verb Transformation Engine | Convert verb across tense/voice. | Past↔present, active↔passive, masdar, imperative. | `L13_VERB_TRANSFORMATION`: base_past_active, base_present_active, base_past_passive, base_present_passive, masdar, imperative. | **Implemented (Pass 1).** SECTION 4l; see docs/stage13_verb_transformation.md. |
| 14 | Jamid vs Mushtaq Engine | Derivational classification. | ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, VERB, PARTICLE from L8/L9/L5/L8B. | token_classifications, classification_summary, ambiguity_log. | **Implemented (Pass 1).** SECTION 4i. See docs/stage14_jamid_mushtaq.md. |
| 15 | Dependency Syntax Builder | Full dependency tree. | Self-loop guard, L10B carry-forward; head-dependent, idafa, jar-majrur, coord, appos. | dependency_links, root_resolution, ambiguity_log, corrections_log, candidate_markers. | Core for rule-based iʿrāb. **Implemented (additive; Pass A self-loop+carry-forward, B/C/D/E).** See Section C and docs/dependency_syntax_builder.md. |
| 16 | Clause Engine | Clause decomposition (conditional, etc.). | Shart particle, feil shart, jawab particle, jawab shart; clause_analysis. | clause_analysis, conditional_structure_detected, SECTION 4g. | **Implemented (in STAGE_ORDER).** Conditional decomposition; parent_clause_id. |
| 17 | Rule-Based Iʿrāb Reasoner | Iʿrāb from reasoning, not only text. | Stage 15/16, L8B, L5, L4; v2: L12, L14; token_reasoning; does not replace L11B. | token_reasoning (syntactic_role, governing_factor, i3rab_case_or_mood, marker, reasoning_steps, clause_id), reasoning_summary; v2: agreement_evidence, derivational_evidence, refinement_applied. | **Implemented (v1 + v2).** SECTION 4h; docs/stage17_rule_based_i3rab_v2.md. |
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
Stage 16 (Clause Engine), Stage 21 (Lexical Ontology), Stage 19 (Advanced Sentence Modes).

**Priority 3:**  
Stage 18 (Semantic Role Engine), Stage 20 (Rhetorical Structures), Stage 22 (Gold Evaluation), Stage 23 (Error Taxonomy), Stage 24 (Research Reporting), Stage 25 (Optimization Strategy).

---

## F. ENGINE EVOLUTION LOG

| Date | Change | Notes |
|------|--------|------|
| (Initial) | FVAFK_MASTER_EVOLUTION created | Snapshot and roadmap recorded; evolution log initialised. |
| 2026-03-15 | discourse frame builder additive layer (conditional/adversative/explanation, scope, weak-frame tightening) (risk: low) | DISCOURSE_FRAME_BUILDER |

| 2026-03-01 | Stage 15 Pass B: JAR_MAJRUR, PP_ATTACH, IDAFA (weak idafa suppression from L10B), SIFA (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-01 | Stage 15 Pass C: COORD, COORD_CONJ, APPOS, ambiguity_log discipline, candidate_markers (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-15 | Stage 15 Pass B: JAR_MAJRUR, PP_ATTACH, IDAFA, SIFA (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-15 | Stage 15 Pass C: coordination, apposition, candidate_markers (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-15 | Stage 15 Pass D complete; readiness for Stage 16 and Stage 17 (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-15 | Stage 16 Clause Engine: conditional decomposition (shart_particle, feil_shart, jawab_particle, jawab_shart); clause_analysis; SECTION 4g (risk: low) | CLAUSE_ENGINE |

| 2026-03-15 | Structural quality patches: Stage 15 self-loop guard + L10B carry-forward; L11B status normalization; L10B main_clause_type (conditional→verbal→nominal); L11 legacy i3rab fixes (مفعول به, fronted PP) (risk: low) | STAGE_15, L10B, L11B, L11 adapter |

| 2026-03-15 | CLAUSE_ENGINE real decomposition: clause_engine.py replaced; L4 COND/JAZM + L8B/L5 verbs → shart_particle, feil_shart, jawab_particle, jawab_shart; single-conditional feil span = verb only; SECTION 4g in analyze_sentence; 8 tests (risk: low) | CLAUSE_ENGINE |

| 2026-03-01 | L11 CRITICAL FIX: verb tokens must never receive nominal iʿrāb labels. get_token_grammatical_family (L8B > L5, surface fallback), _i3rab_text_grammatical_family (normalized), _apply_verb_nominal_guardrail, _validate_and_repair_verb_tokens, verb-safe templates; tests/orchestrator/test_l11_verb_guardrail.py (risk: low) | L11_I3RAB |

| 2026-03-17 | Stage 15 transitive object attachment tightening: effective verb filtering, clause-local OBJ, passive protection, maf'ul mutlaq guard (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-17 | Legacy i'rab family-role safety: strong L8B/L5/Stage15 precedence, passive verb protection, proper noun/jamid safety, and OBJ over maf'ul mutlaq fallback (risk: low) | L11_I3RAB |

| 2026-03-01 | Stage 17 Rule-Based Iʿrāb Reasoner (skeleton v1): L17_RULE_BASED_I3RAB in STAGE_ORDER after L11B; token_reasoning from Stage 15 (SUBJ/OBJ/NAIB_SUBJ/JAR_MAJRUR), Stage 16 clause_id, L8B voice, L5; rules for فعل، فاعل، نائب فاعل، مفعول به، اسم مجرور; safe fallbacks; does not overwrite L11B; SECTION 4h; tests test_stage17_rule_based_i3rab.py (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-01 | Stage 14 Jamid vs Mushtaq Engine (Pass 1): L14_JAMID_MUSHTAQ in STAGE_ORDER after L9; wazn-based derivational classification (ISM_FAIL, ISM_MAFUUL, SIFA_MUSHABBAHA, MASDAR, SIGA_MUBALAGHAH, JAMID, VERB, PARTICLE); token_classifications, classification_summary, ambiguity_log; SECTION 4i; tests test_stage14_jamid_mushtaq.py (risk: low) | L14_JAMID_MUSHTAQ |

| 2026-03-17 | Stage 12 Gender & Number Engine Pass 1 (gender, number, tamyiz_relation; SECTION 4k) (risk: low) | L12_GENDER_NUMBER |

| 2026-03-17 | Stage 17 v2: consume L12 and L14 for agreement/derivational refinement; SIFA/SUBJ/NAIB agreement; JAMID/MASDAR safeguards; tamyiz relation (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Tightening pass: attached coordination prefixes, weak-L8B family safety in L12, and inna-safe clause detection/schema compatibility (risk: low) | DEPENDENCY_SYNTAX_BUILDER,L12_GENDER_NUMBER,CLAUSE_ENGINE |

| 2026-03-18 | Critical tightening batch: family-safe L14, noun-family plural-aware L12, and inna-safe connective/discourse correction (risk: low) | L14_JAMID_MUSHTAQ,L12_GENDER_NUMBER,DISCOURSE_FRAME_BUILDER,connectives |


| 2026-03-18 | restoration batch: strong true-verb priority in L14/L12 and explicit coordination overlap cleanup in Stage 15 (risk: low) | L14_JAMID_MUSHTAQ,L12_GENDER_NUMBER,DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-18 | reference-driven governance batch: إنَّ support, accusative coordination inheritance, ISM_FAIL object-governance, and final verbal clause restoration (risk: low) | DEPENDENCY_SYNTAX_BUILDER,L17_RULE_BASED_I3RAB,L14_JAMID_MUSHTAQ |

| 2026-03-18 | Stage 13 Verb Transformation implemented (Pass 1): base active/passive, masdar, imperative from root+bab evidence (risk: low) | L13_VERB_TRANSFORMATION |

| 2026-03-21 | Stage 13 Verb Transformation: prerequisite L8B/L14 probe documented; Quranic-surface mock tests 11–14 (`test_q11`–`test_q14`) in `test_stage13_verb_transformation.py` (risk: low) | L13_VERB_TRANSFORMATION, tests |

| 2026-03-18 | Constraint batch: reusable governance boundaries for inna chains, supported ISM_FAIL patterns, and mushtaq-like ين plural support (risk: low) | L17_RULE_BASED_I3RAB,L12_GENDER_NUMBER |

| 2026-03-19 | Morphology state persistence and JAMID gate (MUSHTAQ_LEXICAL) (risk: low) | ARABIC_WORD_STATE,L14,L17,L12 |

| 2026-03-19 | Hollow ISM_FAIL root correction and RULE 1H (risk: low) | hollow_ism_fail,L14 |

| 2026-03-19 | Hollow ISM_MAFUUL root correction and RULE 2H (risk: low) | hollow_ism_mafuul,L14 |

| 2026-03-19 | Hollow participle corrections surface as canonical root in word state, reports, and same-root guards (risk: low) | ARABIC_WORD_STATE,L14_PRESENTATION,DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-19 | Canonical derivational morphology propagation (hollow فاعل, geminate فعّل, mutafail) and participial/late-clause link restoration (risk: low) | ARABIC_WORD_STATE,Stage15,L14,L17,canonical_derivation |

| 2026-03-21 | Stabilization batch: canonical_root sync hollow/mafʿūl; stem مُفْعِل inference; APPOS strip for verbal heads; L17 definite single subject (risk: low) | ARABIC_WORD_STATE,Stage15,L17,canonical_derivation |

| 2026-03-21 | L17 V3 Quranic-aligned rules (حال lexicon, إنَّ+elative كُمْ, ظرف زمان lexicon, جملة حالية); `quran_gold.loader` for CSV verification in tests (risk: low) | L17,quran_gold |

| 2026-03-21 | L17 V3 Quranic rules + CSV loader for gold verification tests (risk: low) | L17_RULE_BASED_I3RAB,quran_gold |

| 2026-03-22 | Structural Batch 1.1: Stage 15 Pass E3 — no OBJ from ISM_FAIL to following finite verb (verbal clause boundary) (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-21 | Batch 1.1: Pass E3 ISM_FAIL object spill blocked for following finite verb (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-22 | Structural Batch 1.2: Stage 15 Pass 5b COORD head resumption after participial OBJ + intensifier span (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-21 | Batch 1.2: COORD resumption after participial object span (Pass 5b head scan) (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-18 | Structural Batch 1.3–1.4: Stage 15 false APPOS suppression in verbal tails + Stage 16 `verbal_clause_regions` after INNA_NAME (risk: low) | DEPENDENCY_SYNTAX_BUILDER,CLAUSE_ENGINE |

| 2026-03-22 | Structural Batch 1.5: Stage 15 Pass 5b L14-aware conjunct compatibility (L5 verb vs L14 ISM_FAIL in long وَالـ chains) (risk: low) | DEPENDENCY_SYNTAX_BUILDER |

| 2026-03-22 | Stage 17 Batch 2.1: quantitative naib al-maf'ul + verbal khabar-in packaging (`khabar_in_candidates`) (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Stage 17 Batch 2.2: structural G007 (مفعول به) / G010 (فاعل) from Stage15 OBJ/SUBJ + governor strength; `gold_rule_refs`; إن اسم preserved (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Stage 17 Batch 2.3: G016 NAAT_AGREEMENT — prefer نعت via Stage15 SIFA and agreement-gated APPOS/PRED overrides; L12 + morphological case; no lexical hardcoding (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Stage 17 Batch 2.4: G015 HAL_MANSUB — accusative حال after marfūʿ subject + verb; OBJ/NAAT guards; plural ـِينَ morph cue (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Batch 2.5 (presentation): `analyze_sentence` preferred iʿrāb tiered precedence includes L17 **candidate** over stale L11B; final headline counts from L17 `reasoning_summary`; `khabar_in_candidates` in compact + report; L11/L11B diagnostic sections preserved (risk: low) | analyze_sentence, tests/test_preferred_i3rab_integration |

| 2026-03-18 | Batch 2.6: L17 G026_JAR_TAALLUQ_VERB — fused prep+pronoun (لَـ/بِ+ضمير) taʿalluq to governing verb when OBJ follows; verbal_embedded region boosts confidence; not lexicon-based (risk: low) | L17_RULE_BASED_I3RAB |

| 2026-03-18 | Batch 2.7: L17 clause-level `khabar_in_analysis` — B2.7-K1_resolve_khabar_in_verbal_clause; token roles preserved; additive clause function (risk: low) | L17_RULE_BASED_I3RAB, analyze_sentence |

| 2026-03-21 | **Batch 2.8:** `analyze_sentence.render_report` — L17-first narrative, unified headline **الثقة النهائية** (single user-facing figure), L11/L11B demoted to appendix, `SECTION 4j` preferred table moved to appendix, duplicate L17 table removed; khabar-in after L17; tests `test_batch_28_report_presentation.py` (risk: none) | analyze_sentence |


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
