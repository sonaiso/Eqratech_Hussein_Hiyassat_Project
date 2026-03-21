# SCIENTIFIC NEXT PHASES

**Future phase tracker for the FVAFK Arabic Linguistic Reasoning Engine.**  
Organised by scientific hypothesis, required layers, risk, and expected capability.

---

## Phase Alpha — Syntax realism tightening

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Tighter dependency and role assignment (passive, valency, idafa) improves structural coherence and reduces false role leakage. |
| **Required layers** | L8B (passive, governance), L10B (naib_faʾil, valency alignment, weak idafa suppression), L11B (idafa guard, نائب فاعل prioritisation), Stage 15 Dependency Syntax Builder (effective-verb filtering, clause-local OBJ attachment), L11 legacy iʿrāb family/role safety (proper noun/jamid safety, passive verb protection, OBJ over maf'ul mutlaq when structurally resolved). |
| **Risk analysis** | Low–medium: additive changes; risk of over-suppressing valid idafa in edge cases. |
| **Expected emergence** | More realistic subject/object/naib_faʾil assignment; SECTION 4b/4c and confidence reflect structure. |

*Status: Implemented (tightening pass completed). L11 legacy iʿrāb now respects grammatical family, passive voice, proper noun/jamid safety, and Stage 15 core-role evidence; verb rows stay verbal, noun rows stay noun-family, passive nouns prefer نائب فاعل, and Stage 15 OBJ suppresses weak maf'ul mutlaq fallbacks. Stage 15 now also attaches direct objects in clear simple transitives more realistically while preserving passive protection and maf'ul mutlaq caution. Stage 17 Batch 2.2 adds gold-style structural reinforcement (G007 مفعول به / G010 فاعل) from Stage 15 OBJ/SUBJ when governors are licensed, without phrase lookup. Stage 17 Batch 2.3 adds G016 (نعت agreement) from Stage 15 SIFA/APPOS/PRED plus L12 and morphological case agreement. Stage 17 Batch 2.4 adds G015 (حال منصوب) with structural SUBJ/NAIB and accusative morphology, without phrase lookup.*

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
| **Required layers** | Connectives layer (in place); DISCOURSE_FRAME_BUILDER (in place); Stage 15 Dependency Syntax Builder (implemented); Stage 16 Clause Engine (implemented); L12B discourse hints. |
| **Risk analysis** | Medium: clause boundaries and attachment are hard; connectives are hints only. |
| **Expected emergence** | Clause typing; connective-aware attachment; discourse coherence hints; SECTION 4e discourse frames; SECTION 4g clause structure. |

*Status: Connectives and DISCOURSE_FRAME_BUILDER in place; Stage 15 (Dependency Syntax Builder) implemented (self-loop guard, L10B carry-forward, Pass B/C/D/E, attached coordination-prefix handling with APPOS suppression, explicit-coordination suppression of residual `APPOS`/`PRED` overlap on the same pair, narrow `INNA_NAME` governance support, stricter attached-prefix detection so `فُرُوجَهُمْ` is not misread as coordination, **Pass E2/E3** late-clause verbal SUBJ/OBJ and `ISM_FAIL` object patterns with nominal-`PRED` supersession where applicable, **Pass E3 gating**: no `OBJ` from `ISM_FAIL` to a **following finite verb** (`L14:VERB` / strong verb evidence) so object chains do not spill into a new verbal clause; **Pass 5b COORD resumption**: attached `وَ` conjuncts resolve their head by scanning left past local participial `OBJ` spans and accusative intensifier tails so coordination chains resume correctly (e.g. after `… الذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ`); **Batch 1.5** Pass 5b conjunct compatibility uses L14 (`ISM_FAIL`, `ISM_MAFUUL`, `SIFA_MUSHABBAHA`, `SIGA_MUBALAGHAH`) when L5 mis-tags a `وَالـ` list member as `verb`, so intermediate conjuncts are not skipped; **multi-letter PP-prefix** gating for APPOS/E3, **post-pass removal of APPOS** whose head is a strong verb / L14 `VERB`, and **Batch 1.3 structural competition** against false `Pass_C_apposition_adjacent_nouns_gated` APPOS in verbal tails (OBJ+و-second-conjunct, waw-conjunct+`SIFA_MUSHABBAHA`, `ISM_FAIL` OBJ+`SIFA_MUSHABBAHA`)). Stage 16 (Clause Engine) implemented: conditional decomposition (shart_particle, feil_shart, jawab_particle, jawab_shart); SECTION 4g; **`verbal_clause_regions`** flags a late finite SUBJ+OBJ span after `INNA_NAME` as `verbal_embedded` for downstream L17. Clause triggers now prefer real `COND` operators over noisy connective hints, and the shared connective/discourse layer now also blocks `إِنَّ` / `أَنَّ` from false conditional framing unless the token is explicitly the conditional `إِنْ`. **Canonical derivational morphology** (`canonical_stem` / `canonical_root` / `canonical_wazn` in `ARABIC_WORD_STATE`, `canonical_derivation` module, hollow sync of `canonical_root`) feeds L14/L17 and report tables; see `docs/stage15_canonical_core_link_batch.md`.*

---

## Phase Epsilon — Narrative reasoning

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Combined syntax, iʿrāb, semantics and rhetoric support narrative/argument structure. |
| **Required layers** | Stage 15 Dependency Builder **(implemented — self-loop guard, L10B carry-forward, Pass B/C/D/E)**, Stage 16 Clause Engine **(implemented)**, L17 Rule-Based Iʿrāb, L18 Semantic Role Engine, L20 Rhetorical Structures. |
| **Risk analysis** | High: multiple new engines; integration and evaluation critical. |
| **Expected emergence** | End-to-end narrative-level analysis; explainable argument structure. |

*Status: Stage 15 implemented (self-loop guard, L10B carry-forward, PP, idafa, SIFA, COORD, APPOS, candidate_markers, effective-verb filtering, clause-local OBJ, maf'ul mutlaq guard, attached coordination-prefix handling, explicit-coordination suppression of residual `APPOS`/`PRED` overlap, and narrow `INNA_NAME` governance support). Stage 16 (Clause Engine) implemented: conditional decomposition; SECTION 4g; `ACC_TAWKID` / `إنَّ` no longer triggers false conditional packaging; **`verbal_clause_regions`** for embedded finite tails. **L17 Batch 2.1:** B2.1-V1 نائب عن المفعول المطلق from Stage15+L14 participial object patterns; B2.1-V2 **`khabar_in_candidates`** when `INNA_NAME` + verbal region. **Batch 2.5 (reporting only):** `scripts/analyze_sentence.py` fuses **preferred structured iʿrāb** with precedence L17 resolved → L17 candidate → L11B → L11 text; headline summary and `ما وجده` use L17 `reasoning_summary` when present so L11B-only unresolved counts do not masquerade as final state; `khabar_in_candidates` surfaced in markdown. **Batch 2.6 (L17):** **G026_JAR_TAALLUQ_VERB** — fused لَـ/بِ + ضمير as **شبه جملة متعلّقة بالفعل** when a strong verb governs an OBJ after the PP token; uses `verbal_embedded` when available; no phrase lexicon. **Batch 2.7 (L17):** **`khabar_in_analysis`** + **B2.7-K1_resolve_khabar_in_verbal_clause** — clause-function label (جملة فعلية في محل رفع خبر إن) without overwriting per-token roles; `secondary_analysis.khabar_in_clause_resolution_rule` distinct from B2.1 `khabar_in_rule`. **L14 Jamid vs Mushtaq implemented (Pass 1):** derivational classification after L9 with family-safe tightening against weak VERB/MASDAR overreach, internal proclitic-aware normalization, restored strong true-verb priority for genuine verbs, **stem-aligned L8/L9 via additive ARABIC_WORD_STATE**, **hollow اسم فاعل root recovery** (صائم→ص-و-م, RULE 1H), **hollow اسم مفعول root recovery** (مقول→ق-و-ل, مبيع→ب-ي-ع, RULE 2H), and a **hard JAMID gate** when root or wazn is pipeline-confirmed (`MUSHTAQ_LEXICAL`). **Canonical root propagation:** `ARABIC_WORD_STATE.root` is authoritative after hollow correction (`raw_l8_root` retains L8 for audit); L14 presentation and Stage 15 same-root indexing read canonical roots, eliminating split state where derivational class was correct but displayed root still reflected raw L8. **L13 Verb Transformation implemented (Pass 1):** `L13_VERB_TRANSFORMATION` now sits between `L14_JAMID_MUSHTAQ` and `L12_GENDER_NUMBER` in `STAGE_ORDER`, producing base active/passive forms, masdar, and imperative with conservative weak-root/unknown-bab fallbacks; SECTION 4l. **L12 Gender & Number implemented (Pass 1):** noun-family plural tightening keeps `...ين` forms plural/dual-aware instead of false singular fallback, and supported mushtaq-like noun-family `...ين` forms now prefer `PLURAL_SOUND_M` over `UNKNOWN`; genuine verbs still stay on verb-family handling instead of noun defaults; SECTION 4k; gender/number merged back into ARABIC_WORD_STATE after L12. **L17 Rule-Based Iʿrāb Reasoner implemented (v1 + v2):** token_reasoning from Stage 15/16, L8B, L5, L4; v2 consumes L12 and L14 for agreement/derivational refinement, reads ARABIC_WORD_STATE for morphology evidence, plus a narrow reference-driven pass for `إنَّ` governance, accusative conjunct inheritance, constrained `ISM_FAIL` object-governance, targeted `نائب عن المفعول المطلق` support notes, and clear late verbal-clause restoration; explicit `إنَّ` coordination chains are now preserved before local governance can activate, and unsupported conditional overreach is blocked; SECTION 4h; docs/stage17_rule_based_i3rab_v2.md. **L17 V3 (Quranic-aligned, lexicon/structural):** documented accusative حال (e.g. جَمِيعًا), `إنَّ` + dual elative `…كُمْ` (اسم/خبر), documented ظرف زمان (لَيْلَةَ), nominal clause خبر مرشح for اسم الجلالة after هُوَ (NFC-tolerant), and **جملة حالية** labelling for verbal hal-clauses (full clause-hal analysis deferred v4); tests verify tokens against `data/quran_i3rab.csv` via `orchestrator.quran_gold.loader`. L18, L20 remain planned.*

---

## Phase Zeta — Arabic cognitive simulation

| Item | Description |
|------|-------------|
| **Scientific hypothesis** | Full pipeline (morphology → syntax → iʿrāb → semantics → rhetoric → evaluation) approximates a cognitive model of Arabic grammatical reasoning. |
| **Required layers** | L12–L25 (Gender/Number, Verb Transformation, Jamid/Mushtaq, Dependency, Clause, Iʿrāb Reasoner, Semantic Roles, Sentence Modes, Rhetoric, Lexical Ontology, Gold Eval, Error Taxonomy, Reporting, Optimization). |
| **Risk analysis** | High: long roadmap; depends on gold data and evaluation discipline. |
| **Expected emergence** | Reproducible, evaluable, explainable Arabic linguistic reasoning engine. |

*Status: Long-term roadmap; see FVAFK_MASTER_EVOLUTION.md. **L12 Gender & Number (Pass 1) implemented:** token_features (gender, number, number_type, agreement_candidates, agreement_status, tamyiz_relation); SECTION 4k; agreement unresolved in pipeline order. **L13 Verb Transformation (Pass 1) implemented:** `L13_VERB_TRANSFORMATION` derives base active/passive, masdar, and imperative from root + bab/tense evidence; SECTION 4l. **L14 Jamid vs Mushtaq (Pass 1) implemented:** derivational classification now feeds Stage 13 as a verb-confirmation gate. **Batch 2.8 (reporting):** `analyze_sentence` user-facing markdown puts L17 first with a single headline confidence; L11/L11B are appendix-only for reference.*

---

*End of SCIENTIFIC_NEXT_PHASES*
