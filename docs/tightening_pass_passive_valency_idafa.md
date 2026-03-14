# Tightening Pass: Passive-Aware Wiring, Valency-Aware Syntax, Weak Idafa Suppression

This document describes the focused tightening pass that improves L10B and L11B by using existing upstream evidence (L8B verb governance, passive voice, valency) more intelligently, without redesigning the pipeline.

## Goals

- **Passive-aware wiring**: When L8B says a verb is passive, L10B and L11B treat the following noun as نائب فاعل (passive subject), not active فاعل.
- **Valency-aware syntax**: L8B governance/valency expectations shape dependency interpretation (intransitive vs transitive, required PP).
- **Weak idafa suppression**: Weak noun-noun idafa candidates are downgraded or suppressed when stronger verbal/passive structure exists.

## What Changed

### L10B (Deep Syntax)

1. **L8B profile map**  
   `_l8b_profile_by_token_index(tokens, lo)` builds a token-index → L8B verb profile map (by surface alignment). Used for passive, valency, and idafa logic.

2. **Passive-aware L10 isnadi mapping**  
   When mapping L10 isnadi links to edges, if the head is a passive verb (L8B `voice == "passive"` or `expected_subject_role == "نائب فاعل"`), subject links are mapped to **naib_fa'il** instead of fa'il.

3. **Passive-aware edges (step 3b)**  
   For each token with an L8B profile where `voice == "passive"` and the next token is noun-like and not already attached (e.g. as majrur), an edge (verb → noun) with relation **naib_fa'il** is added. Confidence comes from L8B voice evidence.

4. **Idafa tightening (step 4)**  
   - Idafa (i → j) is **not** added if token i has an L8B verb profile (verb must not head idafa).  
   - Idafa to j is **not** added if j already has relation **naib_fa'il** (stronger verbal structure wins).

5. **Weak idafa suppression (step 4b)**  
   For each idafa edge (from_id = i, to_id = j), if the token at i immediately follows a passive verb (L8B passive at i−1), the idafa edge is downgraded: confidence set to `CONF_WEAK`, status to candidate, and `idafa_suppression` set to *"weak idafa candidate under competing verbal structure"*. The same note is set on the dependent node.

6. **Valency in governance pass**  
   In `_run_verb_governance_pass`, L8B profiles are used: `valency_class == "intransitive"` forces `exp_objects = 0`; `valency_class == "transitive_one_object"` sets `exp_objects = max(exp_objects, 1)`. Actual naib_fa'il edges are considered; when the verb is passive and has at least one naib, a trace line is added. Summary gains optional flags: **passive_alignment_used** (true when any edge has relation naib_fa'il), **valency_alignment_used** (true when verb governance was applied), and **structural_conflict_penalty**.

7. **Trace**  
   If any edge has `idafa_suppression`, the syntax reasoning trace is extended with: *"Weak idafa candidate suppressed due to stronger verbal/passive structure."*

### L11B (Causal I3rab)

1. **Relation from L10B**  
   For each token, `dependency_relation` (and `dependency_head_id`) is taken **from L10B nodes/edges first**; L11 token_results are used only as fallback. So when L10B sets relation **naib_fa'il**, L11B sees it.

2. **Rule A0 — L10B naib_fa'il**  
   If `dep_relation == "naib_fa'il"` (or `"naib_fa'il_candidate"`) and the token is a noun, role is set to **نائب فاعل** with governing factor **فعل مبني للمجهول**, case مرفوع, marker الضمة. Reasoning and supporting sources refer to L10B and L8B.

3. **Rule B — نائب فاعل from L8B or template**  
   Rule B (passive verb + following noun) now also checks L8B: if the previous token has an L8B profile with `voice == "passive"`, نائب فاعل is assigned with reasoning *"L8B passive verb precedes; noun is نائب فاعل"*. When parse_strength is low, limitation can be *"passive evidence strong but dependency support weak"*.

4. **Idafa guard (Rule H)**  
   When `dep_relation == "idafa"`, L11B first checks `_l8b_has_upstream_passive_verb(lo, idx, tokens)`. If true, role is **not** مضاف إليه; instead, نائب فاعل is assigned as **candidate** with limitation *"weak idafa suppressed; preferred نائب فاعل from passive evidence"*. Otherwise, the existing idafa → مضاف إليه behaviour is kept.

5. **Helper**  
   `_l8b_has_upstream_passive_verb(lo, token_index, tokens)` returns True if any token before `token_index` has an L8B profile with `voice == "passive"`.

### Explainability

- **L10B**: Evidence list and claims now include: `passive_alignment_used`, `valency_alignment_used`, `naib_fa'il_edges`, `weak_idafa_suppressed`, and explicit claims such as *"Passive frame from L8B used to prioritize نائب فاعل over active فاعل"*, *"Valency/governance expectation used as weak syntactic prior"*, *"Weak idafa candidate suppressed due to stronger verbal/passive structure"*.
- **L11B**: Evidence and claims report نائب فاعل assignment count and weak idafa suppression in role prioritization when present.

### Presentation and analyze_sentence

- **SECTION 4b — DEEP SYNTAX**: When present, report `passive_alignment_used`, `valency_alignment_used`, and `weak_idafa_suppressed` (count).
- **SECTION 4c — CAUSAL I'RAB**: When present, report نائب فاعل assigned count and *weak_idafa_suppressed in role prioritization*.
- **L14 detailed/debug**: Deep syntax section shows passive alignment used, valency alignment used, and weak idafa suppressed count; causal i3rab section shows نائب فاعل count and weak idafa suppression note.

## Regression Sentence

**Input**:  
`"لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً أَبَداً وَلَعَاشَ مُنْتَمِياً لِوَطَنِهِ مُخْلِصاً لِدِينِهِ وَمُتَوَكِّلاً عَلَى اللَّهِ"`

**Desired direction of improvement**:

1. **ضُرِبَ** remains passive (L8B).
2. **الظَّالِمُ** moves away from false weak roles (e.g. weak مضاف إليه): L10B adds naib_fa'il (0→1) when L8B says passive; idafa from verb to الظالم is not added (verb in L8B); any idafa that would make الظالم mudaf ilayh under a competing passive is downgraded with `idafa_suppression`.
3. If full نائب فاعل cannot be resolved, الظالم should at least be a stronger نائب فاعل candidate than weak idafa.
4. Weak idafa loses influence under passive/verbal competition (downgraded or suppressed).
5. Confidence and limitations reflect remaining structural weakness (e.g. shallow parse, passive evidence strong but dependency support weak).

## What Remains Unresolved

- Full Arabic iʿrāb coverage is not claimed; only first-scope roles and prioritization.
- Present passive is out of scope for this pass.
- Valency seed is small; many roots still get "unknown" valency.
- Dependency parse strength may stay low on long conditional sentences; L11B correctly keeps confidence and status conservative (candidate/unresolved) and adds limitations.
- Idafa suppression is heuristic (e.g. “mudaf follows passive verb”); other competing structures could be added later.

## Files Changed

- `src/orchestrator/l10b_deep_syntax.py`: L8B map, passive L10 mapping, step 3b, idafa conditions, step 4b, governance pass valency/passive flags and trace.
- `src/orchestrator/l11b_causal_i3rab.py`: L10B-based dep_relation/dep_head_id, Rule A0, Rule B L8B check, `_l8b_has_upstream_passive_verb`, Rule H idafa guard.
- `src/orchestrator/explainability.py`: L10B and L11B evidence/claims for passive, valency, weak idafa.
- `src/orchestrator/l14_presentation.py`: Deep syntax and causal i3rab lines for passive/valency/idafa.
- `scripts/analyze_sentence.py`: SECTION 4b/4c reporting of passive_alignment_used, valency_alignment_used, weak_idafa_suppressed, نائب فاعل assigned.
- `tests/orchestrator/test_stage10b_deep_syntax.py`: passive-aware edge, weak idafa suppression, valency summary, regression sentence structure.
- `tests/orchestrator/test_stage11b_causal_i3rab.py`: passive → نائب فاعل, idafa guard, regression sentence نائب فاعل preferred.

## Definition of Done (Summary)

- L10B consumes passive evidence from L8B (naib_fa'il edges, L10 mapping, idafa exclusion/suppression).
- L10B uses valency/governance as a syntactic prior in the governance pass.
- Weak idafa is suppressed under stronger competing structure (downgrade + trace).
- L11B prioritizes passive-compatible roles (نائب فاعل) over weak idafa (idafa guard).
- Regression sentence shows measurable improvement (naib_fa'il or suppressed idafa; no confident false مضاف إليه for الظالم).
- Confidence and limitations reflect shallow parse and weak dependency support where applicable.
- Tests pass; no analyzer internals (L8, L9, core analyzers) were rewritten.
