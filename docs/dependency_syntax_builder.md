# Stage 15 — DEPENDENCY SYNTAX BUILDER

## Purpose and scope

**Purpose:** Turn L10B (and related) precursor signals into an explicit, auditable dependency graph with fixed head→dependent directions, so that Stage 16 (Clause Engine) and Stage 17 (Rule-Based Iʿrāb) can consume governor/dependent structure without re-parsing.

**Scope (all passes):**

- **Pass A:** Nominal (mubtada–khabar) and verbal (verb–subject–object, passive subject) sentences; root in `root_resolution` only.
- **Pass B:** PP (JAR_MAJRUR, PP_ATTACH), idafa (IDAFA), adjective–noun (SIFA); weak idafa suppression.
- **Pass C:** Coordination (COORD, COORD_CONJ), apposition (APPOS), full `ambiguity_log` discipline, `candidate_markers` (TAMYIZ_CAND, HAL_CAND — mark only for Stage 16).
- **Pass D:** Integration tests, full documentation, final self-audit; no new relations or builder logic.
- **Pass E:** Quality-and-presentation upgrade only: reporting (SECTION 4f, ADDITIVE LAYERS block, evidence_trace); root selection (never operator/conjunction/preposition); POS bridge (L8B verb = effective verb); clause-first parsing; APPOS gating; PP attachment ranking; candidate markers (HAL_CAND, TAMYIZ_CAND) expansion; ambiguity discipline (≥0.80 resolved, 0.60–0.79 weak, &lt;0.60 logged). STAGE_ORDER unchanged; additive only.

Subordinate clauses, hal/tamyiz resolution, and relative clauses are **deferred to Stage 16**.

## Overview

The **DEPENDENCY_SYNTAX_BUILDER** (Stage 15) turns L10B precursor signals into an explicit, auditable dependency graph. It reads L4, L5, L8, L8B, and L10B; it does **not** overwrite or mutate L10B outputs.

- **Integration:** Runs after L10B; output stored under `lo["DEPENDENCY_SYNTAX_BUILDER"]`.

## ROOT representation policy

- **Root** is represented **only** in `root_resolution`. There is **no** ROOT relation in `dependency_links`.
- If a ROOT edge were present in `dependency_links`, its `head_id` would be null and it would be treated as redundant; `root_resolution` is the single source of truth for the root node.
- Pass A: ROOT is omitted from the relation inventory entirely.

## Output schema (Pass A)

```json
{
  "dependency_links": [
    {
      "head_id": "str",
      "dependent_id": "str",
      "relation": "str",
      "arabic_role": "str | null",
      "confidence": "float",
      "rule": "str",
      "inferred": "bool"
    }
  ],
  "root_resolution": {
    "root_id": "str",
    "root_form": "str",
    "confidence": "float",
    "rule": "str"
  },
  "ambiguity_log": [...],
  "corrections_log": [...],
  "coverage": "nominal_verbal_only"
}
```

- **dependency_links:** Head → dependent edges; `relation` from the controlled inventory; `arabic_role` e.g. MUBTADA, FAIL, KHABAR, MAF3UL_BIH, NAIB_FAIL.
- **root_resolution:** Sole record for the root node; no ROOT in `dependency_links`.
- **ambiguity_log:** Token-level ambiguity and selection (structured).
- **corrections_log:** Overrides of L10B signals by Stage 15 (structured).
- **coverage:** Pass A `"nominal_verbal_only"`; with Pass B, `"nominal_verbal_pp_idafa_sifa"`; with Pass C, `"nominal_verbal_pp_idafa_sifa_coord_appos"`.
- **candidate_markers:** (Pass C+) List of `{ "token_id", "marker": "TAMYIZ_CAND"|"HAL_CAND", "surface" }`; not resolved in Stage 15.

## Canonical dependency directions

Direction is **fixed** for every relation; no mixed directionality. All links are **head → dependent**.

| Relation    | Canonical direction | Notes |
|------------|---------------------|--------|
| **SUBJ**   | governing verb/root → SUBJ → subject noun | Verbal sentences only. Nominal sentences do **not** use SUBJ (mubtada is in root_resolution; predicate is PRED). |
| **OBJ**    | governing verb/root → OBJ → object noun | |
| **PRED**   | governing nominal head (mubtada) → PRED → khabar | Nominal only. |
| **NAIB_SUBJ** | governing passive verb/root → NAIB_SUBJ → naib al-fa'il | |
| **JAR_MAJRUR** | harf_al_jarr → JAR_MAJRUR → majrur noun | |
| **PP_ATTACH** | governing head (verb or noun) → PP_ATTACH → harf_al_jarr (PP anchor) | Do not use reverse. |
| **IDAFA**  | mudaf → IDAFA → mudaf_ilayhi | Do not use reverse. |
| **SIFA**   | noun (mawsuf) → SIFA → adjective (sifa) | |
| **COORD**  | head_conjunct → COORD → dependent_conjunct | |
| **COORD_CONJ** | head_conjunct → COORD_CONJ → conjunction | |
| **APPOS**   | main_noun → APPOS → appositive | |

Builder and tests use exactly these directions.

## Relation inventory (Pass A)

Defined in `src/orchestrator/dependency_syntax/relation_inventory.py`. ROOT is not in the inventory.

| Relation    | arabic_name      | arabic_role  | Canonical direction |
|------------|------------------|-------------|---------------------|
| SUBJ       | فاعل             | FAIL        | verb/root → SUBJ → subject noun (verbal only) |
| OBJ        | مفعول به         | MAF3UL_BIH | verb/root → OBJ → object noun |
| PRED       | خبر المبتدأ      | KHABAR     | mubtada → PRED → khabar |
| NAIB_SUBJ  | نائب فاعل       | NAIB_FAIL  | passive verb/root → NAIB_SUBJ → naib al-fa'il |

- **SUBJ** is used for **verbal** sentences only; nominal sentences use root_resolution (mubtada) and PRED (mubtada→khabar), not SUBJ.
- **arabic_role** is set on every link for downstream use.

## Relation inventory (Pass B)

| Relation    | arabic_name           | arabic_role  | Definition | Direction |
|------------|----------------------|-------------|------------|-----------|
| JAR_MAJRUR | جار ومجرور           | JAR_MAJRUR  | Preposition linked to governed noun (majrur) | harf → majrur |
| PP_ATTACH  | تعلق شبه الجملة      | PP_ATTACH   | PP attached to governing head | **head = governor (verb or noun), dependent = PP (harf). Always head → PP.** |
| IDAFA      | إضافة                | MUDAF       | Mudaf linked to mudaf ilayhi (head = mudaf, dependent = mudaf ilayhi) | mudaf → mudaf_ilayhi |
| SIFA       | نعت                  | NA3T        | Adjective (sifa) depending on noun (mawsuf) | **head = noun, dependent = adjective. Always noun → SIFA → adjective.** |

**Dependency direction policy (Pass B):** Direction is fixed and must not vary by case. **SIFA:** head = noun (mawsuf), dependent = adjective (sifa). **PP_ATTACH:** head = governing head (verb or noun), dependent = PP (harf_jar token). Downstream (e.g. Stage 17) can rely on these conventions.

## Relation inventory (Pass C)

| Relation     | arabic_name | arabic_role | Canonical direction |
|-------------|-------------|-------------|---------------------|
| COORD       | عطف         | ATF         | head_conjunct → COORD → dependent_conjunct |
| COORD_CONJ  | حرف عطف     | ATF_CONJ    | head_conjunct → COORD_CONJ → conjunction |
| APPOS       | بدل         | BADAL       | main_noun → APPOS → appositive |
| TAMYIZ_CAND | تمييز (مرشح) | —           | Marker only; no link. See `candidate_markers`. |
| HAL_CAND    | حال (مرشح)  | —           | Marker only; no link. See `candidate_markers`. |

- **Coordination detection:** Conjunction particle (و، ف، ثم، أو، أم) from L4 operator list or normalized surface; token between two conjuncts yields COORD (head_conjunct → dependent_conjunct) and COORD_CONJ (head_conjunct → conjunction).
- **Apposition heuristic:** Two adjacent noun-like tokens with no particle between and no existing PRED/IDAFA link between them; confidence medium (0.6). Do not add APPOS when the pair is already mubtada–khabar (PRED) or mudaf–mudaf_ilayhi (IDAFA).
- **Ambiguity log discipline:** Every ambiguous attachment must produce an entry with `token_id`, `candidates` (each with `relation`, `head_id`, `score`, `reason`), `selected`, `selection_reason`. Do not silently collapse ambiguity; if no candidate is clearly preferred, select highest score and mark confidence low.
- **TAMYIZ_CAND / HAL_CAND:** Placeholder markers only; do not resolve in Stage 15. Output key `candidate_markers` is a list (e.g. `[{ "token_id": str, "marker": "TAMYIZ_CAND"|"HAL_CAND", "surface": str }]`). Stage 16 uses these for clause-level resolution.

## Self-loop guard and L10B carry-forward (structural quality)

- **Self-loop guard:** Before adding any link to `dependency_links`, the builder checks `head_id != dependent_id`. If they are equal, the link is **not** added; an entry is appended to `corrections_log` with `override_reason: "self_loop_forbidden"` and `evidence_signals: ["self_loop_guard"]`. This applies to all relation types (SUBJ, OBJ, PRED, NAIB_SUBJ, JAR_MAJRUR, PP_ATTACH, IDAFA, SIFA, COORD, COORD_CONJ, APPOS). No exceptions; no self-loops ever.

- **Carry-forward from L10B:** Before applying Stage 15 rules, the builder reads all L10B `dependency_edges` with `status == "resolved"`. For each such edge, if the (from_id, to_id) pair is not already in `dependency_links`, it is added with: `relation` and `arabic_role` from a fixed mapping (naib_fa'il→NAIB_SUBJ/NAIB_FAIL, majrur→JAR_MAJRUR, idafa→IDAFA/MUDAF, fa'il/subject→SUBJ/FAIL, maf'ul_bih/object→OBJ/MAF3UL_BIH, mubtada→SUBJ/MUBTADA, khabar→PRED/KHABAR), `rule: "carried_forward_from_L10B"`, `inferred: false`. A `corrections_log` entry records `override_reason: "L10B resolved edge preserved"`. Stage 15 output must never have fewer links than L10B resolved edges (except for invalid self-loops or schema violations). Pass B/C then skip adding a link for the same (head, dependent) pair when that pair was already carried or added.

## Core builder rules (Pass A)

- **Nominal:** `main_clause_type == "nominal"`. First content noun → mubtada (root_resolution); second content noun/adjective → PRED (KHABAR). No PP-based predicate in Pass A.
- **Verbal:** Verb present; verb → root_resolution. Post-verb noun: active (L8B) → SUBJ (FAIL); passive (L8B) → NAIB_SUBJ (NAIB_FAIL). Second noun after subject, if L8B transitivity confirmed → OBJ (MAF3UL_BIH).
- **Simple active transitive tightening (2026-03-17):** Stage 15 now uses an **effective verb** filter for L8B profiles (resolved/high-confidence/passive/object-governance or L5 verb) instead of trusting every weak candidate profile as a real verb. This prevents noun tokens such as proper names from being skipped during SUBJ/OBJ detection. Direct-object detection is **clause-local** (`clause_units` boundary respected), preserves passive protection (`NAIB_SUBJ` instead of OBJ), and adds a conservative **maf'ul mutlaq** guard: same-root masdar-like nouns are not forced into normal OBJ. Exact duplicate links are suppressed.
- Every rule references morphological evidence (L5, L8, L8B), word order, and L10B precursor hints (as signals, not conclusions).

## Core builder rules (Pass B)

- **PP (jar–majrur):** L10B edges with relation `majrur` yield a **JAR_MAJRUR** link (harf_jar → majrur). **PP_ATTACH** direction is fixed: head = governing head (verb or noun), dependent = PP (harf_jar token). Always head → PP. Governor is chosen by valency (L8B `required_prepositions`) or nearest noun to the left. Ambiguous attachment is logged in `ambiguity_log` with ranked candidates.
- **Idafa:** Canonical direction **only**: mudaf → IDAFA → mudaf_ilayhi (head=mudaf, dependent=mudaf_ilayhi). Docs and builder do not use the reverse. L10B edges with relation `idafa` yield this link; **weak idafa suppression** reuses L10B rule (mudaf follows passive verb → suppress). *Note for Stage 17:* consider labelling head as MUDAF and dependent as MUDAF_ILAYH.
- **Adjective (SIFA):** Direction is fixed: head = noun (mawsuf), dependent = adjective (sifa). Link: **noun → SIFA → adjective**. Tokens typed as adjective (L5 or `pos_hint`) are linked to the nearest preceding noun; `arabic_role` NA3T on the link. Agreement (gender/number) from morphology can be used as a confidence booster in future passes.

## Core builder rules (Pass C)

- **Coordination:** Detect conjunction (waw, fa, thumma, aw, am) via normalized surface or L4 operator. For each conjunction at index `i` with neighbors `i-1`, `i+1`: add COORD (head_id=`i-1`, dependent_id=`i+1`) and COORD_CONJ (head_id=`i-1`, dependent_id=`i`). If consecutive conjunctions exist, add ambiguity_log entry with ranked candidates.
- **Apposition:** For each adjacent pair of noun-like tokens with no existing PRED/IDAFA link between them, add APPOS (head_id=first, dependent_id=second); confidence 0.6.
- **Ambiguity log:** All entries must have `token_id`, `candidates`, `selected`, `selection_reason`. Builder normalizes any incomplete entries before return.
- **Candidate markers:** Output includes `candidate_markers` (list). TAMYIZ_CAND and HAL_CAND are not resolved; they are markers for Stage 16.

## Integration point

- **Pipeline:** Hook in `pipeline_orchestrator.py` immediately after `L10B_DEEP_SYNTAX`; call `build_dependency_syntax(lo)` and set `lo["DEPENDENCY_SYNTAX_BUILDER"]`.
- **Non-destructive:** L10B (and other stage) outputs are unchanged.

## What Stage 15 consumes

- **L10B_DEEP_SYNTAX:** `main_clause_type`, `dependency_nodes`, `dependency_edges` (including `majrur`, `idafa`), `clause_units`, node-level hints (connective, role candidates).
- **L8B_VERB_BAB_GOVERNANCE:** Verb profiles (voice, expected_subject_role, transitivity, governance_family) for verbal root and SUBJ/OBJ/NAIB_SUBJ.
- **L8 (root extraction):** Root and token alignment for root_resolution.
- **L5 (word typing):** Noun/verb/adjective/operator for SIFA and conjunction detection.
- **L4 (operators):** Operator words (e.g. حرف جر، حرف عطف) for JAR_MAJRUR, PP_ATTACH, COORD_CONJ.
- **Morphology:** Used indirectly via L5/L8/L8B and L10B edges.

## What Stage 15 emits

- **dependency_links:** List of head→dependent edges with `relation`, `arabic_role`, `confidence`, `rule`, `inferred`.
- **root_resolution:** Single root node (`root_id`, `root_form`, `confidence`, `rule`); no ROOT in dependency_links.
- **ambiguity_log:** Structured entries (token_id, candidates, selected, selection_reason) for ambiguous attachments.
- **corrections_log:** Overrides of L10B signals by Stage 15 (when applicable).
- **coverage:** String describing enabled passes (e.g. `nominal_verbal_pp_idafa_sifa_coord_appos`).
- **candidate_markers:** List of TAMYIZ_CAND / HAL_CAND markers for Stage 16; not resolved here.

## How Stage 17 depends on Stage 15 outputs

Stage 17 (Rule-Based Iʿrāb Reasoner) will use:

- **Governor–dependent structure:** Each link gives a clear head (governor) and dependent; case/mood assignment can follow ʿāmil (governor) rules.
- **arabic_role:** FAIL, NAIB_FAIL, MAF3UL_BIH, KHABAR, MUDAF, JAR_MAJRUR, NA3T, etc., map directly to iʿrāb roles and ʿawāmil.
- **root_resolution:** Identifies the syntactic root (verb or mubtada) for sentence-level structure.
- **Canonical directions:** Fixed head→dependent convention avoids ambiguity when resolving case (مرفوع/منصوب/مجرور).

Stage 17 does **not** re-parse; it consumes `dependency_links` and `root_resolution` as the dependency backbone.

## Ambiguity handling policy

- **No silent collapse:** When multiple attachment candidates exist (e.g. PP to verb vs noun, or consecutive conjunctions), Stage 15 records them in `ambiguity_log` with ranked candidates (relation, head_id, score, reason).
- **Explicit selection:** Each entry has `selected` and `selection_reason`; if no candidate is clearly preferred, confidence is set low.
- **Downstream:** Stage 16 / Stage 17 can use `ambiguity_log` to refine or explain low-confidence decisions.

## Pass E — Quality and presentation (no new relations)

- **Reporting:** SECTION 4f (or SECTION X) shows coverage, root_resolution, dependency_links count, ambiguity_log count, corrections_log count, candidate_markers count, and main links. SECTION 5 lists STAGE_ORDER unchanged and adds ADDITIVE LAYERS (DEPENDENCY_SYNTAX_BUILDER, SEMANTIC_ROLE_PROJECTION, DISCOURSE_FRAME_BUILDER). evidence_trace includes a DEPENDENCY_SYNTAX_BUILDER entry.
- **Root selection:** Operator/conjunction/preposition (harf_jar) tokens are never chosen as root unless a rare rule explicitly allows it. Priority: resolved verb (L8B) &gt; clause head verb &gt; resolved predicate &gt; nominal predicate &gt; fallback content token.
- **POS bridge:** If a token appears in L8B verb_governance_profiles, Stage 15 treats it as effective_pos=verb only when the profile is strong enough for Stage 15 consumption (resolved/high-confidence/passive/object-governance or L5 verb). Weak candidate-only profiles on noun/name tokens do not suppress SUBJ/OBJ detection.
- **Clause-first:** Dependency relations are built with clause_unit awareness; token_to_clause map used to prefer same-clause attachment and to gate APPOS.
- **APPOS gating:** No APPOS for adjacent nouns if the dependent is PP-governed, HAL_CAND, TAMYIZ_CAND, likely SIFA, in another clause, or preposition-prefixed. Prefer no link over false APPOS.
- **PP attachment ranking:** Candidates ranked: verb/participle that fits (valency) &gt; same-clause noun &gt; other; low scores (&lt;0.60) logged in ambiguity_log; no silent weak attachment.
- **Candidate markers:** HAL_CAND and TAMYIZ_CAND expanded (post-verbal adjective-like for HAL; after quantity-like for TAMYIZ); reduces premature hard linking.
- **Ambiguity discipline:** No silent collapse; ranked candidates, selected, selection_reason; confidence bands: ≥0.80 resolved, 0.60–0.79 weak resolved, &lt;0.60 ambiguity/candidate.

## Known limitations

- **Upstream-bound:** Quality of dependency_links depends on L10B (main_clause_type, edges) and L8B (voice, transitivity). If L10B classifies a verbal sentence as nominal, Stage 15 will emit PRED instead of SUBJ/OBJ.
- **No subordinate clauses:** Clause boundaries and embedded clauses are deferred to Stage 16.
- **Hal and tamyiz:** Only marked as candidates (`candidate_markers`); resolution deferred to Stage 16.
- **Apposition:** Heuristic (adjacent noun-like tokens, no PRED/IDAFA); may over- or under-generate in edge cases.
- **Coordination:** Conjunction detection relies on L4 operator list and normalized surface (و، ف، ثم، أو، أم).

## Deferred to Stage 16

- Subordinate clauses
- Hal (حال) resolution
- Tamyiz (تمييز) resolution
- Relative clauses
- Full agreement-based SIFA confidence and ambiguity logging (optional refinement)

## Stage 15 readiness report (Pass D)

**Stage 15 → Stage 16 readiness:** **Yes.**  
L10B `clause_units` plus Stage 15 `dependency_links` and `root_resolution` provide a sufficient base for the Clause Engine: heads and dependents are explicit, coordination and apposition are represented, and `candidate_markers` (TAMYIZ_CAND, HAL_CAND) pass unresolved candidates to Stage 16. Clause Engine can consume `dependency_links` to infer clause boundaries and attach subordinate/hal/tamyiz when implemented.

**Stage 15 → Stage 17 readiness:** **Yes.**  
`dependency_links` provide the governor/dependent structure needed for rule-based iʿrāb: every relation has a fixed head→dependent direction, `arabic_role` maps to ʿāmil and grammatical function, and `root_resolution` identifies the sentence root. Stage 17 can assign case/mood from the governing head without re-parsing. Missing pieces (e.g. full agreement, some edge cases) are limitations of Stage 15 data quality, not of the schema.

## Files

- `src/orchestrator/dependency_syntax/relation_inventory.py` — relation labels and specs
- `src/orchestrator/dependency_syntax/builder.py` — `build_dependency_syntax(lo)`
- `src/orchestrator/dependency_syntax/__init__.py` — public API
- Hook: `src/orchestrator/pipeline_orchestrator.py` (after L10B)
- Integration tests: `tests/orchestrator/test_dependency_syntax_integration.py`
