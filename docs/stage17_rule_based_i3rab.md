# Stage 17 — Rule-Based Iʿrāb Reasoner

**Skeleton v1.** Stage 17 produces structured per-token iʿrāb reasoning from pipeline evidence. It does **not** replace L11B; L11B remains baseline/fallback and is consumed as supporting evidence.

## Purpose

- **Input:** L4, L5, L8B, L10B, DEPENDENCY_SYNTAX_BUILDER (Stage 15), CLAUSE_ENGINE (Stage 16), L11B.
- **Output:** `token_reasoning` (per-token: syntactic_role, governing_factor, i3rab_case_or_mood, marker, reasoning_steps, clause_id), `reasoning_summary`, `coverage`, `ambiguity_log`.

## Evidence precedence

1. Stage 16 clause boundaries / clause_id  
2. Stage 15 dependency links (SUBJ, OBJ, NAIB_SUBJ, JAR_MAJRUR)  
3. L8B voice / governance  
4. L4 operators  
5. L5 grammatical family  
6. L10B hints  
7. L11B as supporting evidence only  
8. Legacy textual iʿrāb only for low-confidence fallback  

## Rules implemented (v1)

- **Rule 1:** Active verb (L8B voice active / not passive) → فعل، مبني على الفتح  
- **Rule 2:** Passive verb (L8B voice passive) → فعل، مبني للمجهول  
- **Rule 3:** Stage 15 SUBJ + active verb → فاعل، مرفوع، الضمة  
- **Rule 4:** Stage 15 NAIB_SUBJ + passive verb → نائب فاعل، مرفوع، الضمة  
- **Rule 5:** Stage 15 OBJ + active verb → مفعول به، منصوب، الفتحة  
- **Rule 6:** Stage 15 JAR_MAJRUR → اسم مجرور، مجرور، الكسرة  
- **Rule 7:** Clause packaging from Stage 16 (clause_id per token)  
- **Rule 8:** Present verb mood from L4 (v1: safe fallback only)  

Safe fallbacks keep VERB/NOUN/PARTICLE family consistency; no cross-family output.

## Integration

- **Stage order:** L17_RULE_BASED_I3RAB runs after L11B_CAUSAL_I3RAB (in `STAGE_ORDER`).  
- **Reporting:** SECTION 4h in `scripts/analyze_sentence.py` shows token_reasoning table and reasoning_summary.  
- **Compact JSON:** `compact["rule_based_i3rab"]` holds the transformation_result.  

## Limitations (v1)

- No حال، تمييز، نعت، بدل، عطف بيان، خبر/مبتدأ in generality.  
- No استثناء، تنازع، or complex estimated case endings.  
- Present verb mood from strong operators only (Rule 8 minimal).  

## Files

- `src/orchestrator/l17_rule_based_i3rab.py` — builder and stage class  
- `tests/orchestrator/test_stage17_rule_based_i3rab.py` — tests  
