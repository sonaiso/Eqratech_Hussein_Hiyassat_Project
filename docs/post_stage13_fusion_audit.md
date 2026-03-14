# Post-Stage-13 Fusion Audit

## What This Audit Is

The **Post-Stage-13 Fusion Audit** runs **after** L13 Cognitive Fusion. It evaluates whether the fusion result is **stable**, **coherent**, and **aligned** with upstream evidence. It is **not** a linguistic analyzer, **not** a replacement for L13 Validation, and **not** a repair step. It only **inspects** and **reports**.

## Difference Between Pre-Stage-13 and Post-Stage-13 Audit

| | Pre-Stage-13 Readiness Audit | Post-Stage-13 Fusion Audit |
|---|-----------------------------|-----------------------------|
| **When** | Before L13 Cognitive Fusion | After L13 Cognitive Fusion |
| **Purpose** | Evaluate maturity of evidence sources for fusion | Evaluate coherence of fusion output |
| **Inputs** | L4–L12, L12B, layer_outputs | cognitive_fusion, pre_stage13_audit, L8–L12B |
| **Output** | readiness_score, readiness_band, blocking_issues | fusion_consistency, issues, source_alignment |
| **Use** | Set fusion_mode (conservative vs normal) | Report consistency; do not change fusion |

## What This Audit Checks

1. **POS consistency** — `stable_pos` in fusion should not contradict strong upstream morphology (e.g. L5 kind noun vs fusion verb).
2. **Role consistency** — `stable_role` should not contradict syntax/i3rab when those are available and strong.
3. **Confidence sanity** — Token and global confidence must be in [0.05, 0.98]; global coherent with unresolved counts.
4. **Unresolved ambiguity accounting** — Sum of per-token `ambiguities_remaining` should match summary `unresolved_ambiguities`.
5. **Weak-source overreach** — If fusion relied mainly on weak sources (rhetoric/analogical) while strong sources (root/wazn) were present, audit notes it.
6. **Conservative mode behavior** — If pre_stage13_audit readiness was LOW and fusion_mode was conservative, fusion must not over-resolve syntactic roles.

## Why It Exists

- Gives a **second check** on fusion output without replacing validation.
- Surfaces **contradictions** (e.g. POS vs upstream kind) and **overreach** (e.g. weak-only evidence when strong was available).
- Supports **debugging** and **quality gates** (e.g. fail or warn when fusion_consistency is low).

## What It Does NOT Do

- Does **not** change upstream or fusion outputs.
- Does **not** infer new roots, wazn, or roles.
- Does **not** “repair” fusion results; only audits them.
- If fusion is missing, it **reports** (e.g. MISSING_FUSION_STATE); it does **not** fabricate fusion.

## Output Shape

- **fusion_consistency**: `high` | `medium` | `low`
- **resolved_conflicts**: int (from token_states)
- **remaining_ambiguities**: int (from fusion summary)
- **issues**: list of `{ code, message, severity, token? }`
- **advisory_notes**: list of strings
- **source_alignment**: `{ strong_sources_respected, weak_source_overreach }`

## Issue Codes (When Supported by Data)

- `FUSION_POS_CONTRADICTION`
- `FUSION_ROLE_CONTRADICTION`
- `CONFIDENCE_OUT_OF_RANGE`
- `UNRESOLVED_AMBIGUITY_MISMATCH`
- `WEAK_SOURCE_OVERREACH`
- `CONSERVATIVE_MODE_VIOLATION`
- `MISSING_FUSION_STATE`

## Future Use for Stronger Coherence Models

The same hook (run after fusion, read-only) can later drive a **stronger coherence model** (e.g. learned scorer, or stricter rules) while keeping the same output shape and no overwrite of fusion or upstream.
