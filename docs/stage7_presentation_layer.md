# Stage 7 — Real Presentation Layer (L14)

## Summary

L14 is the **presentation/rendering layer**. It converts the pipeline object into readable output for users and developers. It does **not** perform any linguistic analysis; it only renders existing pipeline outputs.

## What L14 Renders

- **Input**: The full pipeline object (after L0–L13 have run), including `layer_outputs`, `final_validation`, and `original_text`.
- **Output**: A structured `rendered_output` with `mode`, `summary`, `sections`, and optional `artifacts`.
- **Source of truth**: All content is derived from actual pipeline data. No fabricated interpretations. If data is absent, the renderer states so clearly.

## Rendering Modes

| Mode      | Purpose |
|----------|---------|
| **compact**  | Short readable summary: input, validity, sentence type, key roots, key i3rab, validation note. |
| **detailed** | Layer-by-layer report with all required sections (overview, stage status, tokens, phonology, morphology, syntax, **i3rab**, semantic/rhetorical, validation). |
| **debug**    | Structural summary for developers: request_id, stage order, per-stage status and warning/error counts, validation issue codes. No full raw_module_output dump. |

Default mode when `_render_mode` is not set: **detailed**.

## Section Structure (Detailed Mode)

1. **Overview** — Original text, `global_validity`, `final_confidence`, short interpretation.
2. **Stage Status Summary** — All stages L0–L14 with status (success / partial / skipped / failed / pass_through / missing).
3. **Token / Word Summary** — Tokens from L2, word typing from L5.
4. **Phonology / Syllables** — L6/L7 status and counts.
5. **Morphology** — Roots (L8), wazn/pattern (L9); if skipped, explains why from stage status.
6. **Syntax** — L10 result; if failed/partial, states so clearly.
7. **I3rab** — **Explicit standalone section.** Renders L11 `token_results`: per-token surface form and `i3rab_text`. Not hidden inside syntax.
8. **Semantic / Rhetorical** — Sentence type (L12), rhetoric signals if any.
9. **Validation** — `global_validity`, `final_confidence`, issues list from L13.

## How L14 Uses L13 final_validation

- L14 reads `pipeline["final_validation"]` (populated by the orchestrator after L13 runs).
- Overview and Validation sections use `global_validity`, `final_confidence`, and `issues`.
- Compact mode uses the same for the one-line validation note.

## How I3rab Is Displayed

- **Detailed mode**: Dedicated section **"I3rab"** with title "I3rab (L11) — إعراب". Lists each token’s surface form and its `i3rab_text` from L11 `token_results`.
- **Compact mode**: Shows up to the first few tokens’ i3rab in the summary block under "I3rab:".
- I3rab is never folded into the Syntax section; it remains a first-class visible section.

## What Presentation Does NOT Do

- Does **not** run or change any analyzer (L1–L12).
- Does **not** invent linguistic results or fill missing data with guesses.
- Does **not** validate; it only displays validation results from L13.
- Does **not** dump full `raw_module_output` in user-facing sections (debug mode shows counts and codes only).

## Integration

- **Orchestrator**: After L14 runs, the orchestrator copies L14’s `transformation_result` into `pipeline["rendered_output"]`.
- **Render mode**: Passed via `run_pipeline(..., render_mode="compact"|"detailed"|"debug")`. L14 reads `pipeline["_render_mode"]` (set by the orchestrator before the run). The key is removed from the final pipeline before return.
- **Script**: `scripts/run_orchestrator_skeleton.py` supports `--render compact`, `--render detailed`, `--render debug`. With `--render`, the script prints the rendered summary (and for detailed, each section).

## Files

- **Implementation**: `src/orchestrator/l14_presentation.py` — `render_pipeline()`, `RealL14Presentation`.
- **Contract**: Same as Stage 2; `rendered_output` is an optional top-level key on the pipeline object.
