# Stage 9 — Orchestrator Integration Test Framework

## What Is Covered

The orchestrator integration test suite in `tests/orchestrator/` verifies:

1. **Pipeline contract** — Top-level keys (`pipeline_version`, `request_id`, `original_text`, `stage_order`, `layer_outputs`), fixed stage IDs (L0–L14), required fields per layer (`status`), `final_validation` and `rendered_output` populated.

2. **Stage ordering** — `stage_order` length 15, equals the fixed list; registry order matches; `layer_outputs` keys match `stage_order`.

3. **Routing / gate semantics (Stage 5)** — For "وَ" and "في", L8 and L9 are skipped; for "!", L8/L9 skipped; tokenization still works for "!"; for "كَاتِبٌ", L8 has root evidence, L9 has wazn evidence, L11 has i3rab evidence; L12 does not overclaim for single-token operator.

4. **Validation (Stage 6)** — L13 is not pass_through; L13 `transformation_result` includes `global_validity`; top-level `final_validation` exists with `global_validity`, `issues`, `final_confidence`; direct call to `run_validation` with manipulated `layer_outputs` returns expected structure (issues list, validity in allowed set).

5. **Presentation (Stage 7)** — L14 status is success or partial; `rendered_output` exists; mode matches requested (compact/detailed/debug); summary non-empty; detailed mode has sections; detailed mode has explicit **I3rab** section; debug mode includes stage-level information.

6. **Explainability (Stage 8)** — `rendered_output.artifacts.evidence_trace` exists; trace is a list; for content input non-empty; each entry has `claim`, `supporting_stage`, `evidence`, `status`; for "وَ", trace explains L8/L9 skipped; for "كَاتِبٌ", trace includes root/pattern/i3rab; L13 validation reasoning appears in trace.

7. **Smoke inputs** — All canonical inputs complete; all stage statuses in allowed set; `final_validation.global_validity` present; rendered output has mode and summary; for "كَاتِبٌ" and "إِنَّ اللَّهَ غَفُورٌ", detailed mode has I3rab section; evidence trace structure checked for all inputs.

## What Is Intentionally Not Asserted

- **Exact long text bodies** — No assertions on full section content or exact summary strings, so the suite stays stable when wording or formatting changes.
- **Exact raw_module_output dumps** — Tests do not depend on full analyzer raw output.
- **Timing or request_id value** — Not asserted.
- **Exact validity value** for pathological inputs — Only that `global_validity` exists and is in the allowed set (valid/partial/weak/invalid).
- **Exact issue codes** — Validation tests check that issues exist and structure is correct, not a fixed list of codes for every run.

## Canonical Test Inputs

| Input | Purpose |
|-------|---------|
| وَ | Operator-only; L8/L9 skipped |
| في | Particle; L8/L9 skipped |
| ! | Punctuation; tokenization + L8/L9 skipped |
| يَا رَبِّ | Invocation + noun |
| كَاتِبٌ | Derived noun; root, wazn, i3rab |
| إِنَّ اللَّهَ غَفُورٌ | Short sentence; i3rab and syntax relevance |

## Snapshot Policy

The suite does **not** use golden snapshot files for full pipeline JSON (too brittle). Assertions are:

- **Status semantics** — Allowed values only; skipped/success/partial as expected per input.
- **Section existence** — Section IDs (e.g. `i3rab`) present in detailed mode; no exact body.
- **Evidence trace structure** — Required keys on entries; presence of L8/L9/L11/L13 in trace.

If a future snapshot is added (e.g. `tests/orchestrator/golden/status_map_katib.json`), it should be limited to small, stable structures (e.g. stage_id → status) and documented here. Update snapshots only when contract or intended behavior changes, and run the full suite after updates.

## How to Run Orchestrator Tests Locally

```bash
PYTHONPATH=src pytest tests/orchestrator -q
```

Verbose:

```bash
PYTHONPATH=src pytest tests/orchestrator -v
```

Single file:

```bash
PYTHONPATH=src pytest tests/orchestrator/test_stage5_routing.py -v
```

## Relation to Other Tests

- **Analyzer-level tests** (e.g. `tests/c2b/`, `tests/c2e/`, `tests/test_syllabifier.py`) — Test individual engines (root extraction, enricher, syllabifier, etc.). Orchestrator tests do **not** replace them; they complement by ensuring the **orchestrator** contract, routing, validation, rendering, and explainability hold when those engines are wired together.
- **Existing `tests/test_orchestrator_e2e.py`** — Overlaps in coverage (e.g. 15 layers, rendered output, gate skips). The `tests/orchestrator/` suite is more structured (contract, order, routing, validation, presentation, explainability, smoke) and keeps assertions focused on status semantics and section existence.

## Test Files

| File | Coverage |
|------|----------|
| `test_pipeline_contract.py` | Top-level keys, stage IDs, layer_outputs shape, final_validation, rendered_output |
| `test_stage_order.py` | stage_order fixed list, registry order, layer_outputs keys |
| `test_stage5_routing.py` | Gate skips for وَ/في/!; root/wazn/i3rab for كَاتِبٌ; L12 no overclaim |
| `test_stage6_validation.py` | L13 not pass_through, global_validity, final_validation, run_validation direct call |
| `test_stage7_presentation.py` | L14 status, modes, sections, I3rab section |
| `test_stage8_explainability.py` | evidence_trace artifact, entry shape, skipped/reasoning |
| `test_smoke_inputs.py` | All canonical inputs; status validity; section existence |

## Helpers (`conftest.py`)

- `run_pipeline_for_test(text, render_mode="detailed")` — Run pipeline for tests.
- `extract_stage_status_map(pipeline)` — `stage_id -> status` for all required stages.
- `assert_has_section(rendered_output, section_id)` — Assert section id present.
- `get_evidence_claims(pipeline)` — `rendered_output.artifacts.evidence_trace`.
- `CANONICAL_INPUTS`, `REQUIRED_STAGE_IDS` — Shared constants.
- Fixtures: `pipeline_katib`, `pipeline_waw` (module-scoped).
