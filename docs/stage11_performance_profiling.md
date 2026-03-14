# Stage 11 — Performance & Profiling Layer

## What Is Measured

- **Total pipeline execution time** (`total_time_ms`): Sum of per-stage elapsed times for L0–L14.
- **Per-stage execution time** (`elapsed_ms`): Wall-clock time from immediately before `stage.run(pipeline)` to immediately after the stage returns (or raises).
- **Per-stage metadata**: `status`, `warnings_count`, `errors_count` (from layer output).
- **Summary counts**: `stages_run_count`, `stages_skipped_count`; `slowest_stage_id`, `slowest_stage_time_ms`.

No linguistic output is changed. Measurement only.

## Where Profiling Data Is Stored

- **Top-level**: `pipeline["profiling"]` when `profile=True` is passed to `run_pipeline` / `run`.
- **Shape**:
  - `total_time_ms`, `stage_count` (15), `stages_run_count`, `stages_skipped_count`
  - `slowest_stage_id`, `slowest_stage_time_ms`
  - `per_stage`: dict of stage_id → `{ elapsed_ms, status, warnings_count, errors_count }`
- **Presentation**: When profiling is present, `augment_rendered_output_with_profiling()` adds a "Performance Summary" section to `rendered_output.sections`. Compact mode can show total time in the summary line; detailed and debug get the full performance section.

## How to Enable / Use Profiling

- **API**: `run(text, profile=True)` or `run_pipeline(text, profile=True)`.
- **Script**: `PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --profile "كَاتِبٌ"`.
- **Benchmark script**: `PYTHONPATH=src python3 scripts/profile_orchestrator.py` runs the six canonical inputs with profiling and prints a report; `--json FILE` writes a JSON report.

Profiling is **off by default** (`profile=False`). When off, `pipeline["profiling"]` is not set.

## What Profiling Does NOT Mean

- **Not a validation or quality gate**: Slow performance does not affect `global_validity` or L13 issues.
- **Not an optimization**: This stage only measures; no caching, batching, or analyzer changes.
- **Not a guarantee of real-world latency**: Times are process-local and exclude e.g. FVAFK cold start; the first run is dominated by `run_fvafk_once()` which is not split per stage.
- **Environment-dependent**: Numbers vary by machine and load; do not assert exact timings in tests.

## Benchmark Inputs Used

The canonical set used in `scripts/profile_orchestrator.py` and in docs:

1. "وَ"
2. "في"
3. "!"
4. "يَا رَبِّ"
5. "كَاتِبٌ"
6. "إِنَّ اللَّهَ غَفُورٌ"

Optionally a longer multi-word input can be added later.

## How This Prepares Later Optimization

- **Identify slow stages**: `slowest_stage_id` and `per_stage` show where time is spent.
- **Regression detection**: CI or local runs can compare total or per-stage times over time (without failing on exact values).
- **Targeted optimization**: Once a stage is identified as slow, optimization can be done in the analyzer or adapter without changing the profiling contract.

## Implementation

- **Module**: `src/orchestrator/profiling.py` — `build_profiling_summary(per_stage_records)`.
- **Orchestrator**: `pipeline_orchestrator.run_pipeline(..., profile=False)` times each stage when `profile=True`, appends to `profile_records`, then sets `pipeline["profiling"]` and calls `augment_rendered_output_with_profiling(pipeline)`.
- **L14**: Compact shows total time when profiling present; detailed/debug get a Performance Summary section via augment (no change to L14’s internal render when pipeline had no profiling at render time).
