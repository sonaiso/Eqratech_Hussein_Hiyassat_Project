# Stage 11 — Profiling Smoke Tests

## Commands Used

```bash
PYTHONPATH=src python3 scripts/profile_orchestrator.py
PYTHONPATH=src python3 scripts/profile_orchestrator.py --json report.json
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --profile "كَاتِبٌ"
```

## Observed Timing Summaries (example run)

- **Inputs**: 6 (canonical set).
- **Average total time** (sum of 15 stage elapsed_ms): ~0.1 ms (loop only; excludes initial FVAFK run).
- **Min/Max total time**: ~0.09–0.17 ms.
- **Note**: End-to-end wall time for the script is dominated by `run_fvafk_once()` before the stage loop; per-stage times are adapter-only.

## Slowest Stages Seen

- In repeated runs, **L14_PRESENTATION** often appears as slowest (rendering + evidence trace + augment).
- **L8_ROOT_EXTRACTION**, **L13_VALIDATION** can appear next when they do more work.
- Numbers are environment-dependent; do not rely on exact values.

## Future Optimization Candidates

- **L14_PRESENTATION**: Rendering and evidence-trace build; could be trimmed or cached if needed.
- **run_fvafk_once()**: Not currently in per-stage timing; future work could wrap it as a “pre-stage” and include in profiling.
- **L8 / L9**: Resolver and wazn matching; already fast in adapter path; optimization would be inside fvafk if ever needed.

## Environment Note

All timing is process-local and machine-dependent. CI and different machines will show different values. Tests assert only shape and consistency (e.g. `total_time_ms` present and non-negative, `per_stage` has all stage IDs), not exact timings.
