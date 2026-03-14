# Golden snapshots (optional)

This folder may hold small, stable snapshots for orchestrator tests (e.g. stage status map for one canonical input). The suite currently does **not** depend on any file here; assertions are on status semantics and section existence only. If you add a snapshot:

- Keep it small (e.g. `{"L0_INPUT": "success", ...}`).
- Do not snapshot full pipeline JSON or long text bodies.
- Document the update in `docs/stage9_orchestrator_tests.md`.
- Re-run the full suite after changing snapshots: `PYTHONPATH=src pytest tests/orchestrator -q`.
