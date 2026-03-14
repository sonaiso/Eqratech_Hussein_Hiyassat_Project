# Stage 10 — GitHub Continuous Integration & Quality Gates

## What CI Runs

The workflow in `.github/workflows/ci.yml` runs on every **push** and **pull_request** to branches **main** and **develop**.

### Jobs

1. **Orchestrator & quality gates** (required)
   - **Matrix**: Python 3.11, 3.12
   - **Steps**:
     - Checkout repository
     - Set up Python
     - Install dependencies: `pip install -r requirements.txt` (if present), then `pip install pytest hypothesis pytest-cov`
     - **Run orchestrator integration tests**: `PYTHONPATH=src pytest tests/orchestrator -q -ra`
     - Run core engine smoke tests: if `tests/engines` exists, runs `pytest tests/engines -q -ra` (otherwise skipped)
     - **Generate coverage report**: `pytest tests/orchestrator --cov=src --cov-report=xml --cov-report=term-missing -q` (does **not** fail the build if coverage is low or step fails)

2. **Coq skeleton** (optional)
   - Compiles Coq gate files. Set with `continue-on-error: true` so that orchestrator pass is the gate; Coq failures do not block the main CI.

### Determinism and environment

- `PYTHONHASHSEED=0` is set at job level for reproducible ordering where relevant.
- No parallel pytest workers (single process).
- No network calls or large corpus downloads in the orchestrator tests.
- If future tests depend on local data (e.g. Quran dataset), they should mock or skip gracefully when the dataset is missing.

## How to Run Locally (same as CI)

```bash
export PYTHONHASHSEED=0
export PYTHONPATH=src
pip install -r requirements.txt
pip install pytest hypothesis pytest-cov
pytest tests/orchestrator -q -ra
```

With coverage (no failure on low coverage):

```bash
pytest tests/orchestrator --cov=src --cov-report=term-missing -q
```

## How to Debug a CI Failure

1. **Orchestrator tests failed**
   - Open the "Run orchestrator integration tests" step log.
   - Reproduce locally: `PYTHONPATH=src pytest tests/orchestrator -q -ra`.
   - Run a single file: `PYTHONPATH=src pytest tests/orchestrator/test_stage5_routing.py -v`.
   - Check for routing/validation/presentation/explainability regressions (e.g. L8/L9 no longer skipped for "وَ", or missing `evidence_trace`).

2. **Install failed**
   - Ensure `requirements.txt` exists and installs cleanly; CI falls back to installing only `pytest hypothesis pytest-cov` if needed for running tests.

3. **Python version**
   - CI uses 3.11 and 3.12. Run the same versions locally if the failure is version-specific.

## What CI Does NOT Yet Enforce

- **Coverage threshold** — Coverage is computed and reported (XML + term). The build does **not** fail on a minimum coverage %. Future work can add a threshold (e.g. `--cov-fail-under=50`).
- **Performance gate** — No maximum runtime or performance regression checks.
- **Linguistic depth** — CI does not fail due to limitations of analyzers (e.g. shallow syntax, text-based i3rab).
- **Coq proofs** — Coq job is optional (`continue-on-error: true`); admitted proofs or Coq install issues do not fail the main gate.
- **Optional datasets** — Missing local corpora (e.g. Quran files) must not fail CI; tests should skip or mock.

## Failure Semantics (when CI fails)

CI **fails** if:

- Any orchestrator test fails
- Stage routing regression (e.g. L8/L9 incorrectly success for operator-only input)
- Validation structure missing (e.g. `final_validation` or L13 output missing)
- Presentation output missing (e.g. `rendered_output` or L14 section missing)
- Explainability trace missing (e.g. `evidence_trace` not in artifacts)

CI **does not fail** because of:

- Linguistic depth limitations
- Admitted Coq proofs or Coq job failure
- Optional datasets missing
- Coverage % below a threshold (no threshold enforced yet)

## Future Roadmap

- **Coverage gate**: Add `--cov-fail-under` and optionally upload XML to Codecov/Coveralls.
- **Performance gate**: Fail or warn if orchestrator test suite exceeds a time limit (e.g. 3 min).
- **Branch coverage**: Switch to branch coverage and set a minimum for `src/orchestrator`.

## Pytest configuration (Stage 10)

- `pytest.ini`: `addopts` includes `-ra` (summary of all test results). `pythonpath = src .` and `testpaths = tests` ensure discovery and import path match local and CI runs.
