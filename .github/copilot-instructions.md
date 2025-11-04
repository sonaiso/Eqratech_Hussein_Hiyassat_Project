## Purpose
Provide concise, actionable guidance for an AI coding agent to be productive in this repository. Focus is on the engine pattern, data shapes, and common workflows so agents can make minimal, safe changes.

## High-level architecture (big picture)
- Repository is a set of small, focused "engine" modules (files ending with `_engine.py`).
- Each engine exposes a class (usually named <Thing>Engine) that subclasses `BaseReconstructionEngine` and implements a `make_df()` classmethod and a `SHEET_NAME` string. Example: `SentenceGenerationEngine` in `sentence_generation_engine.py`.
- `reconstruction_utils.reconstruct_from_base_df()` is the canonical transformer: engines return a base DataFrame which is normalized, UTF-8/unicode-filled, and deduplicated by the reconstruct function.
- `Main_engine.py` discovers engine modules (via `pkgutil.iter_modules`) and calls each engine's `make_df()` to export sheets into a single Excel workbook (`full_multilayer_grammar.xlsx`).

## Engine contract / minimal checklist for new or modified engines
- File name should be `<feature>_engine.py` and live in the repository root (module discovery imports by module name).
- Define a class that inherits from `BaseReconstructionEngine`.
- Provide `SHEET_NAME = '...'` (used as the Excel sheet name truncated to 31 chars).
- Provide `@classmethod def make_df(cls) -> pd.DataFrame:` which returns a pandas DataFrame describing rows. At minimum the returned DataFrame must include an `الأداة` column.
- Prefer to call and return `reconstruct_from_base_df(df)` (see `reconstruction_utils.py`) so UTF-8, Unicode and phoneme/haraka derivation are handled consistently.

## Required / commonly used columns (as discovered in `reconstruction_utils.py`)
- Expected or auto-populated columns include: `الأداة`, `الفونيمات`, `الحركات`, `Unicode`, `UTF-8`, `عدد الفونيمات`, `نوع الحركة الأولى`, `UTF-8 للحروف`, `UTF-8 للحركات`.
- Engines are free to include additional descriptive columns used across sheets (e.g., `القالب/التركيب`, `النوع`, `مكوّنات`, `ملاحظات`). See `generic_nouns_engine.py` for a concrete example.

## Common patterns and examples
- Look at `sentence_generation_engine.py` — it composes outputs from multiple engines (AtfEngine, NafiEngine, PronounsEngine, etc.) and builds rich example sentences. This shows:
  - Engines can call other engines' `make_df()` to reuse lexical inventories.
  - Use helper functions to select the first few tokens for generation and then call `reconstruct_from_base_df()` on the composed DataFrame.
- `Main_engine.py` expects engines to be import-safe. Avoid top-level code in engines that raises on import. If an engine needs heavy initialization, wrap it in functions or lazy-load inside `make_df()`.

## Developer workflows (what to run locally)
- Create a virtualenv and install deps:
  - python -m venv .venv
  - source .venv/bin/activate
  - pip install -r requirements.txt
- Export all engines to Excel (run from repo root):
  - python Main_engine.py
  - Output: `full_multilayer_grammar.xlsx` in the current folder.
- Run the dev API server (if web app present):
  - python run_server.py --reload
  - Note: `run_server.py` launches `uvicorn "web_app.main:app"` — if the `web_app` package is missing, the server will fail.

## Integration points and external dependencies
- `reconstruction_utils.load_maps()` imports `phonemes_engine` and a harakat provider to build UTF-8 maps; engines that declare phoneme mappings must expose `UTF-8` columns compatible with that loader.
- The export path in `Main_engine.export_all()` is an Excel writer (pandas). Some downstream tooling expects the sheet names and columns; keep `SHEET_NAME` stable for existing sheets.

## Tips for safe edits by an AI agent
- Small, local changes are preferred: add a new engine file or modify `make_df()` content. Avoid global refactors that change discovery or import semantics.
- If adding imports used by `make_df()`, prefer importing inside the method to avoid breaking `Main_engine.collect_engines()` during module discovery.
- If `Main_engine` import fails when discovering modules, inspect engines for top-level side effects or missing dependencies.

## Where to look first (key files)
- `Main_engine.py` — module discovery and Excel export.
- `reconstruction_utils.py` — canonical normalization, column expectations and UTF-8 mapping.
- `sentence_generation_engine.py`, `generic_nouns_engine.py` — illustrative engine implementations.
- `run_server.py` — simple launcher for the FastAPI app (dev server via uvicorn).

## When in doubt
- Follow the engine contract above and mirror patterns from `generic_nouns_engine.py` or `sentence_generation_engine.py`.
- Keep changes small and run `python Main_engine.py` to validate that discovery and export succeed.

If you want, I can: (1) merge this into an existing instructions file if found, (2) run a quick validation step (attempt to import and call a single engine), or (3) expand examples for adding a new engine. Which would you like next?
