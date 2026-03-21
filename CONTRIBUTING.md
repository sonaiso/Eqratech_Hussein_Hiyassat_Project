# Contributing to FVAFK / Bayan

Thank you for your interest in contributing!  
This document explains how to set up the project locally and submit high-quality contributions.

---

## 📋 Table of Contents

1. [Prerequisites](#prerequisites)
2. [Local Setup](#local-setup)
3. [Project Structure](#project-structure)
4. [Running Tests](#running-tests)
5. [Coding Standards](#coding-standards)
6. [Adding an Engine](#adding-an-engine)
7. [Adding a Gate](#adding-a-gate)
8. [Submitting a Pull Request](#submitting-a-pull-request)

---

## Prerequisites

- Python **3.10+**
- Git
- (Optional) Coq — only needed when editing formal proofs in `coq/`

---

## Local Setup

```bash
# 1. Fork & clone
git clone https://github.com/<your-username>/Eqratech_Hussein_Hiyassat_Project.git
cd Eqratech_Hussein_Hiyassat_Project

# 2. Create a virtual environment
python3 -m venv .venv
source .venv/bin/activate   # Windows: .venv\Scripts\activate

# 3. Install the package with dev dependencies
pip install -e ".[dev]"

# 4. Verify everything works
pytest -q
```

Expected result: **497+ passed, 0 errors**.

---

## Project Structure

```
src/fvafk/       ← Core NLP pipeline (C1, C2a, C2b, syntax)
src/engines/     ← 66 linguistic engines (6 layers)
src/maqam_theory/← Maqam Theory gates (12 gates)
src/syntax_theory/← Graph-based syntax (ISN/TADMN/TAQYID)
app/models/      ← Pydantic models
web_app/         ← FastAPI application
tests/           ← pytest test suite
coq/Gates/       ← Coq formal proofs
docs/            ← Documentation
```

---

## Running Tests

```bash
# All tests
pytest -q

# Specific area
pytest tests/test_gate_sukun.py -v
pytest tests/test_pydantic_models.py -v

# With coverage
pytest --cov=src --cov-report=term-missing
```

---

## Coding Standards

| Rule | Detail |
|------|--------|
| **Type hints** | Required on all public functions and methods |
| **Docstrings** | Required on classes and public methods |
| **Column names** | Always use Arabic names (`الأداة`, `الفونيمات`, `الحركات`) |
| **Pydantic models** | Use `model_config = ConfigDict(...)` (Pydantic V2 style) |
| **No `eval()`** | Use `ast.literal_eval()` if dynamic parsing is needed |
| **SHEET_NAME** | Must be ≤ 31 characters (Excel limit) |
| **Layer imports** | Never import a higher layer from a lower layer |

---

## Adding an Engine

1. Create your file in `src/engines/{layer}/my_engine.py`
2. Inherit from the appropriate base:

```python
from engines.base import MorphologyEngine, EngineLayer
import pandas as pd

class MyNewEngine(MorphologyEngine):
    SHEET_NAME = "اسم_قصير"   # ≤ 31 chars
    LAYER = EngineLayer.MORPHOLOGY
    GROUP = "2.1"
    GROUP_AR = "الأفعال"

    @classmethod
    def make_df(cls) -> pd.DataFrame:
        data = {"الأداة": [...]}
        return pd.DataFrame(data)
```

3. Export from `src/engines/{layer}/__init__.py`
4. Add at least one test in `tests/engines/{layer}/test_my_engine.py`
5. Verify: `python engine_hierarchy.py --search MyNew`

---

## Adding a Gate (Maqam Theory)

1. Create `src/maqam_theory/gates/my_gate.py`
2. Inherit from `BaseGate` and implement all three abstract methods:

```python
from maqam_theory.gates.base_gate import BaseGate, GateType

class MyNewGate(BaseGate):
    def __init__(self):
        super().__init__(GateType.MY_TYPE)

    def can_activate(self, x) -> bool: ...
    def compute_satisfaction(self, x, y) -> float: ...  # returns [0, 1]
    def compute_cost(self, x, y, activated: bool) -> float: ...  # may be ∞
```

3. Add tests proving at least one **hard-fail** (∞) and one **soft-penalty** scenario.

---

## Documentation (required on major changes)

**For contributors and AI agents:** Any **major update** to the codebase (new stage, new additive layer, pipeline/orchestrator change, tightening pass, or change affecting architecture/roadmap) **must** be reflected in these three files in the same task:

| File | When to update |
|------|----------------|
| `docs/architecture/PIPELINE_MASTER_MEMORY.md` | Architecture, stages, additive layers, integration points; add a row to Section 8 Change Log |
| `docs/research/FVAFK_MASTER_EVOLUTION.md` | Engineering state, achievements, planned stages table, roadmap; add a row to Section F Engine Evolution Log |
| `docs/architecture/SCIENTIFIC_NEXT_PHASES.md` | Phase status (e.g. planned → implemented), phase descriptions |

- **Do not** consider the task complete until these docs are updated (or you explicitly report "not updated" with reason).
- Full rules and the required post-task report format are in **PIPELINE_MASTER_MEMORY.md Section 7** (Agent Operating Rules).
- Project rule file: **`.cursorrules`** (Cursor will use this to enforce doc updates on major changes).

---

## Submitting a Pull Request

1. Create a feature branch: `git checkout -b feat/my-feature`
2. Make your changes with focused commits
3. Ensure all tests pass: `pytest -q`
4. If the change is major (see Documentation above), update the three doc files and include the doc-update check in your PR description
5. Push and open a PR against `main`
6. Fill in the PR template describing:
   - What changed and why
   - Which tests cover the change
   - Any breaking changes
   - Documentation update check (if applicable)

---

*Questions? Open an issue or start a discussion on GitHub.*
