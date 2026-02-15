# FVAFK Project Status

Single source of truth for **current progress** and **roadmap**. Updated at sprint boundaries and when major features land.

**Last updated:** 2026-02-01

---

## 1. Current progress

### 1.1 Baseline

| Item | Status |
|------|--------|
| **Tests** | 269 passing; CI green |
| **Pipeline** | C1 → C2a → C2b working in CLI |
| **Phonology V2** | Integrated; `--phonology-v2`, `--phonology-v2-details`, `--phonology-v2-witnesses` |
| **WordForm** | Implemented (`word_form.py`, `word_form_builder.py`, `word_form_validator.py`) |
| **ISNADI** | V1 and V1.1 implemented; **not yet in CLI output** |
| **Structure** | `src/fvafk/`, `tests/`, `docs/` |

### 1.2 What’s done (by phase)

- **Phase 1 (Infrastructure):** Segment inventory, orthography, C1 encoder, FormCodecV2, Trace V1, gate framework.
- **Phase 2 (Gates):** All 10 gates + GateWasl; orchestrator.
- **Phase 3 (Morphology):** Word boundaries (Plan A), root extraction, pattern matcher, awzan loader, pattern analyzer, word classifier, features V1, operators catalog.
- **Phase 4 (Syntax):** WordForm bridge, ISNADI linker (in package); **TADMINI/TAQYIDI and parser not implemented; syntax not in CLI.**
- **Phase 5 (Constraints):** Not started.
- **Phase 6 (Integration):** CLI and C2b integrated; no corpus evaluation or C2c yet.

### 1.3 Known gaps

- Syntax not exposed in CLI (no `result["syntax"]`).
- TADMINI and TAQYIDI linkers not implemented.
- No single SyntacticParser; no constraint modules or validator.
- No corpus F1/UAS/LAS evaluation.
- Coq and Plan B word boundaries out of scope for current roadmap.

---

## 2. Roadmap

The **full task checklist** (Parts 1–6) is in **`docs/MASTER_PLAN_CHECKLIST.md`**. The **sprint plan** is in **`ENHANCED_ROADMAP.md`**.

| Sprint | Weeks | Focus | Outcome |
|--------|--------|--------|---------|
| 1 | 1–2 | Part 1: packaging + ISNADI in CLI | pyproject.toml, bayan-fvafk, Pydantic models, CLI JSON (tokens, WordForm, ISNADI), 10+ tests |
| 2 | 3–4 | Part 2 (+ 2.5): phonology + Coq | Gates, OrthographyAdapter rules, syllabifier, Coq skeletons; semantic gates base |
| 3 | 5–6 | Part 3: morphology + corpus | Plan B boundaries, PatternCatalog bridge, morph_flags, gold corpus, F1 ≥ 0.85 |
| 4 | 7–8 | Part 4: syntax + events | ISNADI/TADMINI/TAQYIDI, SyntacticParser, EventExtractor, UAS/LAS |
| 5 | 9–10 | Part 5: constraints | 5 constraints + Amil-Sign, ConstraintValidator, Coq predicates |
| 6 | 11–14 | Part 6: integration + ops | Full pipeline, corpus eval, proof mode, FastAPI, CI/CD, docs |

**Critical path:** Part 1 (Sprint 1) → Part 2 → Part 3 → Part 4 → Part 5 → Part 6.

---

## 3. Related docs

- **docs/MASTER_PLAN_CHECKLIST.md** – Full 6-part checklist (foundation, phonology, semantics, morphology, syntax, constraints, integration); use for GitHub issues.
- **ENHANCED_ROADMAP.md** – Sprint deliverables, success metrics, weeks 1–14.
- **docs/PLAN_MERGE_ANALYSIS.md** – Gaps/overlaps between current state and 6-phase plan.
- **WHERE_WE_ARE_VS_PLAN.md** – Phase-by-phase status vs master plan.
- **project_deleverables.md** – Living deliverables (Arabic + English).
- **src/fvafk/phonology/INTEGRATION_PLAN.md** – Phonology V2 integration + post-integration milestones.

---

## 4. This week (from ENHANCED_ROADMAP)

1. Wire syntax into CLI: WordForm + ISNADI → `result["syntax"]`.
2. Add integration tests for `result["syntax"]`.
3. PROJECT_STATUS.md (this file) and ENHANCED_ROADMAP.md created.
4. INTEGRATION_PLAN.md updated with post-integration milestones.
5. project_deleverables.md updated (269 tests, syntax next).
6. Create GitHub milestones (Sprint 1–6) and top 20 issues.

---

*For detailed acceptance criteria and GitHub issue list, see ENHANCED_ROADMAP.md.*
