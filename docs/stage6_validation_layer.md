# Stage 6 — Real validation layer (L13)

## Purpose

L13_VALIDATION is now a **real stage** that checks cross-layer consistency from **existing stage outputs only**, emits structured validation issues, assigns **global_validity**, and optionally **final_confidence**. No analyzer logic is changed; validation is lightweight, structured, and honest.

---

## What L13 checks

1. **Prerequisite consistency**
   - L8 or L9 marked **success** but L2 has no tokens → `MISSING_PREREQUISITE` (warning).
   - Stage marked success with empty evidence where skip/partial would be more appropriate (see morphology/syntax below).

2. **Morphology consistency**
   - L8 **success** but all roots null (and tokens exist) → `EMPTY_SUCCESS` / root-related (warning).
   - L9 **success** but no template/word_wazn in any word → `EMPTY_SUCCESS` (warning).

3. **Syntax / i3rab consistency**
   - L10 **failed** → `INCONSISTENT_STATUS` (info).
   - L11 **success** but no `i3rab_text` in any token_result → `I3RAB_MISSING` (warning).
   - L11 **success** with empty `token_results` while L2 has tokens → `EMPTY_SUCCESS` (warning).

4. **Semantic consistency**
   - L12 **success** with single token and no rhetoric → `WEAK_SENTENCE_EVIDENCE` (info).

5. **Placeholder hygiene**
   - L14 is not visible to L13 (L13 runs before L14); no L14 check. Placeholder stages are not reported as errors unless inconsistent with status.

---

## Issue format (Stage 2 contract)

Each issue has:

- **code**: string (e.g. `EMPTY_SUCCESS`, `MISSING_PREREQUISITE`, `I3RAB_MISSING`, `WEAK_SENTENCE_EVIDENCE`, `INCONSISTENT_STATUS`).
- **message**: short description.
- **layer_id**: layer concerned (e.g. `L8_ROOT_EXTRACTION`).
- **severity**: `info` | `warning` | `error`.

Supported codes (used when observed):

- `MISSING_PREREQUISITE`
- `EMPTY_SUCCESS`
- `INCONSISTENT_STATUS`
- `I3RAB_MISSING`
- `WEAK_SENTENCE_EVIDENCE`
- `ROOT_MISSING` / `WAZN_MISSING` (via EMPTY_SUCCESS messages)

---

## Global validity

Computed from issue severities:

| Value      | Condition |
|-----------|-----------|
| **invalid** | At least one **error**. |
| **weak**    | At least two **warnings** (no error). |
| **partial** | One warning, or any **info**. |
| **valid**   | No issues, or only info (and we treat as valid in current logic; see below). |

Current logic in code: `error_count >= 1` → invalid; `warning_count >= 2` → weak; `warning_count >= 1 or info_count >= 1` → partial; else valid.

---

## Final confidence (optional)

Simple heuristic, only when `global_validity != "invalid"`:

- `final_confidence = max(0, min(1, 1.0 - 0.25*errors - 0.12*warnings - 0.02*info))`.
- Stored in L13 `transformation_result` and in top-level `final_validation.final_confidence`.
- Probabilistic confidence fusion is **deferred**.

---

## L13 output shape

- **status**: `success` or `partial` (partial if any warning/error in issues).
- **transformation_result**:
  - `global_validity`
  - `issues` (list of {code, message, layer_id, severity})
  - `validated_layers_summary` (layer_id → status)
  - `issue_count`
  - `final_confidence` (optional)
- **next_input**: carries `global_validity` and `validated_layers_summary` for L14.

Top-level **final_validation** is populated from L13’s transformation_result (global_validity, issues, validated_layers_summary, final_confidence).

---

## Interaction with Stage 5 (gates)

With Stage 5 eligibility routing, L8 and L9 are **skipped** when there is no morphology/root candidate (e.g. input "وَ", "في"). So L13 often sees coherent output and may report **valid** and no issues. L13 would still flag **EMPTY_SUCCESS** or **MISSING_PREREQUISITE** if a layer ever reported success with empty or inconsistent data (e.g. regression or different entry path).

---

## Deferred

- Probabilistic confidence fusion.
- Deep linguistic validation (e.g. grammar rules).
- Blocking the whole pipeline on validation (we do not block; we only set global_validity and issues).

---

## Implementation

- **`src/orchestrator/l13_validation.py`**: `run_validation(layer_outputs)`, `RealL13Validation` stage.
- **`src/orchestrator/stage_registry.py`**: L13 uses `RealL13Validation()` instead of placeholder.
- **`src/orchestrator/pipeline_orchestrator.py`**: After L13 runs, copy L13’s transformation_result into `pipeline["final_validation"]`.
