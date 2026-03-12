# Stage 5 — Gates and eligibility-based routing

## Purpose

Ensure pipeline layer **statuses reflect eligibility honestly**. Minimal or pathological inputs (e.g. single operator "وَ", "في", or "!") must not produce **fake success** for stages that have no eligible input (e.g. root extraction when all tokens are operators).

No analyzer logic is changed; only **orchestrator and adapter behavior** (gates, status assignment, `gates_applied`, warnings).

---

## Status model

| Status | Meaning |
|--------|--------|
| **success** | Stage ran and produced a full eligible result. |
| **partial** | Stage ran but result is incomplete or only partly eligible (e.g. no roots but tokens present; no sentence-level evidence). |
| **skipped** | Stage did not run because entry gates failed (ineligible input). |
| **failed** | Stage ran and raised an error or returned a hard failure. |
| **pass_through** | Placeholder / pass-through; no real run. |
| **missing** | No adapter or no upstream data. |

---

## Entry gates (lightweight)

Computed in `orchestrator/gates.py` from `_fvafk_result` and `original_text`:

| Gate | Meaning |
|------|--------|
| **has_text** | `original_text` (strip) non-empty. |
| **has_tokens** | `c2b.words` exists and `len > 0`. |
| **has_segmentable_word** | At least one token with length ≥ 2 and Arabic letters. |
| **has_morphology_candidate** | At least one word that is not closed-class only (not all operator/particle/pronoun), or at least one word has a root. |
| **has_root_candidate** | At least one word has non-null `root` (formatted or letters). |
| **has_syntax_candidate** | Multiple tokens, or `c2d.sentence_type`, or `syntax.links.isnadi` present. |
| **has_i3rab_evidence** | At least one word has non-empty `c2e.i3rab_text`. |
| **has_sentence_level_evidence** | Multiple tokens with `c2d.sentence_type`, or non-empty `rhetoric_signals`. |

Closed-class kinds (no root expected) for **has_morphology_candidate**: `operator`, `particle`, `pronoun` (and Arabic tags أداة, حرف, ضمير).

---

## Per-stage eligibility and status

### L8 — Root extraction

- **Entry gates:** `has_tokens`, `has_morphology_candidate`.
- If **no tokens** → `status=skipped`, `gates_applied` failed, warning.
- If **no morphology candidate** (all operator/particle/pronoun) → `status=skipped`, `gates_applied` failed, warning.
- Else: run as before; `status=success` if any word has root, else `status=partial`.
- **Minimum for "وَ":** skipped (one operator token, no root candidate).

### L9 — Wazn matching

- **Entry gates:** `has_root_candidate`.
- If **no root candidate** → `status=skipped`, `gates_applied` failed, warning.
- Else: run as before; `status=success` if any word has template/wazn, else `status=partial`.
- **Minimum for "وَ":** skipped.

### L11 — i3rab

- **Gates applied:** `has_tokens`, `has_i3rab_evidence`.
- No skip based on gates: i3rab can still output for particles (e.g. "حَرْفٌ مَبْنِيٌّ").
- `status=success` if any token has `i3rab_text`; else `status=partial`.
- **Minimum for "وَ":** success if c2e provides i3rab for و.

### L12 — Semantic / rhetorical

- **Entry gates:** `has_tokens`, `has_sentence_level_evidence`.
- `has_sentence_level_evidence` = (multiple tokens and c2d.sentence_type) or non-empty rhetoric_signals.
- If evidence weak (e.g. single token, no rhetoric) → `status=partial`; else `status=success`.
- **Minimum for "وَ":** partial (single token, no rhetoric).

---

## Implementation

- **`src/orchestrator/gates.py`:** `compute_gates(pipeline)`, `gate_entry(gate, passed, reason)`.
- **`src/orchestrator/stages/real_stages.py`:** L8, L9, L11, L12 call `compute_gates(pipeline)`, set `status` and `gates_applied` (and warnings when skipped).

---

## Definition of done (Stage 5)

Minimal/pathological inputs **do not** get fake success for ineligible stages:

- "وَ" → L8 and L9 **skipped**; L11 may success (i3rab for particle); L12 **partial** (weak sentence-level evidence).
- "في", "!" → same idea: no success for root/wazn when there is no eligible content.
- "يَا رَبِّ", "كَاتِبٌ" → L8/L9 success or partial when content and roots exist; L12 partial for single-token when no rhetoric.

See **docs/stage5_smoke_tests.md** for actual run results.
