# Pipeline Contract

## 1. Why the pipeline contract exists

The pipeline contract defines a **single canonical JSON structure** for:

- The **full pipeline run** (top-level object) so every run has a consistent shape regardless of entry point (CLI, script, future API).
- **Each layer’s output** so the orchestrator and downstream stages consume a uniform structure (status, received_input, transformation_result, raw_module_output, validation, warnings, next_input).
- **Validation and presentation** so we can report global validity, confidence, issues, and rendered output without inventing new formats.

The contract is **adapter-facing**: existing modules are not rewritten; adapters produce and consume this structure. Partial stages, skipped stages, and missing stages are first-class (status: partial | skipped | missing). i3rab is an **explicit independent stage** (L11) with its own payload shape.

---

## 2. Top-level pipeline object

The global pipeline run is a single JSON object with **fixed required fields** and optional sections.

### Required

| Field | Type | Description |
|-------|------|-------------|
| `pipeline_version` | string | Semver, e.g. `"1.0.0"`. |
| `request_id` | string | Unique id for this run, e.g. `"REQ_000001"`. |
| `created_at` | string | ISO-8601 timestamp. |
| `original_text` | string | Raw input text. |
| `stage_order` | array of string | Ordered list of stage IDs (see below). |
| `layer_outputs` | object | Map of stage ID → LayerOutput. **Only fixed keys** are used (see §3). |

### Optional

| Field | Type | Description |
|-------|------|-------------|
| `source` | object | Entry point and mode (e.g. `entrypoint`, `mode`, `input_type`). |
| `normalized_text` | string \| null | Output of normalization stage if run. |
| `metadata` | object | e.g. `language`, `notes`, `tags`. |
| `final_validation` | object | Global validation result (§6). |
| `rendered_output` | object | Presentation result (§7). |

### Fixed stage IDs (for `stage_order` and `layer_outputs`)

- `L0_INPUT` — Input acquisition  
- `L1_NORMALIZATION` — Normalization  
- `L2_TOKENIZATION` — Tokenization  
- `L3_SEGMENTATION` — Segmentation  
- `L4_OPERATORS` — Particles / operators / functional gating  
- `L5_WORD_TYPING` — Word typing / routing  
- `L6_PHONOLOGY` — Phonology / CV extraction  
- `L7_SYLLABIFICATION` — Syllabification  
- `L8_ROOT_EXTRACTION` — Root hypothesis extraction  
- `L9_WAZN_MATCHING` — Wazn matching  
- `L10_SYNTAX` — Syntax / sentence relations  
- `L11_I3RAB` — i3rab (explicit independent stage)  
- `L12_SEMANTIC_RHETORICAL` — Semantic / rhetorical classification  
- `L13_VALIDATION` — Validation / hypothesis pruning  
- `L14_PRESENTATION` — Presentation / rendering  

**Example top-level (minimal):**

```json
{
  "pipeline_version": "1.0.0",
  "request_id": "REQ_000001",
  "created_at": "2025-03-15T12:00:00Z",
  "source": {
    "entrypoint": "fvafk.cli",
    "mode": "cli",
    "input_type": "text"
  },
  "original_text": "إِنَّ اللَّهَ غَفُورٌ",
  "normalized_text": null,
  "metadata": { "language": "ar", "notes": [], "tags": [] },
  "stage_order": [
    "L0_INPUT", "L1_NORMALIZATION", "L2_TOKENIZATION", "L3_SEGMENTATION",
    "L4_OPERATORS", "L5_WORD_TYPING", "L6_PHONOLOGY", "L7_SYLLABIFICATION",
    "L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING", "L10_SYNTAX", "L11_I3RAB",
    "L12_SEMANTIC_RHETORICAL", "L13_VALIDATION", "L14_PRESENTATION"
  ],
  "layer_outputs": {
    "L0_INPUT": {},
    "L1_NORMALIZATION": {},
    "L2_TOKENIZATION": {}
  },
  "final_validation": {},
  "rendered_output": {}
}
```

Stages not yet run may be absent from `layer_outputs` or present with `status: "missing"` or `"skipped"`. The contract does not require every stage to exist or succeed.

---

## 3. Standard layer output object

Every stage produces a **LayerOutput** object. This is the value type for each key in `layer_outputs`.

### Required

| Field | Type | Description |
|-------|------|-------------|
| `layer_id` | string | Fixed stage id, e.g. `"L2_TOKENIZATION"`. |
| `layer_name` | string | Human-readable name, e.g. `"Tokenization Layer"`. |
| `stage_index` | integer | Zero-based index (0–14). |
| `status` | string | One of: `success` \| `partial` \| `skipped` \| `failed` \| `pass_through` \| `missing`. |

### Optional (all nullable / omit if not used)

| Field | Type | Description |
|-------|------|-------------|
| `received_input` | object | Input passed to this stage. |
| `reused_module` | object | `file`, `symbol`, `mode` (direct \| adapter \| pass_through). |
| `rules_applied` | array of string | Rule identifiers applied. |
| `gates_applied` | array of GateEntry | Gate checks (see §5). |
| `transformation_result` | object | **Canonical** output for downstream; structure is layer-specific. |
| `raw_module_output` | object | **Original** output from wrapped module (backward compatibility). |
| `validation` | object | Layer-local validation: `status`, `confidence`, `issues`. |
| `warnings` | array of string | Warnings. |
| `errors` | array of string | Error messages. |
| `next_input` | object | Explicit payload for next stage (may equal `transformation_result`). |
| `hypotheses` | array of Hypothesis | Competing analyses when stage has multiple (see §4). |

- **transformation_result**: normalized, stable shape for downstream layers.  
- **raw_module_output**: unchanged output from the existing module; adapters may copy it here.  
- **next_input**: must be explicit so the orchestrator can pass it without guessing.

---

## 4. Status model

Allowed **layer status** values:

| Value | Meaning |
|-------|--------|
| `success` | Stage completed and produced a usable result. |
| `partial` | Stage ran but result is incomplete or best-effort. |
| `skipped` | Stage was not run (e.g. eligibility gate failed). |
| `failed` | Stage ran but failed (errors present). |
| `pass_through` | Stage did nothing; input passed through. |
| `missing` | Stage not implemented or not connected yet. |

Allowed **global validity** (in `final_validation.global_validity`):

- `success` \| `partial` \| `failed` \| `unknown`

---

## 5. Gate model

A **gate** is a conditional check used inside a layer (e.g. “eligible for root extraction”).

**GateEntry** (optional in `gates_applied`):

| Field | Type | Description |
|-------|------|-------------|
| `gate` | string | Gate identifier. |
| `status` | string | `passed` \| `failed` \| `skipped`. |
| `reason` | string | Optional explanation. |

**Example:**

```json
{
  "gate": "eligible_for_root_extraction",
  "status": "passed",
  "reason": "word_type=MUSHTAQ"
}
```

---

## 6. Validation model

**Layer-local validation** (inside a LayerOutput):

- `status`: same as LayerStatus (optional).  
- `confidence`: number in [0,1] or null.  
- `issues`: array of ValidationIssue.

**Global validation** (`final_validation`):

- `global_validity`: `success` \| `partial` \| `failed` \| `unknown`.  
- `final_confidence`: number or null.  
- `issues`: array of issues (same shape as below).

**ValidationIssue:**

| Field | Type | Description |
|-------|------|-------------|
| `code` | string | e.g. `MISSING_PREREQUISITE`. |
| `message` | string | Human-readable message. |
| `layer_id` | string | Optional. |
| `severity` | string | Optional: `error` \| `warning` \| `info`. |

**Example:**

```json
{
  "code": "MISSING_PREREQUISITE",
  "message": "Syllabification skipped because phonology output was unavailable.",
  "layer_id": "L7_SYLLABIFICATION",
  "severity": "warning"
}
```

---

## 7. Hypothesis model

When a stage produces **multiple competing analyses** (e.g. segmentation, root, wazn, syntax, i3rab, rhetoric), it may expose them as **hypotheses**.

**Hypothesis** (optional in `hypotheses`):

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | e.g. `"h1"`. |
| `score` | number | Optional score. |
| `label` | string | e.g. `"preferred"`, `"alternate"`. |
| `analysis` | object | Layer-specific analysis. |

**Example:**

```json
"hypotheses": [
  {
    "id": "h1",
    "score": 0.91,
    "label": "preferred",
    "analysis": { "root": "غ-ف-ر", "pattern": "فَعُول" }
  }
]
```

Hypotheses are **optional**; not every stage uses them.

---

## 8. i3rab payload model (L11)

i3rab is **Stage 11** and has its own explicit contract for `transformation_result`. The current code may not populate every field; nulls and partial output are allowed.

**Recommended shape for `L11_I3RAB.transformation_result`:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `token_results` | array | Yes | One entry per token. |
| (per token) `token_id` | string | Yes | e.g. `"t1"`, `"t2"`. |
| (per token) `surface` | string | Yes | Surface form. |
| (per token) `governing_factor` | string \| null | No | e.g. `"إنَّ"`. |
| (per token) `i3rab_position` | string \| null | No | e.g. `"اسم إن"`, `"خبر مرفوع"`. |
| (per token) `i3rab_case_or_mood` | string \| null | No | e.g. `"منصوب"`, `"مجزوم"`. |
| (per token) `i3rab_marker` | string \| null | No | e.g. `"الفتحة"`, `"الضمة"`. |
| (per token) `estimated_reasoning` | string \| null | No | Short explanation. |
| (per token) `confidence` | number \| null | No | 0–1. |
| (per token) `dependencies_used` | array of string | No | e.g. `["operators", "syntax", "word_typing"]`. |
| (per token) `status` | string | No | e.g. `"partial"`, `"success"`. |
| (per token) `i3rab_text` | string \| null | No | Full i3rab phrase when available (current CLI field). |

**Example (partial i3rab stage):**

```json
{
  "token_results": [
    {
      "token_id": "t1",
      "surface": "اللَّهَ",
      "governing_factor": "إنَّ",
      "i3rab_position": "اسم إن",
      "i3rab_case_or_mood": "منصوب",
      "i3rab_marker": "الفتحة",
      "estimated_reasoning": "preceded by إنَّ",
      "confidence": null,
      "dependencies_used": ["operators", "syntax", "word_typing"],
      "status": "partial",
      "i3rab_text": "اسْمُ إِنَّ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ"
    }
  ]
}
```

This is a **contract shape**. If the current implementation only provides `i3rab_text`, adapters can fill that and leave other fields null until the pipeline is extended.

---

## 9. Rendered output (presentation)

**rendered_output** is a **surface representation only**. It does not replace `layer_outputs`.

| Field | Type | Description |
|-------|------|-------------|
| `mode` | string | `compact` \| `detailed` \| `debug`. |
| `summary` | string | Short summary text. |
| `sections` | array | Optional section objects (e.g. per-stage summaries). |
| `artifacts` | object | Optional paths or blobs (e.g. CSV path, report path). |

---

## 10. Examples

### Example 1: Successful stage (L2_TOKENIZATION)

```json
{
  "layer_id": "L2_TOKENIZATION",
  "layer_name": "Tokenization Layer",
  "stage_index": 2,
  "status": "success",
  "received_input": { "normalized_text": "إِنَّ اللَّهَ غَفُورٌ" },
  "reused_module": { "file": "src/fvafk/c2b/word_boundary.py", "symbol": "WordBoundaryDetector", "mode": "direct" },
  "rules_applied": [],
  "gates_applied": [],
  "transformation_result": {
    "tokens": ["إِنَّ", "اللَّهَ", "غَفُورٌ"],
    "spans": [{"start": 0, "end": 3}, {"start": 4, "end": 10}, {"start": 11, "end": 17}]
  },
  "raw_module_output": {},
  "validation": { "status": "success", "confidence": 1.0, "issues": [] },
  "warnings": [],
  "errors": [],
  "next_input": { "tokens": ["إِنَّ", "اللَّهَ", "غَفُورٌ"], "spans": [] }
}
```

### Example 2: Skipped stage (L8_ROOT_EXTRACTION)

```json
{
  "layer_id": "L8_ROOT_EXTRACTION",
  "layer_name": "Root hypothesis extraction",
  "stage_index": 8,
  "status": "skipped",
  "received_input": { "token": "إِنَّ", "kind": "operator" },
  "reused_module": { "file": "src/fvafk/c2b/root_resolver/resolver.py", "symbol": "RootResolver", "mode": "adapter" },
  "gates_applied": [
    { "gate": "eligible_for_root_extraction", "status": "failed", "reason": "kind=operator" }
  ],
  "transformation_result": {},
  "raw_module_output": null,
  "validation": { "status": "skipped", "confidence": null, "issues": [] },
  "warnings": ["Token is operator; root extraction skipped."],
  "errors": [],
  "next_input": {}
}
```

### Example 3: Partial i3rab stage (L11_I3RAB)

```json
{
  "layer_id": "L11_I3RAB",
  "layer_name": "i3rab",
  "stage_index": 11,
  "status": "partial",
  "received_input": { "words": [], "operators": [], "syntax": {} },
  "reused_module": { "file": "src/fvafk/c2e/enricher.py", "symbol": "MorphEnricher", "mode": "adapter" },
  "transformation_result": {
    "token_results": [
      {
        "token_id": "t1",
        "surface": "اللَّهَ",
        "governing_factor": "إنَّ",
        "i3rab_position": "اسم إن",
        "i3rab_case_or_mood": "منصوب",
        "i3rab_marker": "الفتحة",
        "estimated_reasoning": "preceded by إنَّ",
        "confidence": null,
        "dependencies_used": ["operators", "word_typing"],
        "status": "partial",
        "i3rab_text": "اسْمُ إِنَّ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ"
      }
    ]
  },
  "raw_module_output": {},
  "validation": { "status": "partial", "confidence": null, "issues": [] },
  "warnings": ["Some tokens have no i3rab; dependencies incomplete."],
  "errors": [],
  "next_input": {}
}
```

---

## 11. Backward compatibility with current modules

- **No analyzer rewrites:** The contract does not require changing existing analyzers. Adapters will call current modules and map their results into LayerOutput (and, for L11, into the i3rab transformation_result shape).
- **raw_module_output:** Always reserve a place for the **exact** output of the wrapped module so existing consumers (or tests) can still rely on it.
- **Optional fields:** Almost everything except `layer_id`, `layer_name`, `stage_index`, and `status` is optional so that partial or placeholder stages can omit transformation_result, next_input, or validation.
- **Fixed keys in layer_outputs:** Using only the 15 stage IDs (L0_INPUT … L14_PRESENTATION) keeps orchestration and validation simple; stages that did not run can be absent or present with `status: "missing"` or `"skipped"`.
- **CLI compatibility:** The current CLI builds a `result` dict (c1, c2a, c2b, c2d, rhetoric_signals, etc.). That dict can be **embedded** under `raw_module_output` for the relevant stages, and an adapter can also fill `transformation_result` and `next_input` from the same data so the pipeline object remains the single source of truth for Stage 3 and beyond.

---

## 12. Schema files

| File | Purpose |
|------|---------|
| `schemas/common_defs.schema.json` | Shared enums and definitions (LayerStatus, GateEntry, ValidationIssue, etc.). |
| `schemas/layer_output.schema.json` | Standard LayerOutput shape (required + optional fields, hypotheses). |
| `schemas/pipeline.schema.json` | Top-level pipeline run (required + optional), fixed `layer_outputs` keys, `final_validation`, `rendered_output`. |

The orchestrator in Stage 3 will use these schemas to construct and validate the pipeline object and each layer output.
