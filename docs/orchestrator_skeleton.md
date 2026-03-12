# Orchestrator Skeleton (Stage 3)

## What the orchestrator currently does

- **Accepts** raw Arabic text and optional metadata (request_id, source, run_mode).
- **Builds** a canonical pipeline object per the Stage 2 contract (`pipeline.schema.json`).
- **Initializes** `layer_outputs` with all 15 fixed stage keys (L0_INPUT … L14_PRESENTATION).
- **Runs** stages in fixed order; each stage returns a `LayerOutput` dict that is stored under its `layer_id`.
- **Supports** skipped / partial / pass-through / failed stages; failed stages produce a valid LayerOutput with `status: "failed"` and errors.
- **Preserves** `original_text` and does not overwrite unrelated layers.
- **Logs** stage started/finished, status, and warning/error counts (via Python `logging`).

**Stage 4 (done):** L1–L12 are wired to existing FVAFK/engines via thin adapters; L0, L13, L14 remain placeholder. See `docs/stage4_smoke_tests.md`.

---

## Stage registry order

Stages run in this deterministic order:

| Index | Layer ID | Layer name |
|-------|----------|------------|
| 0 | L0_INPUT | Input acquisition |
| 1 | L1_NORMALIZATION | Normalization |
| 2 | L2_TOKENIZATION | Tokenization |
| 3 | L3_SEGMENTATION | Segmentation |
| 4 | L4_OPERATORS | Particles / operators |
| 5 | L5_WORD_TYPING | Word typing / routing |
| 6 | L6_PHONOLOGY | Phonology / CV |
| 7 | L7_SYLLABIFICATION | Syllabification |
| 8 | L8_ROOT_EXTRACTION | Root hypothesis extraction |
| 9 | L9_WAZN_MATCHING | Wazn matching |
| 10 | L10_SYNTAX | Syntax / sentence relations |
| 11 | **L11_I3RAB** | **i3rab** |
| 12 | L12_SEMANTIC_RHETORICAL | Semantic / rhetorical |
| 13 | L13_VALIDATION | Validation / hypothesis pruning |
| 14 | L14_PRESENTATION | Presentation / rendering |

---

## Placeholder behaviour

- **L0_INPUT**: `status: "success"`; `transformation_result` and `next_input` carry the raw text; no real input adapter.
- **L1–L10, L12–L14**: `status: "pass_through"`; each produces a valid `LayerOutput` with a short warning (e.g. “Placeholder; adapter not connected”) and passes `next_input` from the previous stage.
- **L11_I3RAB**: Explicit independent layer; `status: "missing"` with a note that the i3rab adapter is not connected. No invented analysis.

**Clarity note:** L11_I3RAB is now connected (Stage 4): it is filled from existing `c2b.c2e.i3rab_text` per word; `transformation_result.token_results[]` carries `i3rab_text` and `surface`.

No stage invents linguistic results; all outputs are structurally valid per `layer_output.schema.json`.

---

## What Stage 4 will connect

Stage 4 will:

- Replace placeholders with adapters that call existing modules (e.g. normalizer, tokenizer, root extractor, wazn matcher, syntax, c2e i3rab, etc.).
- Use the same `BaseStage` interface and registry; only the stage implementations change.
- Preserve the same pipeline contract and layer IDs.

---

## How to run a minimal pipeline skeleton

**Option 1 — Script (recommended):**

```bash
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py "إِنَّ اللَّهَ غَفُورٌ"
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --summary "إِنَّ اللَّهَ غَفُورٌ"
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --json "إِنَّ اللَّهَ غَفُورٌ"
```

**Option 2 — From Python:**

From the project root, with `PYTHONPATH=src`:

```bash
python3 -c "
from orchestrator import run
import json
p = run('إِنَّ اللَّهَ غَفُورٌ')
print(json.dumps({
    'pipeline_version': p['pipeline_version'],
    'request_id': p['request_id'],
    'original_text': p['original_text'],
    'stage_order': p['stage_order'],
    'layer_summary': {k: v.get('status') for k, v in p['layer_outputs'].items()}
}, indent=2, ensure_ascii=False))
"
```

Or run with logging to see stage started/finished:

```bash
PYTHONPATH=src python3 -c "
import logging
logging.basicConfig(level=logging.INFO)
from orchestrator import run
p = run('إِنَّ اللَّهَ غَفُورٌ')
print('L11_I3RAB status:', p['layer_outputs']['L11_I3RAB']['status'])
"
```

Expected: a pipeline object with `metadata`, `original_text`, `stage_order`, and `layer_outputs` for all 15 stages; L0 has `success`, L11 has `missing`, others have `pass_through` (or `failed` only if a stage raises).

---

## Files added (Stage 3)

- `src/orchestrator/` — orchestrator package
  - `types.py` — STAGE_ORDER, LayerOutputDict, PipelineDict, status helpers
  - `errors.py` — PipelineError, StageError
  - `builders.py` — build_empty_pipeline, build_layer_output, get_previous_output
  - `stages/base_stage.py` — BaseStage abstract interface
  - `stages/placeholders.py` — PlaceholderStage, L0 and L11 stubs, STAGE_NAMES
  - `stage_registry.py` — get_default_registry(), get_stage_by_id(), get_stage_order()
  - `pipeline_orchestrator.py` — run_pipeline(), run(), insert_layer_output()
  - `validation.py` — validate_pipeline_shape(), validate_layer_output_shape()
  - `__init__.py` — exports run, run_pipeline, get_default_registry, get_stage_order, STAGE_ORDER
- `scripts/run_orchestrator_skeleton.py` — runnable script: `PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py "text" [--summary|--json]`
- `docs/orchestrator_skeleton.md` — this document

---

## Schema awareness

- Builders produce dicts that match the Stage 2 contract (required keys, fixed stage IDs, allowed status values).
- `validation.validate_pipeline_shape()` and `validate_layer_output_shape()` perform lightweight checks (required keys, valid status, fixed layer IDs). Full JSON Schema validation is not applied here and can be added later.
