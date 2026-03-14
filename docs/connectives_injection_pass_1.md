# Connectives Injection Pass 1

## Why a shared connectives layer was added

- **Single source of truth:** Connectives (أدوات الشرط، النفي، التفسير والتعليل، الاستدراك) are loaded once from local JSON and normalized into a stable schema.
- **Reuse across stages:** L4, L10B, L11B, L12, L12B (and later stages) can use the same lookup API instead of each parsing raw API JSON.
- **Separation of concerns:** The layer only loads, normalizes, classifies, and exposes lookups. It does not perform dependency parsing, i'rab assignment, or sentence classification. Those stay in their respective stages.

## Separation of concerns design

- **Connectives layer:** Loads from `data/connectives_api/*.json`, normalizes into internal schema, builds in-memory index, exposes `get_connective_by_token`, `get_connectives_by_group`, `classify_connective`, `is_conditional_connective`, etc.
- **Stages:** Optionally call the lookup API and attach **hints** (e.g. `connective_group`, `connective_hint`) to their outputs. No stage reads raw JSON directly; no stage owns the data format.
- **Explainability:** Reads pipeline outputs (e.g. L10B nodes that already carry `connective_group`) and emits claims that reference the "shared connectives knowledge", not raw files.

## Categories included in Pass 1

| Source file                     | category_id | Category (Arabic)           | Canonical group              |
|---------------------------------|------------|-----------------------------|------------------------------|
| connectives_category_3.json     | 3          | أدوات الشرط                 | conditional                  |
| connectives_category_18.json   | 18         | أدوات النفي                 | negation                     |
| connectives_category_23.json   | 23         | أدوات التفسير والتعليل      | explanation_causation        |
| connectives_category_29.json   | 29         | أدوات الاستدراك             | adversative                  |

## Normalized schema

Each connective entry (after normalization) has:

- `token` — original form (e.g. with harakat)
- `normalized_token` — form with combining diacritics stripped for lookup
- `category_id` — from API (3, 18, 23, 29)
- `category_name` — Arabic name of the category
- `group` — canonical group: `conditional` | `negation` | `explanation_causation` | `adversative`
- `source_file` — e.g. `connectives_category_3.json`
- `raw` — full original API item for traceability only; stages must not depend on `raw` shape.

## Lookup API

- `load_connectives_knowledge(force_reload=False)` — returns list of normalized entries (cached).
- `get_connective_by_token(token)` — returns one normalized entry or `None`; diacritic-insensitive.
- `get_connectives_by_group(group)` — returns all entries for that group.
- `classify_connective(token)` — same as `get_connective_by_token`; returns stable schema only.
- `is_conditional_connective(token)` — bool.
- `is_negation_connective(token)` — bool.
- `is_explanatory_or_causal_connective(token)` — bool.
- `is_adversative_connective(token)` — bool.

## Which stages may consume it

- **L4 operators:** May add `connective_group` and `connective_hint` to word items (optional).
- **L10B deep syntax:** May add `connective_group` and `connective_hint` to dependency nodes as weak structural/discourse hints.
- **L11B causal i'rab:** May use connective class as weak context only; must not depend on raw source format.
- **L12 / L12B:** May use `connective_group` as semantic/discourse hint (e.g. in analogical inferences).

Consumption is **optional and minimal**: hints only, not hard grammatical facts.

## What is intentionally NOT done yet

- No full clause-boundary or sentence-type classification from connectives alone.
- No change to L11/L11B i'rab rules based on connective type.
- No loading of other connectives categories (e.g. 5, 9, 17, 19, 21, 25, 31) in this pass; the design allows adding them later without redesign.
- Present passive / tense from connectives is out of scope.

## Adding more categories later

- Add more `(filename, category_id, category_name)` entries in `loader.SUPPORTED_FILES`.
- If a new category does not map to an existing group, add a new canonical group in `models` and `CATEGORY_ID_TO_GROUP`.
- No change to the lookup API contract; stages that only use `group` and `category_name` keep working.

## Module layout

```
src/orchestrator/connectives/
  __init__.py   — public API
  models.py     — schema, GROUP_*, CATEGORY_ID_TO_GROUP
  loader.py     — load from data/connectives_api, normalize
  lookup.py     — cache, index, get_* / is_* helpers
```

## Tests

- `tests/orchestrator/test_connectives_knowledge_layer.py`: load, normalize, lookup by token/group, diacritic-insensitivity, group classification, L10B consumption, pipeline smoke.
