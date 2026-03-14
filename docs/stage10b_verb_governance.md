# L10B-V — Verb Governance Engine

## Purpose

L10B-V upgrades deep syntax (L10B) by modelling Arabic verb transitivity and argument structure. It runs **inside** L10B after the initial dependency graph is built and before causal iʿrāb (L11B). It does not add a new pipeline stage.

## Components

### 1. Verb Governance Knowledge Base

- **File:** `data/verb_governance.json`
- Each entry: `lemma`, `transitivity`, `objects`, `prepositional_required`, `required_preposition` (if applicable), `semantic_class`.
- Example: `ضرب` transitive 1 object; `عاش` intransitive; `انتمى` intransitive with required PP `إلى`; `أعطى` transitive 2 objects; `ظن` mental_verb 2 objects; `صيّر` transformational 2 objects.

### 2. Argument Expectation Engine

- **Function:** `infer_expected_arguments(verb_node)` in `src/orchestrator/verb_governance.py`.
- **Input:** `verb_node` with at least `lemma` (or `root`).
- **Output:** `expected_subject`, `expected_objects`, `expected_pp_relations`, `optional_roles`.

### 3. Dependency Boosting and Penalties

- **Intransitive + direct object** → mark structure anomaly; add to `illegal_arguments`.
- **Verb requires preposition** and PP exists with correct ḥarf jar → boost (alignment score, trace).
- **Verb expects N objects** and fewer found → add to `missing_arguments`.
- **Transitive with candidate object** → promote candidate object edge to status `probable`.

### 4. Parse Strength Update

- `parse_strength = base_dependency_resolution + governance_alignment_score - structural_conflict_penalty`, clamped to [0, 1].
- `base_dependency_resolution` = resolved_edges / (resolved_edges + candidate_edges + 1) from L10B.

### 5. Explainability

- `syntax_reasoning_trace`: list of strings, e.g. "Verb governance rule applied: transitivity alignment", "Verb governance rule applied: promoted candidate object to probable", "Verb governance rule applied: intransitive verb has direct object — anomaly".
- L14 detailed mode and explainability trace include verb governance summary and trace.

### 6. Output Extension (syntax_summary)

- `verb_governance_applied`: bool
- `governance_alignment_score`: float
- `missing_arguments`: list of strings
- `illegal_arguments`: list of strings

`transformation_result` also includes `syntax_reasoning_trace` (list of strings).

## Tests (5 example sentences)

1. **عاش الرجل** — no object expected; intransitive; no illegal.
2. **ضرب الرجل الحجر** — valid one object.
3. **انتمى الرجل الوطن** — anomaly: missing required PP إلى (or illegal DO).
4. **أعطى المعلم الطالب كتاباً** — valid double object.
5. **ظننتُ الطالبَ مجتهداً** — mental verb; valid two-complement structure.

## Dependencies

- L10B uses L2, L4, L5, L8, L9, L10. Verb governance uses L8 (root) and L9 (template for verb detection). If `data/verb_governance.json` is missing, governance is skipped and default summary fields are set.
