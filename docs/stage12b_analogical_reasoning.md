# Stage L12B — Analogical Reasoning Layer

## Concept: Linguistic Qiyas (القياس)

In Arabic grammar and usul, **qiyas** (analogical reasoning) is the process of inferring a ruling or classification for a new case by analogy to a known case. The L12B layer applies a lightweight, deterministic form of this idea at the orchestration level: it uses **only** existing outputs from L5–L12 to propose inferred features and resolve ambiguity. It does not call external analyzers or mutate prior outputs.

## Why Analogical Reasoning Was Added

* **Ambiguity resolution** — When multiple linguistic interpretations exist (e.g. subject vs predicate), L12B can propose a preferred role based on simple heuristics.
* **Weak evidence** — When explicit evidence is weak (e.g. syntax role missing but root and wazn present), L12B proposes possible roles by pattern similarity.
* **Interpretability** — Inferences are structured (claim, reasoning_type, based_on, confidence_hint, limitation) so downstream layers and explainability can surface them.
* **Future probabilistic reasoning** — The layer prepares the pipeline for later probabilistic or ML-based reasoning by establishing a clear place for “inferred” vs “observed” evidence.

## Heuristics Currently Implemented

1. **Morphological analogy**  
   If `wazn` matches a فاعل-type pattern and word_typing is noun, propose: “Likely active participle (ism fa'il) analogically similar to corpus patterns.” Status: strong.

2. **Pattern similarity inference**  
   If root and wazn exist but L10 has no syntactic links/roles, propose: “Possible syntactic role based on pattern similarity.” Status: weak.

3. **Conditional rhetorical inference**  
   If sentence_type is شرط (conditional), propose: “Causal temporal framing inference from conditional sentence.” Status: proposed.

4. **I3rab fallback analogy**  
   If a token has `i3rab_text` but no structured `syntactic_function` or `governing_factor`, add: “Role inferred via surface i3rab analogy.” Status: weak.

Ambiguity resolutions (e.g. first content word as preferred subject in SV order) are produced when multiple inferences exist.

## What Is NOT Implemented

* **Deep ML reasoning** — No neural or probabilistic models.
* **Corpus lookup** — No external lexicon or corpus for analogical matching.
* **Linguistic engine changes** — No modifications to morphology, syntax, i3rab, or rhetoric analyzers; L12B only reads their outputs.
* **Destructive mutation** — Prior layer outputs are never overwritten; L12B only adds artifacts.

## Output Shape

* `transformation_result.analogical_inferences` — List of `{ token, claim, reasoning_type, based_on, confidence_hint, limitation, status }`.
* `transformation_result.ambiguity_resolutions` — List of `{ token, competing_roles, preferred_role, reason, confidence_hint }`.
* `transformation_result.analogical_summary` — `{ total_inferences, strong_count, weak_count }`.

## Status and Gates

* **success** — At least one inference produced.
* **partial** — Stage ran but no inference possible.
* **skipped** — Upstream tokenization failed (no tokens).
* **failed** — Runtime exception.

Gates used: `has_tokens`, `has_morphology_candidate`, `has_syntax_candidate`.

## Future: Probabilistic Reasoning Roadmap

L12B is designed so that later:

* A probabilistic or ML module could replace or extend the deterministic heuristics.
* Confidence scores could be attached to each inference.
* Ambiguity resolution could use a ranking model instead of fixed rules.
* The same output schema (inferences, resolutions, summary) can be preserved.

## Placement in Pipeline

L12B runs **after** L12_SEMANTIC_RHETORICAL and **before** L13_VALIDATION. Validation and presentation can then use L12B artifacts for consistency checks and reporting.
