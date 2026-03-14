# Pre-Stage-13 Readiness Audit

## Purpose

The Pre-Stage-13 Readiness Audit is a **diagnostic structural audit** run once per pipeline run **before** Stage L13 (Validation). It is **not** a new linguistic stage. It evaluates the **reliability and maturity** of upstream evidence sources so that downstream fusion or validation can adapt.

## Why Fusion Requires Evidence Maturity

* **Fusion** (e.g. combining root, wazn, syntax, i3rab into a single coherent interpretation) depends on how much each source can be trusted. If root extraction is missing or syntax has failed, fusion should not overstate confidence.
* **Readiness** answers: “How much can we rely on this run’s evidence for cognitive fusion or validation?” High readiness means most key sources (roots, wazn, operators, word typing, syntax, i3rab, etc.) are available and structurally adequate. Low readiness means critical sources are missing or weak, so the pipeline should run in a **safe, conservative** mode (e.g. L13 or a future L13 cognitive-fusion stage avoids strong claims).

## Difference Between Linguistic Correctness and Structural Readiness

* **Linguistic correctness** — Whether a root, wazn, or i3rab label is correct according to grammar or a gold standard. The audit does **not** judge that.
* **Structural readiness** — Whether the pipeline **produced** usable outputs from each source (availability), how deep those outputs are (structural_depth 0..3), and what limitations are documented (e.g. “i3rab textual only”, “syntax shallow”). The audit only evaluates this. A run can be “HIGH” readiness but still contain linguistic errors; conversely, “LOW” readiness means the **evidence structure** is weak, not necessarily that every label is wrong.

## What the Audit Produces

* **readiness_score** — Weighted mean of (fusion_weight × availability) over all audited sources. Range 0..1.
* **readiness_band** — HIGH (≥0.75), MEDIUM (0.55–0.74), LOW (&lt;0.55).
* **sources** — For each source (ROOT_EXTRACTION, PATTERN_MATCH, OPERATOR_DETECTION, WORD_TYPING, MORPHO_FEATURES, SYNTAX, I3RAB, SEMANTIC_RHETORICAL, ANALOGICAL_REASONING): availability, structural_depth (0..3), decision_reliability, known_limitations, fusion_weight.
* **blocking_issues** — e.g. “no root extraction”, “no tokens”, “syntax failed completely”.
* **advisory_notes** — e.g. “rhetoric evidence weak”, “i3rab textual only”, “analogical reasoning heuristic-based”.

Integration:

* Result is stored in **pipeline["pre_stage13_audit"]**.
* **pipeline["meta"]["fusion_readiness"]** is set to the readiness_band.
* If **readiness_band == "LOW"**, **pipeline["meta"]["conservative_fusion_mode"]** is set to True so that L13 (or a future cognitive fusion stage) can run in safe, conservative mode.

## Structural Depth (0..3)

* **0** — Missing (source failed or empty).
* **1** — Surface heuristics (e.g. rhetoric, analogical reasoning as currently implemented).
* **2** — Structured but partial (e.g. syntax links, i3rab token_results, operators).
* **3** — Structurally modeled reasoning (e.g. root extraction, wazn matching with full pattern match).

## Default Fusion Weights (Conceptual)

| Source               | Reliability        | Default weight |
|----------------------|--------------------|----------------|
| ROOT_EXTRACTION      | strong             | 0.95           |
| PATTERN_MATCH        | strong             | 0.85           |
| OPERATOR_DETECTION   | strong             | 0.80           |
| WORD_TYPING          | moderate           | 0.65           |
| MORPHO_FEATURES      | moderate           | 0.60           |
| SYNTAX               | moderate_limited   | 0.55           |
| I3RAB                | moderate_textual   | 0.50           |
| SEMANTIC_RHETORICAL  | weak               | 0.35           |
| ANALOGICAL_REASONING | supportive         | 0.40           |

(Exact weights and availability logic are implemented in `pre_stage13_audit.py`.)

## Future Evolution When Syntax / I3rab Deepen

* When **syntax** gains full dependency trees and richer links, the SYNTAX source can be raised to structural_depth 3 and its fusion_weight or reliability can be increased. The audit will then reflect higher readiness when syntax is available.
* When **i3rab** becomes fully structured (case/mood, governing factor, reasoning steps) instead of text-only, the I3RAB source can move to depth 3 and higher weight; advisory_notes can stop adding “i3rab textual only” when that limitation is gone.
* The same audit interface (run_audit → readiness_score, readiness_band, sources, blocking_issues, advisory_notes) can be kept; only the per-source depth and availability logic need to be updated as the pipeline matures.
