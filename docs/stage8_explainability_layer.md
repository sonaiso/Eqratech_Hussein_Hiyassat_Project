# Stage 8 — Explainability and Evidence Rendering

## What Explainability Means in This Project

Explainability here is **exposing evidence and reasoning traces** from existing pipeline outputs. It does **not** generate new linguistic analysis. The goal is to answer:

- What did each stage conclude?
- Why did it conclude that (what evidence)?
- Why was a stage skipped, partial, or failed?
- How are final results grounded in prior layers?

All explanations are **derived strictly from** `layer_outputs` and `final_validation`. No new conclusions are invented.

## Explainability Object Model

Each explanation entry is a lightweight dict:

| Field | Description |
|-------|-------------|
| **claim** | Short human-readable claim (e.g. "Root extraction was skipped (no morphology candidate).") |
| **supporting_stage** | Stage ID that produced the evidence (e.g. L8_ROOT_EXTRACTION) |
| **evidence** | List of concrete evidence strings (e.g. "status=skipped", "words_count=1", "كَاتِبٌ: root=ك-ت-ب") |
| **confidence_hint** | Optional; how the conclusion was reached (e.g. "direct lexical match", "resolver + wazn/heuristic") |
| **limitation** | Optional; honest limit (e.g. "Gate: has_root_candidate false", "I3rab evidence is text-based") |
| **status** | One of: `supported` | `limited` | `absent` | `skipped` |

Example:

```json
{
  "claim": "Root(s) extracted from L8 (resolver/pattern).",
  "supporting_stage": "L8_ROOT_EXTRACTION",
  "evidence": ["words_count=1", "كَاتِبٌ: root=ك-ت-ب"],
  "confidence_hint": "resolver + wazn/heuristic",
  "limitation": null,
  "status": "supported"
}
```

## Evidence Sources by Stage

| Stage | What is extracted |
|-------|-------------------|
| **L4_OPERATORS** | operator_count, words with operator flag; "no operator tokens" when none matched |
| **L5_WORD_TYPING** | words_count, per-word kind |
| **L6_PHONOLOGY** | status, num_units, gates_count |
| **L7_SYLLABIFICATION** | status, syllable count |
| **L8_ROOT_EXTRACTION** | If skipped: gates_applied; else words with root; limitation when no roots |
| **L9_WAZN_MATCHING** | If skipped: gates_applied; else words with template/word_wazn |
| **L10_SYNTAX** | word_forms count, isnadi links; limitation: "Syntax depth may be shallow" |
| **L11_I3RAB** | token_results, i3rab_text present/absent; limitation: "text-based; no deep syntactic case reasoning" |
| **L12_SEMANTIC_RHETORICAL** | sentence_type, rhetoric_signals count; limitation: "surface/syntax-assisted" |
| **L13_VALIDATION** | global_validity, issue_count, final_confidence, issue codes; why validity/confidence |

If evidence is absent, the entry uses status `absent` or `limited` and does not invent data.

## Supported vs Limited Explanations

- **Supported**: Stage succeeded and produced concrete evidence (e.g. roots, wazn, i3rab_text). Claim and evidence list are filled; limitation may still be stated (e.g. i3rab is text-based).
- **Limited**: Stage ran but evidence is weak or partial (e.g. no operators matched, no roots for content words).
- **Skipped**: Stage was not run for eligibility reasons; evidence includes `status=skipped` and gates_applied; limitation explains the gate (e.g. "has_morphology_candidate false").
- **Absent**: No output from that stage (e.g. token_results_count=0).

## Where Explanations Appear

1. **rendered_output.artifacts.evidence_trace**  
   Full list of explanation entries (machine-readable) for all stages L4–L13.

2. **Detailed mode sections**  
   - **Evidence Trace Overview**: Which stages had decisive evidence; which were skipped.  
   - **Morphology Evidence**: L8/L9 claims, evidence, limitations.  
   - **I3rab Evidence**: L11 claim, evidence, source, limitation.  
   - **Validation Reasoning**: Why global_validity and final_confidence.  
   - **Skipped/Partial Reasoning**: Every skipped/limited/absent entry with reason.

3. **Compact mode**  
   Short "Why" lines when relevant (e.g. why root/wazn was skipped; validation limitation).

4. **Debug mode**  
   Stage-to-evidence trace summary (stage → status | claim snippet) and full evidence_trace in artifacts.

## Known Limits (Do Not Overclaim)

- **L10 Syntax**: Shallow; full dependency parse not guaranteed. Stated in L10 evidence limitation.
- **L11 I3rab**: Evidence is current c2e i3rab text payload; rule-based. No deep syntactic case reasoning. Stated in L11 evidence limitation.
- **L12 Rhetoric**: Detection is surface/syntax-assisted; deep semantic rhetoric not implemented. Stated in L12 evidence limitation.
- **L0/L1–L3**: Not included in evidence trace (focus on L4–L13). Can be extended later if needed.
- **Skipped stages**: Explained by gate/eligibility (e.g. has_root_candidate false), not by an imagined linguistic reason.

## Implementation

- **Module**: `src/orchestrator/explainability.py`  
  - `explanation_entry()`  
  - `extract_evidence_L4` … `extract_evidence_L13`  
  - `build_evidence_trace(pipeline)`  
- **Integration**: L14 presentation (`l14_presentation.py`) calls `build_evidence_trace(pipeline)` in all three modes and adds evidence sections (detailed), short why lines (compact), and trace summary (debug). Artifacts are set in all modes: `artifacts["evidence_trace"] = trace`.

## No New Stage ID

Stage 8 does not add a new pipeline stage (L0–L14 unchanged). Explainability is implemented as helpers plus rendering augmentation and artifacts attached to L14 output.
