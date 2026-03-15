# Discourse Frame Builder (Additive Layer)

## Overview

The **DISCOURSE_FRAME_BUILDER** is an additive enrichment layer that builds discourse frames from connectives, L10B clause structure, and L12/L12B hints. It does **not** modify syntax, causal i'rab, rhetorical detection, validation, or fusion math. It is:

- **Additive** — only adds `DISCOURSE_FRAME_BUILDER` to layer outputs
- **Heuristic** — rule-based; no ML or deep semantics
- **Non-blocking** — pipeline continues if the layer is skipped
- **Confidence-agnostic** to pipeline core — does not change global validity or fusion confidence

## Input Sources

The builder uses **only** existing internal sources:

- **Shared connectives layer** — `classify_connective(token)` (no raw CSV/JSON in the builder)
- **L10B** — `main_clause_type`, `clause_units`, `dependency_nodes[].connective_group`
- **L12B** — `analogical_inferences[]` with `reasoning_type == "discourse"` and `connective_group`

It does **not** re-read source API JSON files or duplicate connective normalization.

## Tightening Rationale

Earlier behaviour could produce frames that were too broad or shallow. The tightening pass:

1. **Distinguishes connective detection from discourse framing** — recognising a connective token is not enough for a strong frame; clause or discourse support is required where possible.
2. **Scope hint policy** — scope is set from evidence: token-local, phrase-level, clause-level, sentence-level (no broad scope unless justified).
3. **Weak-frame handling** — weak unsupported frames are kept with a clear limitation string rather than overconfident labels; optionally they can be suppressed to reduce noise (current policy: keep with limitation).
4. **Explanation vs causation** — default to FRAME_EXPLANATION; upgrade to FRAME_CAUSATION only when L12/L12B suggests cause/effect.

## Frame Types and Rules

### Conditional (Rule 1)

- **STRONG** only if: `connective_group == conditional` **and** (L10B `main_clause_type == conditional` or clause_units support conditional).
- **MEDIUM** if: connective conditional exists and L12B discourse support exists, but clause support is weak.
- **WEAK** if: only token recognition (e.g. from L10B node), with no clause support. Limitation: *"conditional frame inferred from connective recognition only"*.

### Adversative (Rule 2)

- Requires `connective_group == adversative`.
- **STRONG** never from token recognition alone. Prefer sentence/discourse support from L12B.
- If only token present: frame may be built as **WEAK** with limitation *"adversative frame lacks downstream contrast support"*.

### Explanation vs Causation (Rule 3)

- If `connective_group == explanation_causation`: default to **FRAME_EXPLANATION**.
- Upgrade to **FRAME_CAUSATION** only if there is real support (e.g. L12B analogical discourse hint suggesting cause/effect, or sentence-level interpretation).
- If unclear: remain FRAME_EXPLANATION with limitation *"causation vs explanation not fully disambiguated"*.
- Do **not** over-produce FRAME_CAUSATION.

### Negation (Rule 4)

- Negation frame allowed when negation connective exists.
- **STRONG** only if sentence-level effect is visible or structurally grounded; otherwise **MEDIUM** or **WEAK**.
- This layer does not claim full polarity reasoning.

### Scope Hints (Rule 5)

Allowed values:

- **token-local** — only token recognition, no structural support
- **phrase-level** — very local attachment only
- **clause-level** — L10B clause unit or conditional structure exists
- **sentence-level** — broad sentence-wide discourse effect only

Do not use broad scope unless justified.

### Weak-Frame Suppression (Rule 6)

- If a detected connective/discourse hint is too weak and unsupported:
  - Either keep the frame as **WEAK** with a clear limitation, or
  - Suppress the frame entirely if it would add noise.
- Prefer fewer, cleaner frames over many weak noisy ones. Current implementation keeps WEAK frames with limitations so downstream (e.g. Clause Engine) can filter.

## Output Shape

```
lo["DISCOURSE_FRAME_BUILDER"] = {
    "frames": [
        {
            "trigger": str,
            "frame_type": str,
            "scope_hint": str,
            "confidence": "strong" | "medium" | "weak",
            "connective_group": str,
            "limitation": str | null
        }
    ],
    "frame_count": int,
    "frame_types": [str],
    "coverage_hint": str,
    "strong_frame_count": int,
    "weak_frame_count": int
}
```

## Presentation

- **SECTION 4e** (detailed): trigger, frame_type, scope_hint, confidence, limitation per frame; summary counts and coverage_hint.
- **Debug mode**: frame_count, strong_frame_count, weak_frame_count, frame_types, coverage_hint.
- **Compact mode**: list only strong/medium frame types to avoid clutter from weak frames.

## Integration

- Invoked **after** L12B_ANALOGICAL_REASONING in the pipeline (same loop as other additive enrichments).
- Explainability: `extract_evidence_discourse_frames(lo)` reports evidence quality (connective + clause/discourse alignment, limitations).

## Limitations

- Does not implement full clause segmentation or discourse parsing.
- Does not override syntax or i'rab.
- Explanation vs causation remains conservative; disambiguation is partial.
