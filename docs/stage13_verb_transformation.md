# Stage 13 — Verb Transformation Engine

## Purpose

`L13_VERB_TRANSFORMATION` is a real stage in `STAGE_ORDER` that runs after `L14_JAMID_MUSHTAQ` and before `L12_GENDER_NUMBER`.

Its job is to generate a conservative base paradigm for confirmed verbs using:

- `L8_ROOT_EXTRACTION` for root
- `L8B_VERB_BAB_GOVERNANCE` for `bab`, `root_type`, `voice`, and `tense_mapping`
- `L14_JAMID_MUSHTAQ` as a verb-confirmation gate

It does not rewrite downstream syntax, i'rab, or analyzer output. It only adds structured transformation data under `lo["L13_VERB_TRANSFORMATION"]`.

## Scope

Pass 1 supports:

- base past active
- base present active
- base past passive
- base present passive
- masdar derivation
- imperative derivation

Only tokens confirmed as verbs by strong `L8B` evidence or `L14_JAMID_MUSHTAQ == VERB` are included.

## Output Schema

```python
lo["L13_VERB_TRANSFORMATION"] = {
    "status": "success",
    "verb_transformations": [
        {
            "token_id": str,
            "surface": str,
            "root": str | None,
            "root_type": str | None,
            "bab": str | None,
            "bab_status": str,
            "base_past_active": str | None,
            "base_present_active": str | None,
            "base_past_passive": str | None,
            "base_present_passive": str | None,
            "masdar": str | None,
            "masdar_wazn": str | None,
            "imperative": str | None,
            "tense_of_surface": str,
            "voice_of_surface": str,
            "transformation_confidence": float,
            "transformation_rule": str,
            "limitations": list[str],
        }
    ],
    "transformation_summary": {
        "total_verbs": int,
        "fully_transformed": int,
        "partially_transformed": int,
        "untransformed": int,
    },
    "coverage": "verb_transformation_pass1",
}
```

## Rules

### T1 — Past active

- Source: `L8B.tense_mapping.past_pattern`
- If root is triliteral, apply it to the wazn with `apply_root_to_wazn()`
- If application is not possible, keep the template only

### T2 — Present active

- Source: `L8B.tense_mapping.present_pattern`
- Same root-application rule as T1

### T3 — Past passive

- `صحيح سالم` triliteral roots use `فُعِلَ`
- Other supported roots infer conservatively from passive evidence when possible
- If not derivable, add `passive_past_not_derivable`

### T4 — Present passive

- Source: `L8B.tense_mapping.present_passive_pattern`
- Applied conservatively through the same root-to-wazn helper

### T5 — Masdar derivation

Current bab to masdar-wazn mapping:

| Bab | Masdar wazn |
|-----|-------------|
| `فَعَلَ-يَفْعُلُ` | `فَعْل` |
| `فَعَلَ-يَفْعِلُ` | `فَعْل` |
| `فَعِلَ-يَفْعَلُ` | `فَعَل` |
| `فَعُلَ-يَفْعُلُ` | `فُعُول` |
| `فَعَّلَ` | `تَفْعِيل` |
| `أَفْعَلَ` | `إِفْعَال` |
| `تَفَعَّلَ` | `تَفَعُّل` |
| `انْفَعَلَ` | `انْفِعَال` |
| `افْتَعَلَ` | `افْتِعَال` |
| `اسْتَفْعَلَ` | `اسْتِفْعَال` |

If bab is unknown or unmapped, the stage does not invent a masdar.

### T6 — Imperative derivation

Current imperative templates:

| Bab | Imperative template |
|-----|---------------------|
| `فَعَلَ-يَفْعُلُ` | `اُفْعُلْ` |
| `فَعَلَ-يَفْعِلُ` | `اِفْعِلْ` |
| `فَعِلَ-يَفْعَلُ` | `اِفْعَلْ` |
| `فَعُلَ-يَفْعُلُ` | unsupported in Pass 1 |
| `فَعَّلَ` | `فَعِّلْ` |
| `أَفْعَلَ` | `أَفْعِلْ` |
| `تَفَعَّلَ` | `تَفَعَّلْ` |
| `انْفَعَلَ` | `انْفَعِلْ` |
| `افْتَعَلَ` | `افْتَعِلْ` |
| `اسْتَفْعَلَ` | `اسْتَفْعِلْ` |

### T7 — Root application helper

`apply_root_to_wazn(root, wazn)`:

- parses root like `ض-ر-ب` into `["ض", "ر", "ب"]`
- replaces `ف` with radical 1
- replaces `ع` with radical 2
- replaces `ل` with radical 3
- preserves vowels and extra template letters

## Confidence and Fallbacks

- resolved bab + strong coverage: high confidence
- non-resolved bab: confidence capped conservatively
- weak roots: transformed, but tagged with `weak_root_transformation_approximate`
- quadrilateral roots: not generated in Pass 1
- null root: all generated fields remain null with confidence `0.0`

## Integration Point

`L13_VERB_TRANSFORMATION` is available to downstream stages through `layer_outputs`, especially:

- `L12_GENDER_NUMBER`
- `L10B_DEEP_SYNTAX`
- Stage 15 `DEPENDENCY_SYNTAX_BUILDER`
- `L17_RULE_BASED_I3RAB`

Pass 1 does not require downstream consumption changes. It only makes the paradigm available.

## Presentation

The stage is exposed in:

- `scripts/analyze_sentence.py` as `SECTION 4l — VERB TRANSFORMATIONS`
- `src/orchestrator/l14_presentation.py` detailed output as `SECTION 4l — VERB TRANSFORMATIONS`

## Known Limitations

- quadrilateral transformation is deferred
- weak-root handling is conservative and approximate
- unsupported or unknown bab values do not receive invented forms
- no dual/plural/person inflection generation in Pass 1
- no downstream i'rab consumption changes yet

## Deferred To Pass 2

- broader augmented-form coverage
- fuller passive derivation for weak roots
- person/number/gender inflection sets
- richer masdar ambiguity modeling
- downstream Stage 17 consumption for verb-form-aware reasoning
