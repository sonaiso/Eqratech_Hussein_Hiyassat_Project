# Stage 12 — Gender & Number Engine (Pass 1)

## Purpose and scope

**Purpose:** Enrich tokens with gender and number features for downstream agreement checking and case refinement (Stage 17 v2, iʿrāb agreement rules).

**Scope (Pass 1):**

- Gender: MASCULINE, FEMININE, UNKNOWN (noun/verb/particle family-safe).
- Number: SINGULAR, DUAL, PLURAL_SOUND_M, PLURAL_SOUND_F, PLURAL_BROKEN, UNKNOWN.
- Agreement: agreement_candidates, agreement_status (agreed | conflict | unresolved), agreement_rule; in pipeline order L12 runs before Stage 15, so Pass 1 leaves agreement unresolved unless Stage 15 is available (e.g. post-hoc run).
- Tamyiz: tamyiz_relation marks token_id of the following noun when the token is a number/quantity lexeme; full tamyiz iʿrāb is deferred to Stage 17 v2.

**Position:** After L14_JAMID_MUSHTAQ, before L10_SYNTAX. Output under `lo["L12_GENDER_NUMBER"]`.

---

## Gender detection rules

| Rule | Condition | Result |
|------|-----------|--------|
| G1 | Noun-family, normalized surface ends with ة (taa marbuta) | FEMININE, 0.9, taa_marbuta |
| G2 | Noun-family, wazn in feminine patterns (e.g. مفعلة, فعيلة) | FEMININE, 0.8, wazn_feminine_pattern |
| G3 | Noun-family, no stronger feminine rule | MASCULINE, 0.7, default_masculine_noun |
| G4 | Verb-family: use L8B only; no inference from ت | UNKNOWN or conservative, l8b_verb_gender_unknown |
| G5 | Noun-family, L14 JAMID, surface ends with ة | FEMININE, 0.85, jamid_or_proper_noun_taa_marbuta |
| — | Particle-family | UNKNOWN, 0.3, particle_no_gender |

Bare final "ت" alone is not treated as a universal feminine marker.

---

## Number detection rules

| Rule | Condition | Result |
|------|-----------|--------|
| N1 | Noun-family, normalized surface ends with ان (alef + noon) | DUAL, dual, 0.85, dual_suffix_an |
| N2 | Noun-family, ends with ون | PLURAL_SOUND_M, sound_plural, 0.85 |
| N3 | Noun-family, ends with ات | PLURAL_SOUND_F, sound_plural, 0.85 (+ FEMININE if default) |
| N4 | Noun-family, wazn in broken plural set (أفعال, فعول, مفاعل, etc.); فِعَال excluded (ambiguous with كِتَاب) | PLURAL_BROKEN, broken_plural, 0.8 |
| N5 | No dual/plural match | SINGULAR, singular, 0.7, default_singular |

Suffix **ين** is not forced to dual or plural without additional evidence (logged in ambiguity_log).

---

## Agreement detection rules (Pass 2 / when Stage 15 available)

- **A1 SIFA:** Use Stage 15 SIFA links; compare gender/number of mawsuf and sifa → agreed | conflict | unresolved.
- **A2 SUBJ:** Use Stage 15 SUBJ links; Arabic VSO-aware (do not auto-mark number mismatch when verb precedes subject).
- **A3 IDAFA:** No gender transfer; each token keeps own features.

In Pass 1 pipeline order, L12 runs before L10/Stage 15, so agreement_status is left **unresolved** unless dependency_links are present (e.g. post-hoc run).

---

## Tamyiz relation rules

- **T1:** Token in number-lexeme set (واحد، اثنان، ثلاثة … عشرة، عشرون، مئة، ألف) and next token noun-family → tamyiz_relation = next token_id.
- **T2:** Token in quantity-lexeme set (كيلو، لتر، متر, etc.) and next token noun-family → tamyiz_relation = next token_id.

Stage 12 only marks the relation; full tamyiz iʿrāb is deferred to Stage 17 v2.

---

## Output schema

```json
{
  "status": "success",
  "token_features": [
    {
      "token_id": "0",
      "surface": "مَدْرَسَة",
      "gender": "FEMININE",
      "number": "SINGULAR",
      "number_type": "singular",
      "gender_rule": "taa_marbuta",
      "number_rule": "default_singular",
      "agreement_candidates": [],
      "agreement_status": "unresolved",
      "agreement_rule": null,
      "tamyiz_relation": null,
      "confidence": 0.8,
      "evidence_sources": ["surface"]
    }
  ],
  "agreement_summary": { "total": 1, "agreed_count": 0, "conflict_count": 0, "unresolved_count": 1 },
  "coverage": "gender_number_tamyiz_pass1",
  "ambiguity_log": []
}
```

---

## Integration

- **Stage 15:** When dependency_links exist, agreement_candidates and agreement_status can be filled (SIFA, SUBJ).
- **Stage 17:** May consume token_features for agreement-aware case refinement in v2.
- **SECTION 4k:** Added in analyze_sentence.py and l14_presentation.py (surface | gender | number | number_type | agreement_status | confidence).

---

## Known limitations

- Agreement is unresolved in standard pipeline (L12 runs before Stage 15).
- فِعَال wazn excluded from broken plural to avoid false positive on كِتَاب.
- ين left ambiguous (dual vs oblique plural) without extra evidence.
- Verb gender from L8B only; no inference from present-tense ت.

---

## Deferred to Pass 2

- Full agreement resolution when L12 runs after Stage 15 or via a dedicated agreement pass.
- Additional feminine/plural patterns and edge cases.
- Tamyiz iʿrāb resolution (Stage 17 v2).
