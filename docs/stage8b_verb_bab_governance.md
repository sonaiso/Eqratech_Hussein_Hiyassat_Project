# L8B — Verb Bab / Governance Profile

## Purpose

L8B runs immediately after **L8_ROOT_EXTRACTION** and before **L9_WAZN_MATCHING**. It ensures that verbs do not flow into later stages as "bare roots only". Each verb candidate receives a **structured governance profile** that tells later layers:

- What **type of root** it is (صحيح سالم, معتل مثال, etc.)
- What **verb/bab class** it belongs to (trilateral, quadrilateral, derived)
- Whether it is **لازم** or **متعدي**
- How many **objects** it expects
- Whether it **requires a preposition**
- Whether it belongs to **special classes** (أفعال القلوب, أفعال التحويل)

## Why root alone is insufficient

Root extraction (L8) gives only the consonantal root. Syntax and iʿrāb need to know **governance**: e.g. whether a verb can take a direct object, or requires a preposition, or is mental/transformational. L8B enriches the pipeline without replacing L8 or L9.

## Allowed inputs

- **L2** tokenization (tokens)
- **L5** word typing (kind)
- **L8** root extraction (root per word)

No re-running of raw analyzers; no external services.

## Output shape

- **verb_governance_profiles**: list of per-token profiles including **bab**, **bab_status**, **bab_confidence**, **tense_mapping** (past_pattern, present_pattern, present_passive_pattern), plus token_id, surface, root, root_type, verb_class, voice, tense_family, transitivity, objects, prepositional_required, required_prepositions, governance_family, special_class, voice_evidence, expected_subject_role, confidence, status.
- **governance_summary**: verb_count, resolved_profiles, candidate_profiles, unresolved_profiles, **excluded_non_verbs** (count of tokens not given a profile).
- **voice_evidence**: `{ "voice": "active"|"passive"|"unknown", "rule": rule_name, "confidence": 0.05–0.98 }`.
- **expected_subject_role**: `"فاعل"` (active) or `"نائب فاعل"` (passive); `None` for non-verbs.

## Supported root types (triliteral)

- صحيح سالم  
- صحيح مهموز  
- صحيح مضعف  
- معتل مثال  
- معتل أجوف  
- معتل ناقص  
- معتل لفيف مقرون  
- معتل لفيف مفروق  
- unknown / quadrilateral_candidate  

## The six canonical abwab

L8B supports these triliteral past–present **bab** values (from a small lexical KB `data/verb_abwab.json`):

1. **فَعَلَ-يَفْعُلُ** (e.g. رَسَمَ)
2. **فَعَلَ-يَفْعِلُ** (e.g. ضَرَبَ)
3. **فَعَلَ-يَفْعَلُ** (e.g. نَفَعَ)
4. **فَعِلَ-يَفْعَلُ** (e.g. فَرِحَ)
5. **فَعُلَ-يَفْعُلُ** (e.g. قَرُبَ)
6. **فَعِلَ-يَفْعِلُ** (e.g. حَسِبَ)

Also: **derived_form_candidate**, **unknown**. Bab is resolved only when the root (or surface) is found in the abwab KB; otherwise `bab="unknown"`, `bab_status="unknown"`.

## Why bab matters in governance

Bab (الباب) identifies the vowel pattern of the past and present stems. It constrains possible conjugations and helps downstream stages (e.g. L9 wazn, L11 iʿrāb) interpret form. L8B does not replace L9; it adds a first-scope bab hint when lexical evidence exists.

## Present mapping

For each **resolved** canonical bab, L8B fills **tense_mapping**:

- **past_pattern**: the past stem (e.g. فَعَلَ, فَعِلَ, فَعُلَ).
- **present_pattern**: the corresponding present (e.g. يَفْعُلُ, يَفْعِلُ, يَفْعَلُ).

If bab is unknown, both are `"unknown"`.

## Present passive pattern mapping

**present_passive_pattern** is set conservatively and is **descriptive only** (not full present-passive voice detection):

- **صحيح سالم / مهموز / مضعف**: e.g. يُفْعَلُ.
- **معتل أجوف**: middle weak → يُقَالُ-style.
- **معتل ناقص / معتل مثال**: final weak → يُدْعَى-style.
- **فوق الثلاثي (derived_form_candidate)**: e.g. يُسْتَعْمَلُ.

**Limitation:** This is a pattern field only; L8B does not yet perform full present-tense passive voice detection.

## Supported bab (first scope)

- **Resolved:** one of the six canonical abwab above when root is in `data/verb_abwab.json`.
- **unknown** when no KB match or insufficient evidence.
- **derived_form_candidate** for quadrilateral/derived when applicable.

## Governance families

- intransitive_basic  
- intransitive_prepositional  
- basic_transitive  
- double_object  
- triple_object  
- mental_verb  
- transformational_verb  
- unknown  

## Special classes

- أفعال القلوب (e.g. ظن، حسب، خال، زعم)  
- أفعال التحويل (e.g. صيّر، جعل، اتخذ)  
- null  

## Verb candidacy gating

L8B only creates governance profiles for **strong verb candidates**. Root alone or KB match alone is insufficient.

- **Root alone is insufficient:** A token may have a root (from L8) but be a noun, participle, or operator. L8B does not treat every rooted token as a verb.
- **KB match alone is insufficient:** If the token is clearly non-verbal in context (e.g. definite noun, participle ending in اً, preposition phrase), a lexical KB match does not force a governance profile. The token must pass the verb candidacy gate.
- **L8B is only for verbs:** Governance profiles are for finite verbs or very strong verb candidates. Nouns, derived nouns, participles (unless with strong finite-verb evidence), adverbs, objects, and prepositional phrases are **excluded** from `verb_governance_profiles` (they are not listed at all; they are counted in `excluded_non_verbs`).
- **Why this tightening:** Previously, L8B over-generated profiles for non-verb tokens (e.g. الظَّالِمُ، كَالْحَجَرِ، أَحَداً، مُخْلِصاً)، causing inflated verb_count and noisy downstream effects in L10B, L11B, and L13. The candidacy gate keeps L8B low-noise and verb-focused.

A token receives a profile only if at least one of: **(A)** L5 explicitly classifies it as verb (and surface does not look like participle/noun), **(B)** strong finite-verb surface evidence (e.g. فَعَلَ, فُعِلَ), **(C)** strong passive-voice evidence, or **(D)** trusted KB match and compatibility with verbal morphology. Downstream stages (L10B, L11B, L12B, L13) consume only the filtered list of profiles.

## Bab confidence and abwab KB

- **bab_confidence** bands: 0.90 (exact KB match), 0.75 (strong surface-compatible), 0.55 (weak candidate), 0.20 (unknown); clamped [0.05, 0.98].
- **Abwab KB:** `data/verb_abwab.json` — root (normalized) → bab string. Seed entries only (رسم, ضرب, نفع, فرح, قرب, حسب). No overclaim when root is missing or not in KB.

## Lexical knowledge base

- **Path:** `data/verb_governance.json`
- Entries: lemma → transitivity, objects, prepositional_required, required_preposition(s), governance_family, special_class.
- Used by L8B and by L10B-V verb governance pass; L8B precomputes profiles for the whole pipeline.

## Confidence strategy

- [0.05, 0.98]; never 1.0 or 0.0.
- 0.92: exact KB match + compatible root/surface.
- 0.80: good root match.
- 0.65: candidate bab or governance.
- 0.40: weak inference.
- 0.20: unresolved but minimally informed.

## Passive voice morphological detector (past only)

L8B includes a **passive voice morphological detector** for past verbs. It is deterministic and rule-based.

- **Rule A — sound trilateral**: فَعَلَ → فُعِلَ (first consonant damma, second kasra) → `voice=passive`, `rule=sound_trilateral_passive`, confidence 0.92.
- **Rule B — hollow**: قَالَ → قِيلَ (root middle weak; surface كسرة then ي/و then لَ) → `hollow_passive`, confidence 0.70.
- **Rule C — defective**: أَتَى → أُتِيَ (last radical weak; damma, kasra, يَ) → `defective_passive`, confidence 0.70.
- **Rule D — derived**: أَكْرَمَ → أُكْرِمَ (first vowel damma, vowel before last kasra) → `derived_passive`, confidence 0.80.

When `voice == "passive"`, the profile sets **expected_subject_role** = `"نائب فاعل"` and may set **governance_family** to `passive_transitive_frame` for transitive verbs. L10B/L11B/L13 use this as evidence (فاعل vs نائب فاعل). Present-tense passive is out of scope in this pass.

Confidence bands: 0.92 (exact فُعِلَ), 0.80 (derived), 0.70 (hollow/defective), 0.40 (weak), 0.20 (unresolved); clamped [0.05, 0.98].

## Relation to L10B and L11B

- **L10B** (deep syntax) and **L10B-V** (verb governance inside L10B) can use L8B profiles as an optional stronger evidence source (e.g. expected objects, required preposition).
- **L11B** (causal iʿrāb) can use L8B to avoid assigning impossible objects (e.g. direct object to لازم).
- **L13** cognitive fusion can use governance_family as strong evidence.

## Limitations

- Bab is unknown in first scope (no L9 yet).
- Voice and tense_family are unknown without morphology.
- Only verbs in the KB get resolved governance; others remain candidate or unresolved.
- No invention of morphology or unsupported bab.
