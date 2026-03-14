# L8B Verb Bab Governance — Smoke Tests

Canonical examples and expected behaviour (structure and key fields; no exact long Arabic text).

## 1. عاش الرجل

- **Expected:** intransitive_basic, objects=0.
- **Profile:** governance_family = intransitive_basic, transitivity = لازم, objects = 0.
- **Status:** resolved when root عاش in KB.

## 2. ضرب الرجل الحجر

- **Expected:** basic_transitive, objects=1.
- **Profile:** governance_family = basic_transitive, transitivity = متعدي, objects = 1.
- **Status:** resolved when root ضرب in KB.

## 3. انتمى الرجل إلى الوطن

- **Expected:** intransitive_prepositional, required_prepositions includes "إلى".
- **Profile:** governance_family = intransitive_prepositional, required_prepositions = ["إلى"].
- **Status:** resolved when root انتمى in KB.

## 4. توكل الرجل على الله

- **Expected:** intransitive_prepositional, required_prepositions includes "على".
- **Profile:** governance_family = intransitive_prepositional, required_prepositions = ["على"].
- **Status:** resolved when root توكل in KB.

## 5. أعطى المعلم الطالب كتاباً

- **Expected:** double_object.
- **Profile:** governance_family = double_object, objects = 2.
- **Status:** resolved when root أعطى in KB.

## 6. ظننت الطالب مجتهداً

- **Expected:** mental_verb or special_class = أفعال القلوب.
- **Profile:** governance_family = mental_verb, special_class = أفعال القلوب, objects = 2.
- **Status:** resolved when root ظن in KB.

## 7. صيّر المعلم الطين خزفاً

- **Expected:** transformational_verb.
- **Profile:** governance_family = transformational_verb, special_class = أفعال التحويل, objects = 2.
- **Status:** resolved when root صيّر in KB.

## Resolved vs candidate vs unresolved

- **Resolved:** root found in KB with matching governance.
- **Candidate:** verb candidate (root or kind) but no KB match, or partial match.
- **Unresolved:** verb candidate but no governance inferred.
- **Excluded (verb candidacy tightening):** Non-verb tokens are **not** included in `verb_governance_profiles`; they are counted in `governance_summary.excluded_non_verbs`.

## Bab (abwab) and tense mapping

- **Resolved bab:** When the verb root is in `data/verb_abwab.json`, L8B sets bab to one of the six canonical values (e.g. ضرب → فَعَلَ-يَفْعِلُ), bab_status=resolved, and tense_mapping with past_pattern, present_pattern, present_passive_pattern.
- **Unknown bab:** When the root is not in the abwab KB (e.g. ظلم), bab=unknown, bab_status=unknown; tense_mapping fields remain "unknown". No overclaim.

- **L10B:** Can use L8B profile to expect/not expect direct object and required PP.
- **L11B:** Can avoid assigning مفعول به to لازم or wrong object count.
- **L13:** governance_family can be used as strong evidence in fusion.

## Longer sentence (project usage) — before/after verb candidacy tightening

Example: *لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً أَبَداً وَلَعَاشَ مُنْتَمِياً لِوَطَنِهِ مُخْلِصاً لِدِينِهِ وَمُتَوَكِّلاً عَلَى اللَّهِ*

**Before tightening:** verb_count was inflated; noun-like and participle-like tokens (الظَّالِمُ، كَالْحَجَرِ، أَحَداً، أَبَداً، مُنْتَمِياً، لِوَطَنِهِ، مُخْلِصاً، لِدِينِهِ، وَمُتَوَكِّلاً، عَلَى، اللَّهِ) could appear as governance profiles.

**After tightening:**
- **verb_count:** low and realistic (e.g. 3–5): only true finite verbs receive profiles (ضُرِبَ، ظَلَمَ، وَلَعَاشَ).
- **excluded_non_verbs:** high (e.g. 13); tokens without strong verb evidence are excluded.
- **Profiles only for:** ضُرِبَ (passive), ظَلَمَ (active), وَلَعَاشَ (active). No profile for الظَّالِمُ، كَالْحَجَرِ، أَحَداً، أَبَداً، مُنْتَمِياً، لِوَطَنِهِ، مُخْلِصاً، لِدِينِهِ، وَمُتَوَكِّلاً، عَلَى، etc.
- Root type and KB resolution still apply for the tokens that do receive profiles.
