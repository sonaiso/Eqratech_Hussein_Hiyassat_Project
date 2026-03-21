# L14/L12/Discourse Tightening Batch

Focused tightening batch for three upstream issues:

1. `L14_JAMID_MUSHTAQ` family-safe derivational classification
2. `L12_GENDER_NUMBER` noun-family plural/number handling
3. Connective/discourse correction for `إِنَّ`

## Root causes

- Weak or candidate-only L8B evidence and overloaded wazn patterns could still force noun-family tokens into `VERB` or `MASDAR`.
- Noun-family forms ending in `ين` were often falling through to `SINGULAR` because suffix checks were not proclitic-aware.
- The shared connectives layer treated `إِنَّ` like conditional `إِنْ`, so discourse framing could still emit false conditional frames even after Clause Engine tightening.

## Tightening rules

### L14

- Added family-safe helper: strong noun-family cues block weak verb overreach.
- Added internal normalization for derivational checks:
  - strip leading `و`
  - strip leading `ف`
  - strip leading `ال`
- `VERB` now requires strong resolved family evidence; weak/candidate L8B is support only.
- Ambiguous masdar patterns no longer force `MASDAR` from pattern alone.

### L12

- Number detection now uses internal proclitic-aware normalization before suffix checks.
- Noun-family `...ين` forms no longer default blindly to `SINGULAR`.
- Conservative policy:
  - mushtaq noun-family `...ين` can become `PLURAL_SOUND_M`
  - otherwise `UNKNOWN` is preferred over false `SINGULAR`

### Discourse / connectives

- `إِنَّ` / `أَنَّ` and ambiguous bare `إن` / `أن` are treated conservatively as non-conditional.
- Only explicit conditional `إِنْ` is allowed into conditional connective lookup.
- Discourse frame builder also guards against noisy upstream `conditional` labels on `إِنَّ`.

## Protected examples

- `الْمُسْلِمِينَ` -> not aggressive `MASDAR`
- `وَالْمُتَصَدِّقِينَ` -> not weakly forced to `VERB`
- `أَحَداً` -> no high-confidence pattern-only `MASDAR`
- `زَيْدٌ` -> remains noun-safe in L12
- `إِنَّ زَيْدًا قَائِمٌ` -> no conditional discourse frame
- `إِنْ يَجْتَهِدْ يَنْجَحْ` -> conditional behavior preserved
