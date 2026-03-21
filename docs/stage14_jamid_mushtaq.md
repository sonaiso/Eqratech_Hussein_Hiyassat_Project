# Stage 14 — Jamid vs Mushtaq Engine (Pass 1)

**Derivational classification** from L8 root, L9 wazn, L5 kind, and L8B verb profile. Output enriches downstream stages (e.g. Stage 17 v2) with morphological depth.

## Purpose

- Classify each token as **MUSHTAQ** (derived) or **JAMID** (non-derived), with a specific derivational class when applicable.
- **ISM_FAIL** (اسم فاعل), **ISM_MAFUUL** (اسم مفعول), **SIFA_MUSHABBAHA** (صفة مشبهة), **MASDAR** (مصدر), **SIGA_MUBALAGHAH** (صيغ المبالغة) support Stage 17 and future iʿrāb/semantic layers.
- **JAMID** (proper nouns, particles, non-derived nouns) prevents false mushtaq derivation — **except** when **ARABIC_WORD_STATE** marks `root_confirmed` or `wazn_confirmed`: then JAMID is forbidden and the token is labeled **MUSHTAQ_LEXICAL** + `jamid_or_mushtaq=MUSHTAQ` (`jamid_blocked_confirmed_root_or_wazn`).
- **Persistent state:** `layer_outputs["ARABIC_WORD_STATE"]` is rebuilt after L9 with **stem-aligned** L8/L9 (same derivational stem for وَالْمُؤْمِنِينَ and الْمُؤْمِنِينَ when c2b rows use the definite/plural lemma form). **`root` and `canonical_root` in that map are the canonical morphology root** (post hollow-participle correction; hollow/mafʿūl patches set both); **`raw_l8_root`** retains the original L8 hypothesis when a row existed; **`root_correction_source`** records `hollow_ism_fail` / `hollow_ism_mafuul` when canonical ≠ raw L8. **`canonical_derivation`** (`src/orchestrator/canonical_derivation.py`) may infer **`canonical_wazn`** when L9 is empty on long surfaces, including **مُفْعِل** for documented stems like **مسلم / مؤمن** (lexicon-based, not sentence-hardcoded). L14 merges `derivational_class` / `jamid_or_mushtaq` **and re-syncs `root`** from each `token_classifications` entry after classification so downstream stays aligned.
- **Hollow active participle (اسم الفاعل الأجوف):** `src/orchestrator/hollow_ism_fail.py` — surface pattern فَائِل (C+ا+ئ+C) after internal stripping; documented stems map to canonical roots (e.g. صائم→ص-و-م, قائل→ق-و-ل, بائع→ب-ي-ع). L8 roots that treat the hamza as middle radical (e.g. ص-ي-م) are **overridden** in ARABIC_WORD_STATE when the stem matches the lexicon. **Presentation and Stage 15 same-root logic must read `ARABIC_WORD_STATE.root` (or L14 `token_classifications.root`), not raw `L8_ROOT_EXTRACTION.words[].root` alone.** L14 **RULE 1H** assigns `ISM_FAIL` + `MUSHTAQ` before MASDAR/SIFA competition when the stem is a hollow-participle candidate (listed or shape-matched).
- **Hollow passive participle (اسم المفعول الأجوف):** `src/orchestrator/hollow_ism_mafuul.py` — stems `م` + C + (و|ي) + C after affix strip (e.g. مقول، مبيع، مخوف); lexicon maps to verbal origins (مقول→ق-و-ل، مبيع→ب-ي-ع، مخوف→خ-و-ف). Corrects wrong L8 middles (ق-ي-ل، ب-و-ع، خ-ي-ف). L14 **RULE 2H** assigns `ISM_MAFUUL` + `MUSHTAQ` when listed or shape-matched, before MASDAR/SIFA routing.

## Pipeline position

- **Stage key:** `L14_JAMID_MUSHTAQ`
- **Position:** After `L9_WAZN_MATCHING`, before `L10_SYNTAX`.
- **Rationale:** Depends on wazn (L9) and root (L8); must be available to L10, L10B, L11B, Stage 15, Stage 17.

## Output schema

- **token_classifications:** per-token `token_id`, `surface`, `root`, `wazn`, `derivational_class`, `jamid_or_mushtaq`, `confidence`, `rule`, `evidence_sources`.
- **classification_summary:** counts for ism_fail, ism_mafuul, sifa_mushabbaha, masdar, siga_mubalaghah, mushtaq_lexical, jamid, verb, particle, unknown.
- **coverage:** `wazn_based_pass1`.
- **ambiguity_log:** when multiple classes apply (e.g. فَعْل as MASDAR vs SIFA_MUSHABBAHA).

## Wazn-to-class mapping (Pass 1)

| derivational_class | Wazn patterns (normalized) | confidence |
|--------------------|----------------------------|------------|
| ISM_FAIL           | فاعل، مفاعل، مفعل، متفاعل، منفعل، مفتعل، تفاعل، مستفعل | 0.9 |
| ISM_MAFUUL         | مفعول، مفعل، مفاعل، متفعل، منفعل، مفتعل | 0.9 |
| SIFA_MUSHABBAHA    | فعيل، فعل، افعل، فعلان، فعول | 0.75 |
| MASDAR             | فعل، فعال، فعول، تفعيل، افعال، تفاعل، انفعال، افتعال، استفعال، مفعولة، فعالة، فعلة | 0.8 |
| SIGA_MUBALAGHAH    | فعّال، فعيل، مفعال، فعول، فعل | 0.75 |
| MUSHTAQ_LEXICAL    | JAMID path blocked: confirmed L8 root or L9 wazn (see ARABIC_WORD_STATE) | ≤0.85 |
| JAMID              | No mushtaq wazn match; noun/name/particle from L5; **not** if root/wazn confirmed | 0.7–0.85 |
| VERB               | L8B verb profile or L5 verb | 0.95 |
| PARTICLE           | L5 operator/particle | 0.95 |

## Evidence precedence

1. L8B verb profile or L5 verb → VERB (no mushtaq).
2. L5 operator/particle → PARTICLE.
3. L9 wazn vs. pattern sets → ISM_FAIL, ISM_MAFUUL, then MASDAR/SIFA/SIGA with ambiguity log when overlapping.
4. L5 noun + no mushtaq wazn (or proper noun) → JAMID.
5. Else → UNKNOWN.

## Integration with downstream

- **Stage 17 (L17_RULE_BASED_I3RAB):** Pass 1 does not consume L14; output is ready for Stage 17 v2 (ISM_FAIL → فاعل/نعت/خبر candidate; ISM_MAFUUL → نائب فاعل/نعت; MASDAR → مصدر مؤول; JAMID → no mushtaq-based role).

## Reporting

- **SECTION 4i** in `scripts/analyze_sentence.py` and in L14_PRESENTATION (detailed mode): table surface | wazn | derivational_class | jamid_or_mushtaq | confidence, plus summary counts.

## Known limitations (Pass 1)

- Overlap between SIFA_MUSHABBAHA, MASDAR, and SIGA_MUBALAGHAH (e.g. فَعْل، فَعِيل، فَعُول) resolved by confidence and MASDAR preference; ambiguity logged.
- **Deferred to Pass 2:** ism tafdil (أفعل)، nisba (فَعْلِيّ), and other derived patterns.

## Files

- `src/orchestrator/arabic_word_state.py` — `rebuild_arabic_word_state_from_layers`, `ensure_arabic_word_state`, `jamid_assignment_forbidden`, L14/L12 merge helpers
- `src/orchestrator/hollow_ism_fail.py` — hollow اسم فاعل detection, lexicon roots, `resolve_hollow_ism_fail_root`, `apply_hollow_root_to_word_state_entry`
- `src/orchestrator/hollow_ism_mafuul.py` — hollow اسم مفعول detection, lexicon roots, `resolve_hollow_ism_mafuul_root`, `apply_hollow_mafuul_root_to_word_state_entry`
- `src/orchestrator/l14_jamid_mushtaq.py` — `build_jamid_mushtaq(lo)`, `RealL14JamidMushtaq`
- `tests/orchestrator/test_stage14_jamid_mushtaq.py` — includes stem-alignment and JAMID-gate regressions
