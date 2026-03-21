# Quran gold iʿrāb — rule extraction plan

**Source:** `data/i3rab_phrases.csv` (8991 unique phrase types; counts sum to token-attribution occurrences in the Quran gold inventory).  
**Analysis tool:** `scripts/analyze_gold_i3rab.py` — loads phrases, classifies by **deterministic substring patterns** into categories A–E (no phrase lookup in the pipeline).  
**Policy:** Extract **rules only** — do **not** integrate CSV phrases as a runtime lookup table.

---

## 1. Corpus coverage (automated slice)

| Slice | Phrase types (top-N) | Weighted occurrences | Coverage |
|-------|----------------------|----------------------|----------|
| Top 200 | 200 | 107,599 | **77.95%** |
| Top 250 | 250 | 111,789 | **80.99%** |

To exceed **~80%** of weighted occurrences by phrase-type frequency, use **top ≥ 250** phrase patterns.

---

## 2. Category buckets (A–E)

| Letter | Category | Intent |
|--------|----------|--------|
| **A** | Particle rules | عطف، جر، نفي، توكيد/نصب، شرط، استئناف، استثناء، … |
| **B** | Verb rules | ماضٍ / مضارع (رفع/نصب/جزم)، أمر، مبني للمجهول, الأفعال الخمسة |
| **C** | Noun / phrase roles | فاعل، مفعول، مجرور، مضاف إليه، مبتدأ، خبر، نعت، حال، ظرف، … |
| **D** | Pronoun rules | فاعل مستتر، واو الجماعة، هاء الغائب، كاف المخاطب، نا، … |
| **E** | Special constructions | صلة موصول، جملة في محل رفع/نصب/جر، خبر إن، شبه جملة، جواب شرط، … |

**Classifier note:** Some inventory lines remain **`U_UNCLASSIFIED`** (e.g. تنوين/نون الوقاية، أدوات تحليلية نادرة). Extend `classify_phrase()` in the script as new patterns are justified.

---

## 3. Top 20 rules by weighted frequency (top-250 slice)

Ranked by **occurrences** summed over the 250 most frequent phrase types (same order as `scripts/analyze_gold_i3rab.py` output).

| Rank | Rule ID | Occurrences | Example gold line (truncated) |
|------|---------|-------------|-------------------------------|
| 1 | `A_JARR_GENERIC` | 7880 | حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى السُّكُونِ |
| 2 | `A_WAW_ATF` | 7533 | الْوَاوُ حَرْفُ عَطْفٍ … |
| 3 | `D_FAIL_MUSTATIR` | 6410 | الْفَاعِلُ ضَمِيرٌ مُسْتَتِرٌ تَقْدِيرُهُ هُوَ |
| 4 | `D_WAW_JAM_FAIL` | 6168 | وَاوُ الْجَمَاعَةِ … فِي مَحَلِّ رَفْعٍ فَاعِلٌ |
| 5 | `B_PAST_ACT` | 5983 | فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ |
| 6 | `D_PRON_OTHER` | 5433 | نَا … فِي مَحَلِّ رَفْعٍ فَاعِلٌ (وغيرها) |
| 7 | `A_PARTICLE_OTHER` | 4943 | التَّاءُ حَرْفُ تَأْنِيثٍ … (وغيرها) |
| 8 | `U_UNCLASSIFIED` | 4821 | بقية الأنماط غير المطابقة بعد |
| 9 | `C_ISM_MAJRUR` | 4295 | اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ … |
| 10 | `C_MAFUL_BIH` | 3693 | مَفْعُولٌ بِهِ مَنْصُوبٌ … الْفَتْحَةُ |
| 11 | `E_SILA_MAWSUL` | 3061 | الْجُمْلَةُ صِلَةُ الْمَوْصُولِ لَا مَحَلَّ لَهَا … |
| 12 | `D_HA_MUDAF` | 3061 | هَاءُ الْغَائِبِ … مُضَافٌ إِلَيْهِ |
| 13 | `D_HA_GAIB` | 2831 | هَاءُ الْغَائِبِ … بِالْحَرْفِ |
| 14 | `D_KAF_MUKHATAB` | 2828 | كَافُ الْمُخَاطَبِ … |
| 15 | `A_LAM_JARR` | 2763 | اللَّامُ حَرْفُ جَرٍّ … |
| 16 | `C_MUDAF_ILAYH` | 2664 | مُضَافٌ إِلَيْهِ مَجْرُورٌ … |
| 17 | `A_BA_JARR` | 2542 | الْبَاءُ حَرْفُ جَرٍّ … |
| 18 | `A_NAFI` | 2375 | حَرْفُ نَفْيٍ … |
| 19 | `C_FAIL` | 2255 | فَاعِلٌ مَرْفُوعٌ … الضَّمَّةُ |
| 20 | `B_PRES_RAF` | 2124 | فِعْلٌ مُضَارِعٌ مَرْفُوعٌ … الضَّمَّةُ |

**Run command:**  
`python3 scripts/analyze_gold_i3rab.py --top 250 --json-out /tmp/gold_i3rab_summary.json`

---

## 4. Formal rule stubs (G-series — documentation only)

These mirror the **intent** of the gold inventory; triggers must eventually be implemented via **pipeline signals** (L4/L5/L8B/L10B/Stage 15/16), **not** CSV string match.

### RULE G001 — JAR_HARF_GENERIC
- **Trigger:** L4 marks token as **حرف جر** (or operator catalog); following content noun → جرّ.
- **Evidence:** 7880 (weighted, top-250 slice; rule `A_JARR_GENERIC`).
- **Output:** `syntactic_role`: اسم مجرور (dependents) / PP structure per Stage 15; `i3rab_case_or_mood`: مجرور; `marker`: كسرة (when visible).
- **Stage:** L4 + Stage 15 (`JAR_MAJRUR`) + L17.
- **Confidence:** 0.90 (high frequency).

### RULE G002 — COORD_WAW
- **Trigger:** Surface **و** as coordination; L4/connectives classify as **عطف** (not واو الجماعة clitic).
- **Evidence:** 7533 (`A_WAW_ATF`).
- **Output:** `relation`: COORD; `arabic_role`: عطف.
- **Stage:** Stage 15 + L17 (coordination inheritance where implemented).
- **Confidence:** 0.92.

### RULE G003 — SUBJ_ELLIPSIS_PRON
- **Trigger:** Verb with **no overt فاعل**; L8B/L5 strong verb; gold-style “فاعل مستتر”.
- **Evidence:** 6410 (`D_FAIL_MUSTATIR`).
- **Output:** `syntactic_role`: فاعل مستتر; mood/case N/A (مبني).
- **Stage:** L8B + L17.
- **Confidence:** 0.85.

### RULE G004 — WAW_JAMA_FAIL
- **Trigger:** **واو الجماعة** suffix/clitic in verb morphology; plural subject agreement.
- **Evidence:** 6168 (`D_WAW_JAM_FAIL`).
- **Output:** agreement / فاعل role attachment.
- **Stage:** L12 + L17.
- **Confidence:** 0.88.

### RULE G005 — VERB_PAST_ACTIVE
- **Trigger:** L5/L8B finite **ماضٍ** active pattern.
- **Evidence:** 5983 (`B_PAST_ACT`).
- **Output:** `i3rab_case_or_mood`: مبني على الفتح (active past).
- **Stage:** L11B + L17.
- **Confidence:** 0.90.

### RULE G006 — ISM_MAJRUR
- **Trigger:** Token after حرف جر or `JAR_MAJRUR` edge from Stage 15.
- **Evidence:** 4295 (`C_ISM_MAJRUR`).
- **Output:** `syntactic_role`: اسم مجرور; `i3rab_case_or_mood`: مجرور; `marker`: الكسرة.
- **Stage:** Stage 15 + L17 (**partially covered** via `JAR_MAJRUR`).
- **Confidence:** 0.90.

### RULE G007 — MAFUL_BIH
- **Trigger:** Transitive verb + accusative object; Stage 15 `OBJ` where available.
- **Evidence:** 3693 (`C_MAFUL_BIH`).
- **Output:** `syntactic_role`: مفعول به; `i3rab_case_or_mood`: منصوب; `marker`: الفتحة.
- **Stage:** Stage 15 + L17 (**partially covered** via `OBJ`).
- **Confidence:** 0.90.

### RULE G008 — SILA_MAWSUL
- **Trigger:** Relative clause / موصول structure from L10B (when detected).
- **Evidence:** 3061 (`E_SILA_MAWSUL`).
- **Output:** جملة صلة — لا محل لها من الإعراب (phrase-level note).
- **Stage:** L10B + L17 (**gap**: explicit L17 template sparse).
- **Confidence:** 0.75 (needs structural detection).

### RULE G009 — MUDAF_ILAYH
- **Trigger:** `IDAFA` or Stage 15 idafa-like link; genitive after مضاف.
- **Evidence:** 2664 (`C_MUDAF_ILAYH`).
- **Output:** `syntactic_role`: مضاف إليه; مجرور.
- **Stage:** Stage 15 + L17 (**partial**).
- **Confidence:** 0.88.

### RULE G010 — FAIL_MARFUR
- **Trigger:** Stage 15 `SUBJ` to finite active verb (or L10B faʿil).
- **Evidence:** 2255 (`C_FAIL`).
- **Output:** `syntactic_role`: فاعل; `i3rab_case_or_mood`: مرفوع; `marker`: الضمة.
- **Stage:** Stage 15 + L17 (**partially covered** via `SUBJ`).
- **Confidence:** 0.88.

### RULE G011 — INNA_HARF
- **Trigger:** **إنّ** emphatic (L4 `ACC_TAWKID` / operator semantics); next noun → منصوب as اسم إن.
- **Evidence:** 1716 (`A_TAWKID_NASB_GENERIC`); see also standalone line count **778** for `إِنَّ : حَرْفُ تَوْكِيدٍ وَنَصْبٍ` in full CSV.
- **Output:** operator: حرف توكيد ونصب; governed noun: منصوب.
- **Stage:** Stage 15 (`INNA_NAME`) + L17 (**covered** for اسم إن path).
- **Confidence:** 0.88.

### RULE G012 — KHABAR_MARFU
- **Trigger:** Nominal sentence predicate; not after إنّ (different rule).
- **Evidence:** 1534 (`C_KHABAR_MARF`); user-highlighted **1082** for generic خبر مرفوع line in CSV.
- **Output:** `syntactic_role`: خبر; `i3rab_case_or_mood`: مرفوع; `marker`: الضمة.
- **Stage:** L17 (**gap** unless Stage 15 marks `PRED`/nominal shell).
- **Confidence:** 0.82.

### RULE G013 — ZARF_ZAMAN / ZARF_MAKAN
- **Trigger:** ظرف زمان / ظرف مكان accusative adverbials.
- **Evidence:** 1098 + 585 (`C_ZARF_ZAMAN`, `C_ZARF_MAKAN`); user refs **361+585**.
- **Output:** منصوب بالفتحة; ظرف.
- **Stage:** L17 (**gap** — rarely explicit vs generic مفعول به).
- **Confidence:** 0.80.

### RULE G014 — KHABAR_INNA_MARFU
- **Trigger:** Predicate after **اسم إنّ** resolved (جملة أو مفرد); خبر إن مرفوع.
- **Evidence:** 356 (`E_KHABAR_INNA_MARF` pattern); + 968 weighted for `E_JUMLA_KHABAR_INNA` (جملة في محل رفع خبر إن).
- **Output:** `syntactic_role`: خبر إن; مرفوع.
- **Stage:** L17 (**partial** — depends on إن chain resolution).
- **Confidence:** 0.84.

### RULE G015 — HAL_MANSUB
- **Trigger:** حال منصوب (often accusative adverbial clause/phrase).
- **Evidence:** 406 (`C_HAL` in full classification run — see CSV line ~69).
- **Output:** `syntactic_role`: حال; منصوب.
- **Stage:** L17 (**gap**).
- **Confidence:** 0.78.

### RULE G016 — NAAT_AGREEMENT
- **Trigger:** نعت follows منعوت (gender/number/case agreement).
- **Evidence:** 460+408+390 (`C_NAAT_MAJRUR`, `C_NAAT_MARF`, `C_NAAT_NASB` aggregate in wider slice).
- **Output:** `syntactic_role`: نعت; case follows head.
- **Stage:** L17 (**partial** — narrow `نعت` path exists in `l17_rule_based_i3rab.py`).
- **Confidence:** 0.78.

### RULE G017 — JUMLA_SHIBH_KHABAR
- **Trigger:** شبه جملة في محل رفع خبر مقدّم.
- **Evidence:** 701 (`E_SHIBH_JUMLA_KHABAR`).
- **Output:** PP/شبه جملة as fronted predicate.
- **Stage:** L10B + L17 (**gap**).
- **Confidence:** 0.72.

### RULE G018 — JAWAB_SHART
- **Trigger:** جملة في محل جزم جواب شرط.
- **Evidence:** 453 (`E_JAWAB_SHART_JAZM` in classifier).
- **Output:** جزم / جواب شرط (clause typing).
- **Stage:** Stage 16 + L17 (**partial** via clause engine).
- **Confidence:** 0.75.

### RULE G019 — PRES_JAZM / PRES_NASB
- **Trigger:** مضارع مجزوم / منصوب (جازم/ناصب).
- **Evidence:** 712+ (`B_PRES_JAZM`, `B_PRES_NASB`).
- **Output:** جزم/نصب markers (حذف نون، إلخ).
- **Stage:** L4 + L11B + L17 (**gap** for explicit mood line).
- **Confidence:** 0.80.

### RULE G020 — MUBTADA_MARFU
- **Trigger:** مبتدأ مرفوع (مقدّم أو مؤخّر).
- **Evidence:** 702 + 628 (`C_MUBTADA`, `C_MUBTADA_MUAKHKHAR`); user ref **384** for مبتدأ مرفوع.
- **Output:** `syntactic_role`: مبتدأ; مرفوع.
- **Stage:** L17 (**gap** unless Stage 15 nominal root_resolution).
- **Confidence:** 0.82.

---

## 5. Stage 17 — coverage snapshot (manual review vs `l17_rule_based_i3rab.py`)

| Rule theme | L17 today | Note |
|------------|-----------|------|
| إنّ → اسم إن منصوب | **Yes** | `INNA_NAME`, Rule 6b, reference pass |
| Coordination / عطف | **Partial** | Stage 15 `COORD` + inheritance logic |
| جرّ / مجرور | **Partial** | `JAR_MAJRUR`, depends on L10B/Stage 15 |
| فاعل / نائب فاعل / مفعول به | **Partial** | `SUBJ`, `OBJ`, `NAIB_SUBJ` |
| فاعل مستتر / ضمائر | **Partial** | Mostly via verb evidence + defaults |
| خبر / مبتدأ / حال / ظرف صريحة | **Gap** | Needs nominal-shell + L10B cues |
| صلة / شبه جملة / جواب شرط | **Gap** | Clause + deep-syntax dependent |
| Verb moods (نصب/جزم) | **Gap** | L11B richer than L17 token_reasoning |

---

## 6. Top 10 priority (impact × simplicity — **implementation later**)

Per user list, ordered for **first engineering iteration** (not done in this doc):

1. إنّ → اسم إن منصوب (**high coverage**, L17 path exists — **extend confidence / tests**).
2. خبر إن مرفوع (**E_KHABAR_INNA** / `E_JUMLA_KHABAR_INNA` — **partial**).
3. حال منصوب (**C_HAL** — **NEW**).
4. ظرف مكان/زمان منصوب (**C_ZARF_*** — **NEW**).
5. مبتدأ مرفوع (**C_MUBTADA** — **NEW**).
6. خبر مرفوع عام (**C_KHABAR_MARF** — **NEW/partial**).
7. نعت يتبع المنعوت (**C_NAAT_*** — **partial**).
8. مضاف إليه مجرور (**C_MUDAF_ILAYH** — **strengthen** Stage 15 + L17).
9. مفعول به (**C_MAFUL_BIH** — **strengthen** alignment with `OBJ`).
10. حرف جر عام / ذوات (**A_JARR_GENERIC** — **Stage 15** already central).

---

## 7. NEW vs strengthen (summary)

| Status | Rules |
|--------|-------|
| **Already touched by L17 / Stage 15** | إنّ اسم، جرّ→مجرور، فاعل/مفعول via links، بعض التنسيق والعطف |
| **NEW (explicit iʿrāb role labels desired)** | حال، ظرف زمان/مكان، مبتدأ/خبر صريح، شبه جملة خبر مقدّم، صلة موصول، مضارع نصب/جزم تفصيل |
| **Strengthen** | مضاف إليه، نعت، خبر إنّ، تطابق مفعول به مع `OBJ` |

---

## 8. Validation checklist (future work — **not executed here**)

1. Run existing `tests/orchestrator/test_stage17_*.py` after each rule implementation.
2. Conflict check: L17 must not override L11B primary rows; additive only.
3. Edge cases: dual, plural, weak verb, إنّ chains, coordination.

---

## 9. One-line reference (English)

Gold iʿrāb phrases in `data/i3rab_phrases.csv` are **analyzed offline** to propose deterministic **G-rules** for Stage 17 / L11B; phrases are **not** loaded as a lookup — implementation must use existing pipeline layers only.

---

*Generated as part of the rule extraction plan. Classifier v1 lives in `scripts/analyze_gold_i3rab.py`.*
