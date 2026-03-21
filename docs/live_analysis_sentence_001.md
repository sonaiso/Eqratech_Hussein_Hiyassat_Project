# تحليل الجملة — النظام المباشر

## الجملة

ضَرَبَ زَيْدٌ عَمْراً

## ملخص سريع

- الصلاحية العامة: valid
- الثقة النهائية الواقعية: 0.85
- نوع الجملة: خبرية
- الحكم العام: التحليل الصرفي قوي، والإعراب البنيوي النهائي (L17) قوي بلا غير محسوم، والتحليل الدلالي شبه غائب، مع بقاء عناصر غير محسومة في التحليل النحوي العميق (L10B) رغم اكتمال الإعراب البنيوي النهائي (L17).
- عدد الكلمات ذات جذر مستخرج: 3 / 3
- عدد الكلمات ذات وزن مستخرج: 2 / 3
- عدد الكلمات ذات نص إعراب تقليدي (L11): 3 / 3
- عدد الكلمات ذات إعراب بنيوي محلول (L11B، تشخيصي): 0 / 3
- **الإعراب البنيوي النهائي (L17، مُدمَج في العرض المفضّل):** محسوم 3 / مرشح 0 / غير محسوم 0
- عدد الروابط النحوية المحلولة في L10B: 0
- عدد الروابط في Stage 15: 3
- تغطية الأدوار الدلالية: 0.0
- اتساق الدمج (fusion audit): high

## لماذا لم ترتفع الثقة أكثر؟

- ضعف تغطية الأدوار الدلالية

## الجذور والأوزان

| الكلمة | الجذر | الوزن | حالة L8 | حالة L9 |
| --- | --- | --- | --- | --- |
| ضَرَبَ | ض-ر-ب | فَعَلَ | success | success |
| زَيْدٌ | ز-و-د | — | success | success |
| عَمْراً | ع-م-ر | فَعل | success | success |

## الإعراب النصي التقليدي (L11)

| الكلمة | نص الإعراب | ملاحظة |
| --- | --- | --- |
| ضَرَبَ | فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ | موجود |
| زَيْدٌ | فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ | موجود |
| عَمْراً | مَفْعُولٌ بِهِ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ | موجود |

## الإعراب البنيوي المحسوم (L11B)

| الكلمة | الدور | العامل | الحالة | العلامة | الثقة | الحالة النهائية |
| --- | --- | --- | --- | --- | --- | --- |
| ضَرَبَ | منقول من الإعراب النصي | — | غير محسوم | غير محسوم | 0.4 | unresolved |
| زَيْدٌ | منقول من الإعراب النصي | — | غير محسوم | غير محسوم | 0.4 | unresolved |
| عَمْراً | منقول من الإعراب النصي | — | غير محسوم | غير محسوم | 0.4 | unresolved |

## حالة كل مرحلة

| المرحلة | الحالة |
| --- | --- |
| L0_INPUT | success |
| L1_NORMALIZATION | success |
| L2_TOKENIZATION | success |
| L3_SEGMENTATION | success |
| L4_OPERATORS | success |
| L5_WORD_TYPING | success |
| L6_PHONOLOGY | success |
| L7_SYLLABIFICATION | success |
| L8_ROOT_EXTRACTION | success |
| L8B_VERB_BAB_GOVERNANCE | success |
| L9_WAZN_MATCHING | success |
| L14_JAMID_MUSHTAQ | success |
| L13_VERB_TRANSFORMATION | success |
| L12_GENDER_NUMBER | success |
| L10_SYNTAX | success |
| L10B_DEEP_SYNTAX | partial |
| CLAUSE_ENGINE | success |
| L11_I3RAB | success |
| L11B_CAUSAL_I3RAB | partial |
| L17_RULE_BASED_I3RAB | success |
| L12_SEMANTIC_RHETORICAL | success |
| L12B_ANALOGICAL_REASONING | success |
| L13_COGNITIVE_FUSION | success |
| L13_VALIDATION | success |
| L14_PRESENTATION | success |
| ARABIC_WORD_STATE | success |
| DEPENDENCY_SYNTAX_BUILDER | success |
| SEMANTIC_ROLE_PROJECTION | success |
| DISCOURSE_FRAME_BUILDER | success |

## ملخص نحوي عميق

- resolved_edges: 0
- candidate_edges: 0
- unresolved_tokens (L10B): 3 — قد يبقى مرتفعاً حتى مع اكتمال L17؛ راجع الملخص النهائي أعلاه.
- main_clause_type: verbal
- parse_strength: 0.0
- passive_alignment_used: False
- valency_alignment_used: False

## ملخص الإعراب السببي

- resolved_tokens: 0
- candidate_tokens: 0
- unresolved_tokens: 3

## SECTION 4g — CLAUSE STRUCTURE

  conditional_structure_detected: False
  clause_count: 1
  clause_id              | clause_type            | arabic_label   | span     | head   | conf
  main_0                 | main                   | جملة رئيسية    | 0-2      | 0      | 0.5 [no conditional structure detected]

## SECTION 4h — RULE-BASED IʿRĀB (Stage 17)

  (v2 refinement applies when L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ are present: agreement/derivational evidence, additive fields in token_reasoning.)

  coverage: high_confidence_rules_only
  resolved: 3  candidate: 0  unresolved: 0

  | token_id | surface | family | role | case/mood | marker | confidence | status |
  |----------|---------|--------|------|------------|--------|------------|--------|
  | 0 | ضَرَبَ | VERB | فعل | مبني على الفتح | الفتح | 0.75 | resolved |
  | 1 | زَيْدٌ | NOUN | فاعل | مرفوع | الضمة | 0.92 | resolved |
  | 2 | عَمْراً | NOUN | مفعول به | منصوب | الفتحة | 0.77 | resolved |

## SECTION 4i — DERIVATIONAL CLASSIFICATION

  | surface | wazn | derivational_class | jamid_or_mushtaq | conf |
  |---------|------|--------------------|-------------------|------|
  | ضَرَبَ | فَعَلَ | VERB | VERB | 0.95 |
  | زَيْدٌ | — | MUSHTAQ_LEXICAL | MUSHTAQ | 0.7 |
  | عَمْراً | فَعل | SIFA_MUSHABBAHA | MUSHTAQ | 0.75 |

  summary: ism_fail=0 ism_mafuul=0 masdar=0 jamid=0 verb=1 particle=0 unknown=0

## SECTION 4j — PREFERRED STRUCTURED IʿRĀB

  preferred from L17: 3  from L11B: 0  from L11 text: 0  agree: 0  disagree: 3  unresolved rows: 0

  | id | token | preferred | L17 status | role | عامل/governing | case/mood | marker | conf | agreement |
  |----|-------|-----------|------------|------|----------------|-----------|--------|------|-----------|
  | 0 | ضَرَبَ | L17 | resolved | فعل | — | مبني على الفتح | الفتح | 0.75 | disagree |
  | 1 | زَيْدٌ | L17 | resolved | فاعل | ضَرَبَ | مرفوع | الضمة | 0.92 | disagree |
  | 2 | عَمْراً | L17 | resolved | مفعول به | ضَرَبَ | منصوب | الفتحة | 0.77 | disagree |

## SECTION 4k — GENDER & NUMBER

  | surface | gender | number | number_type | agreement_status | conf |
  |---------|--------|--------|-------------|-------------------|------|
  | ضَرَبَ | UNKNOWN | SINGULAR | singular | unresolved | 0.6 |
  | زَيْدٌ | MASCULINE | SINGULAR | singular | unresolved | 0.7 |
  | عَمْراً | MASCULINE | SINGULAR | singular | unresolved | 0.7 |

  agreement_summary: total=3 agreed=0 conflict=0 unresolved=3

## SECTION 4l — VERB TRANSFORMATIONS

  coverage: verb_transformation_pass1 | total=1 fully=1 partially=0 untransformed=0

  | surface | past_active | present_active | past_passive | masdar | imperative | conf |
  |---------|-------------|----------------|--------------|--------|------------|------|
  | ضَرَبَ | ضَرَبَ | يَضْرِبُ | ضُرِبَ | ضَرْب | اِضْرِبْ | 0.9 |

## روابط Stage 15

| الرأس | التابع | العلاقة | الدور العربي |
| --- | --- | --- | --- |
| 0 | 1 | SUBJ | FAIL |
| 0 | 2 | OBJ | MAF3UL_BIH |
| 1 | 2 | APPOS | BADAL |

## أمثلة على العناصر غير المحسومة

- ضَرَبَ
- زَيْدٌ
- عَمْراً

## ملاحظات التحقق

- dependency parse shallow — interpret cautiously
- i3rab textual only
- rhetoric evidence weak
- analogical reasoning heuristic-based

## ما وجده النظام وما لم يجده

### ما وجده ✅

- تم استخراج طبقات صرفية واضحة لعدد معتبر من الكلمات.
- تم تصنيف نوع الجملة.
- تم استخراج جزء من البنية النحوية العميقة.
- تم إسقاط أدوار دلالية أولية حيث توفرت البنية.
- الإعراب البنيوي النهائي (L17) في العرض المفضّل: محسوم 3، مرشح 0، غير محسوم 0.

### ما لم يجده أو وجده جزئياً ⚠️

- مطابقة الأوزان جزئية: 2/3.
- التحليل النحوي العميق (L10B) لا يزال يعرض unresolved_tokens=3 (طبقة مستقلة؛ قد لا تعكس الإعراب البنيوي النهائي L17).
- L11B (تشخيصي) يظهر unresolved_tokens=3 بينما L17 النهائي لا يبقي غير محسوم؛ الفرق طبيعي عندما تقدّم L17 تغطية أوضح من طبقة L11B القديمة.
- تغطية الأدوار الدلالية منخفضة نسبيًا: 0.0.

## ملاحظات للطالب

هذا التقرير مبني من المخرجات الحية للطبقات نفسها، وليس من rendered_output جاهز. لذلك قد ترى أن الثقة النهائية الواقعية أقل من final_validation الخام إذا كانت التغطية النحوية أو الدلالية جزئية.

كما تم الفصل بين الإعراب النصي التقليدي (L11) والإعراب البنيوي المحسوم (L11B)، حتى لا يظهر التقرير وكأن جميع الكلمات محلولة نحويًا بينما الواقع غير ذلك.
