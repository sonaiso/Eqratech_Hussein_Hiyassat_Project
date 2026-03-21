# الترتيب التنفيذي الفعلي للبوابات في المشروع

يوجد في هذا المشروع نوعان مختلفان من “الترتيب” يجب عدم الخلط بينهما:

---

## 1) الترتيب التنفيذي الفعلي

وهو الترتيب الذي تعمل به البوابات فعليًا داخل الـ orchestrator في النسخة الحالية من النظام.

**المرجع البرمجي للمعرفات:** القائمة الثابتة `STAGE_ORDER` في `src/orchestrator/types.py`.  
**ترتيب الاستدعاء في التشغيل:** حلقة `run_pipeline` تمرّ على `get_default_registry()` في `src/orchestrator/stage_registry.py`، مع **خطافات (hooks)** بعد مراحل محددة في `src/orchestrator/pipeline_orchestrator.py` لإنتاج الطبقات الإضافية وتحديث `ARABIC_WORD_STATE`.

السلسلة التنفيذية الأساسية (مطابقة لترتيب التشغيل + نقاط التكامل):

`L0_INPUT`  
→ `L1_NORMALIZATION`  
→ `L2_TOKENIZATION`  
→ `L3_SEGMENTATION`  
→ `L4_OPERATORS`  
→ `L5_WORD_TYPING`  
→ `L6_PHONOLOGY`  
→ `L7_SYLLABIFICATION`  
→ `L8_ROOT_EXTRACTION`  
→ `L8B_VERB_BAB_GOVERNANCE`  
→ `L9_WAZN_MATCHING`  
→ **`[ARABIC_WORD_STATE rebuild]`** (بعد انتهاء L9 — في الـ orchestrator)  
→ `L14_JAMID_MUSHTAQ`  
→ **`[ARABIC_WORD_STATE merge من L14]`** (داخل تنفيذ مرحلة L14 عبر `merge_l14_classifications_into_word_state`)  
→ `L13_VERB_TRANSFORMATION`  
→ `L12_GENDER_NUMBER`  
→ **`[ARABIC_WORD_STATE merge من L12]`** (بعد انتهاء L12 — في الـ orchestrator)  
→ `L10_SYNTAX`  
→ `L10B_DEEP_SYNTAX`  
→ **`[DEPENDENCY_SYNTAX_BUILDER (Stage 15)]`**  
→ **`[CLAUSE_ENGINE (Stage 16)]`** — يُملأ مخرجها في نفس خطاف ما بعد `L10B` مع Stage 15؛ المعرف موجود في `STAGE_ORDER` لكن التنفيذ الحالي يعتمد على `build_clause_output` من الخطاف وليس دائمًا كـ `BaseStage` منفصل في السجل الافتراضي؛ يتضمن `verbal_clause_regions` عند وجود جملة فعلية خبرية لاحقة بعد `INNA_NAME` (راجع Stage 15 dependency_links)  
→ `L11_I3RAB`  
→ `L11B_CAUSAL_I3RAB`  
→ **`[SEMANTIC_ROLE_PROJECTION]`** (بعد L11B — في الـ orchestrator)  
→ `L17_RULE_BASED_I3RAB`  
→ `L12_SEMANTIC_RHETORICAL`  
→ `L12B_ANALOGICAL_REASONING`  
→ **`[DISCOURSE_FRAME_BUILDER]`** (بعد L12B — في الـ orchestrator)  
→ `L13_COGNITIVE_FUSION`  
→ `L13_VALIDATION`  
→ `L14_PRESENTATION`

---

## 2) الطبقات الإضافية

بعض المكونات ليست جزءًا من السلسلة الرقمية الأصلية، لكنها تعمل في نقاط تكامل محددة داخل التنفيذ. هذه تُعامل كطبقات **additive**، وأهمها:

| الطبقة الإضافية | متى تُفعَّل | ملاحظة |
|-----------------|-------------|--------|
| **ARABIC_WORD_STATE** | إعادة بناء بعد `L9_WAZN_MATCHING`؛ دمج من L14 داخل مرحلة L14؛ دمج بعد `L12_GENDER_NUMBER` | مخزن حالة تراكمية في `layer_outputs` تحت مفتاح غير مرقم في `STAGE_ORDER` |
| **DEPENDENCY_SYNTAX_BUILDER** | بعد `L10B_DEEP_SYNTAX` | Stage 15 — روابط تبعية |
| **SEMANTIC_ROLE_PROJECTION** | بعد `L11B_CAUSAL_I3RAB` | قبل `L17_RULE_BASED_I3RAB` في تدفق البيانات |
| **DISCOURSE_FRAME_BUILDER** | بعد `L12B_ANALOGICAL_REASONING` | إطارات خطاب |

---

## 3) ترتيب الأولوية العلمي

هذا ليس ترتيب تنفيذ، بل ترتيب أولوية تطوير في roadmap العلمي. لذلك لا يجوز اعتباره ترتيب تشغيل.  
انظر: `docs/architecture/SCIENTIFIC_NEXT_PHASES.md`.

---

## 4) ملاحظة مهمة حول التسمية

بعض الأسماء في المشروع متراكبة تاريخيًا، مثل:

- `L12_GENDER_NUMBER` مقابل `L12_SEMANTIC_RHETORICAL`
- `L13_VERB_TRANSFORMATION` مقابل `L13_COGNITIVE_FUSION` و`L13_VALIDATION`
- `L14_JAMID_MUSHTAQ` مقابل `L14_PRESENTATION`

لذلك المرجع المعتمد عند الحديث عن **التنفيذ** هو ترتيب التشغيل الفعلي داخل الـ orchestrator و`STAGE_ORDER`، لا مجرد رقم الطبقة أو تشابه الاسم.

---

## الصيغة المختصرة جدًا

الترتيب المعتمد في المشروع هو **ترتيب التنفيذ الفعلي** داخل الـ orchestrator، مع وجود **طبقات additive** تعمل في نقاط محددة مثل `ARABIC_WORD_STATE` و`DEPENDENCY_SYNTAX_BUILDER` و`SEMANTIC_ROLE_PROJECTION` و`DISCOURSE_FRAME_BUILDER`. ولا يجوز الخلط بين هذا الترتيب وبين **ترتيب الأولوية العلمية** في roadmap.

---

## جدول التنفيذ الفعلي للبوابات (مختصر رسمي)

| الترتيب | المرحلة | النوع | تعمل بعد / ضمن السياق | تستهلك أساسًا | تنتج أساسًا |
|:--------:|---------|------|------------------------|---------------|-------------|
| 1 | L0_INPUT | مرحلة رئيسية | — | النص الخام | إدخال أولي |
| 2 | L1_NORMALIZATION | مرحلة رئيسية | L0 | النص الخام | نص مطبّع |
| 3 | L2_TOKENIZATION | مرحلة رئيسية | L1 | النص المطبّع | tokens |
| 4 | L3_SEGMENTATION | مرحلة رئيسية | L2 | tokens | سوابق/جذع/لواحق |
| 5 | L4_OPERATORS | مرحلة رئيسية | L3 | tokens + segmentation | أدوات/مشغلات |
| 6 | L5_WORD_TYPING | مرحلة رئيسية | L4 | tokens + operators | نوع الكلمة |
| 7 | L6_PHONOLOGY | مرحلة رئيسية | L5 | tokens | خصائص صوتية |
| 8 | L7_SYLLABIFICATION | مرحلة رئيسية | L6 | phonology | مقاطع |
| 9 | L8_ROOT_EXTRACTION | مرحلة رئيسية | L7 | tokens + segmentation | الجذر |
| 10 | L8B_VERB_BAB_GOVERNANCE | مرحلة رئيسية | L8 | root + word typing | ملف الفعل/الباب/الحوكمة |
| 11 | L9_WAZN_MATCHING | مرحلة رئيسية | L8B | root + stem | الوزن |
| 12 | ARABIC_WORD_STATE rebuild | طبقة إضافية | L9 | L2 + L8 + L9 | حالة الكلمة التراكمية |
| 13 | L14_JAMID_MUSHTAQ | مرحلة رئيسية | L9 / word state | root + wazn + state | مشتق/جامد/صنف اشتقاقي |
| 14 | ARABIC_WORD_STATE merge (L14) | طبقة إضافية | داخل L14 | مخرجات L14 | تحديث الحالة الاشتقاقية |
| 15 | L13_VERB_TRANSFORMATION | مرحلة رئيسية | L14 | root + bab + دليل فعل | صيغ تحويل الفعل |
| 16 | L12_GENDER_NUMBER | مرحلة رئيسية | L13 | word state + morphology | جنس/عدد/تمييز |
| 17 | ARABIC_WORD_STATE merge (L12) | طبقة إضافية | L12 | مخرجات L12 | تحديث الجنس/العدد |
| 18 | L10_SYNTAX | مرحلة رئيسية | L12 | typing + operators + morphology | نحو أولي |
| 19 | L10B_DEEP_SYNTAX | مرحلة رئيسية | L10 | syntax + governance | علاقات أعمق |
| 20 | DEPENDENCY_SYNTAX_BUILDER | طبقة إضافية / Stage 15 | L10B | deep syntax + L5/L8B/L14… | dependency_links |
| 21 | CLAUSE_ENGINE | مرحلة / Stage 16 | ما بعد L10B (خطاف مع 20) | operators + syntax | clauses / clause ids |
| 22 | L11_I3RAB | مرحلة رئيسية | سياق ما بعد البند 21 | syntax + morphology | إعراب نصي |
| 23 | L11B_CAUSAL_I3RAB | مرحلة رئيسية | L11 | L11 + syntax | إعراب سببي/بنيوي |
| 24 | SEMANTIC_ROLE_PROJECTION | طبقة إضافية | L11B | causal iʿrāb + syntax | semantic roles |
| 25 | L17_RULE_BASED_I3RAB | مرحلة رئيسية | L11B + projection | Stage 15 + clauses + L12 + L14 | token_reasoning |
| 26 | L12_SEMANTIC_RHETORICAL | مرحلة رئيسية | L17 | syntax + clauses | دلالي/بلاغي |
| 27 | L12B_ANALOGICAL_REASONING | مرحلة رئيسية | L12_SEMANTIC_RHETORICAL | semantic/rhetorical | analogical reasoning |
| 28 | DISCOURSE_FRAME_BUILDER | طبقة إضافية | L12B | connectives + L10B/L12… | discourse frames |
| 29 | L13_COGNITIVE_FUSION | مرحلة رئيسية | L12B + discourse | طبقات سابقة | دمج معرفي |
| 30 | L13_VALIDATION | مرحلة رئيسية | fusion | fusion + audits | تحقق نهائي |
| 31 | L14_PRESENTATION | مرحلة رئيسية | validation | جميع المخرجات | report / compact / display |

---

## جدول الطبقات الإضافية فقط

| الطبقة الإضافية | متى تعمل | وظيفتها |
|-----------------|----------|---------|
| ARABIC_WORD_STATE | بعد L9 ثم يُحدَّث من L14 (داخل المرحلة) وبعد L12 (في الـ orchestrator) | حفظ الحالة التراكمية للكلمة |
| DEPENDENCY_SYNTAX_BUILDER | بعد L10B | بناء الروابط النحوية Stage 15 (يشمل Pass E3: لا ينسكب `OBJ` من `ISM_FAIL` إلى فعل مركّز لاحق — Batch 1.1) |
| SEMANTIC_ROLE_PROJECTION | بعد L11B | إسقاط الأدوار الدلالية |
| DISCOURSE_FRAME_BUILDER | بعد L12B | بناء إطارات الخطاب |

---

## القاعدة المعمارية المعتمدة

- **`STAGE_ORDER`** هو المرجع الأساسي **لمعرفات** المراحل الرئيسية وحفظ `layer_outputs`.
- الطبقات **additive** ليست مراحل مرقمة داخل السلسلة نفسها، لكنها تعمل في نقاط ثابتة في `pipeline_orchestrator.py`.
- **`ARABIC_WORD_STATE`** هو مخزن الحالة التراكمي للكلمة، وليس مجرد مخرج عرض.
- أي إصلاح لغوي يجب أن يُطبَّق في الطبقة المالكة للمعلومة، لا في analyzer أو presentation إلا من جهة القراءة/العرض فقط.

**إصلاح بنيوي (Batch 1.1 — Stage 15):** في `dependency_syntax/builder.py`، مرور Pass E3 (`_apply_ism_fail_governed_object`) لا يضيف `OBJ` من حاكم `ISM_FAIL` إلى التوكن التالي إذا كان ذلك التوكن **فعلًا محدودًا** بحسب `L14:VERB` أو `has_strong_true_verb_evidence`، حتى لو خَيَّرَ L5 نوعه كاسم؛ يمنع ذلك انسكاب المفعولية إلى فعل يفتتح جملة فعلية لاحقة (مثل التنسيق الطويل قبل `أَعَدَّ`).

**إصلاح بنيوي (Batch 1.2 — Stage 15):** Pass 5b (`Pass_C_coordination_attached_prefix`) يحدد رأس `COORD` لتوكن `وَ…` بمسح يسارًا مع تخطي المفعول به التابع لاسم فاعل/مفعول (`OBJ` + `ISM_FAIL`/`ISM_MAFUUL`) وتخطي ذيل التوكيد المنصوب (`كَثِيرًا`، `قليلا`…) حتى تُستأنف سلسلة العطف بعد نطاق المفعول المحلي.

---

## سطر واحد رسمي للوثائق (إنجليزي)

The pipeline executes through the fixed main stage chain (`STAGE_ORDER`), while additive layers such as `ARABIC_WORD_STATE`, `DEPENDENCY_SYNTAX_BUILDER`, `SEMANTIC_ROLE_PROJECTION`, and `DISCOURSE_FRAME_BUILDER` run at defined integration points in `pipeline_orchestrator.py` and are not separate numbered stages in the core `STAGE_ORDER`—except that `CLAUSE_ENGINE` is listed in `STAGE_ORDER` but is currently populated via the post-`L10B_DEEP_SYNTAX` hook alongside Stage 15.

---

## مراجع ملفات الكود

| الملف | الغرض |
|-------|--------|
| `src/orchestrator/types.py` | `STAGE_ORDER` الثابت |
| `src/orchestrator/stage_registry.py` | `get_default_registry()` — ترتيب استدعاء `BaseStage` |
| `src/orchestrator/pipeline_orchestrator.py` | خطافات ما بعد L9 / L10B / L11B / L12B ودمج `ARABIC_WORD_STATE` |
| `src/orchestrator/arabic_word_state.py` | إعادة البناء والدمج |
| `docs/architecture/PIPELINE_MASTER_MEMORY.md` | الذاكرة المعمارية المركزية |

---

*End of ORCHESTRATOR_EXECUTION_ORDER_AR.md*
