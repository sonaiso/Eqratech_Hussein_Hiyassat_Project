# تحليل الجملة — النظام المباشر

## الجملة

ضُرِبَ الظَّالِمُ

## ملخص سريع

- الصلاحية: valid
- الثقة: 1.0
- نوع الجملة: خبرية
- عدد الكلمات التي وُجد لها جذر: 2
- عدد الكلمات التي وُجد لها وزن: 2
- عدد الكلمات التي وُجد لها إعراب: 2
- اتساق الدمج (fusion audit): high

## الجذور والأوزان

| الكلمة | الجذر | الوزن | حالة L8 | حالة L9 |
|--------|-------|-------|---------|---------|
| ضُرِبَ | ض-ر-ب | فُعل | success | success |
| الظَّالِمُ | ظ-ل-م | فَاعِل | success | success |

## الإعراب (L11)

| الكلمة | نص الإعراب | ملاحظة |
|--------|------------|--------|
| ضُرِبَ | فَاعِلٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ | موجود |
| الظَّالِمُ | فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ | موجود |

## حالة كل مرحلة

| المرحلة | الحالة |
|---------|--------|
| L0_INPUT | success |
| L1_NORMALIZATION | success |
| L2_TOKENIZATION | success |
| L3_SEGMENTATION | success |
| L4_OPERATORS | success |
| L5_WORD_TYPING | success |
| L6_PHONOLOGY | success |
| L7_SYLLABIFICATION | success |
| L8_ROOT_EXTRACTION | success |
| L9_WAZN_MATCHING | success |
| L10_SYNTAX | success |
| L11_I3RAB | success |
| L12_SEMANTIC_RHETORICAL | success |
| L13_VALIDATION | success |
| L14_PRESENTATION | success |

## التفسير والأدلة

- **Stage:** L4_OPERATORS
  - Claim: No operator tokens; L4 word list from c2b.
  - Evidence: ['operator_count=0', 'words_count=2']

- **Stage:** L5_WORD_TYPING
  - Claim: Word typing (kind) from morphology.
  - Evidence: ['words_count=2', 'ضُرِبَ: kind=noun', 'الظَّالِمُ: kind=noun']

- **Stage:** L6_PHONOLOGY
  - Claim: Phonology (CV, units) from L6.
  - Evidence: ['status=success', 'num_units=16', 'gates_count=11']

- **Stage:** L7_SYLLABIFICATION
  - Claim: Syllable count from L7.
  - Evidence: ['status=success', 'count=8']

- **Stage:** L8_ROOT_EXTRACTION
  - Claim: Root(s) extracted from L8 (resolver/pattern).
  - Evidence: ['words_count=2', 'ضُرِبَ: root=ض-ر-ب', 'الظَّالِمُ: root=ظ-ل-م']

- **Stage:** L8B_VERB_BAB_GOVERNANCE
  - Claim: Passive voice detected by rule sound_trilateral_passive. Bab resolved from lexical bab knowledge base. Present passive pattern estimated from root type and bab.
  - Evidence: ['verb_count=1', 'resolved=1', 'candidate=0', 'excluded_non_verbs=1', 'ضُرِبَ: root_type=صحيح سالم, transitivity=متعدي, objects=1, governance=passive_transitive_frame', '  expected_subject_role=نائب فاعل', "  valency_class=transitive_one_object, required_roles=['فاعل', 'مفعول به']"]
  - Limitation: Tokens without strong verb evidence excluded from verb governance (verb-focused gating). Valency knowledge is seed-level and does not yet cover full Arabic verb semantics.

- **Stage:** L9_WAZN_MATCHING
  - Claim: Wazn/template from L9 (pattern match).
  - Evidence: ['words_count=2', 'ضُرِبَ: template=فُعل', 'الظَّالِمُ: template=فَاعِل']

- **Stage:** L10_SYNTAX
  - Claim: Syntax: word forms and isnadi links from L10.
  - Evidence: ['word_forms_count=2', 'isnadi_links=0']
  - Limitation: Syntax depth may be shallow; full dependency parse not guaranteed.

- **Stage:** L10B_DEEP_SYNTAX
  - Claim: Resolved dependency relations from L10 isnadi and rule-based harf_jar/idafa. Passive frame from L8B used to prioritize نائب فاعل over active فاعل. Clause units: nominal.
  - Evidence: ['dependency_nodes=2', 'dependency_edges=1', 'resolved_edges=1', 'candidate_edges=0', 'unresolved_tokens=1', 'main_clause_type=nominal', 'clause_units=1', 'passive_alignment_used=True', "naib_fa'il_edges=1"]
  - Limitation: Rule-constrained dependency inference with guarded relation generation.

- **Stage:** L11_I3RAB
  - Claim: I3rab per token from L11 (c2e i3rab_text).
  - Evidence: ['token_results_count=2', 'ضُرِبَ: i3rab_text=present', 'الظَّالِمُ: i3rab_text=present']
  - Limitation: I3rab evidence is text-based; no deep syntactic case reasoning.

- **Stage:** L11B_CAUSAL_I3RAB
  - Claim: Resolved grammatical roles from L10B/L11 and rule-based governing factors. Passive evidence used to assign نائب فاعل where L8B/L10B support it. Candidate roles from nominal/idafa/object heuristics.
  - Evidence: ['resolved_tokens=1', 'candidate_tokens=1', 'unresolved_tokens=0', 'ضُرِبَ: role=مبتدأ status=candidate gov=الابتداء', 'الظَّالِمُ: role=نائب فاعل status=resolved gov=فعل مبني للمجهول', 'نائب فاعل assigned=1']
  - Limitation: Rule-constrained; first-scope roles only. No full Arabic i3rab coverage.

- **Stage:** SEMANTIC_ROLE_PROJECTION
  - Claim: Semantic role projection: PATIENT inferred from passive syntactic structure.
  - Evidence: ['projection_coverage=0.5', 'assigned_roles=1', 'الظَّالِمُ: PATIENT (passive_naib_fael_projection)']
  - Limitation: Structural semantic projection only; not deep semantics or logical inference.

- **Stage:** L12_SEMANTIC_RHETORICAL
  - Claim: Sentence type and rhetoric signals from L12.
  - Evidence: ['sentence_type=خبرية', 'rhetoric_signals_count=0']
  - Limitation: Rhetoric detection is surface/syntax-assisted; deep semantic rhetoric not implemented.

- **Stage:** L12B_ANALOGICAL_REASONING
  - Claim: Analogical inference: ism fa'il pattern similarity, syntactic role inference, or i3rab analogy.
  - Evidence: ['total_inferences=4', 'ambiguity_resolutions=1', 'inference: morphological (strong)', 'inference: syntactic (weak)', 'inference: syntactic (weak)']
  - Limitation: Deterministic rules only; no ML or corpus lookup.

- **Stage:** L13_COGNITIVE_FUSION
  - Claim: Cognitive fusion: hierarchical evidence arbitration; dominant source per token.
  - Evidence: ['fusion_mode=normal', 'token_states_count=2', 'global_confidence=0.7611', 'ضُرِبَ->ROOT', 'الظَّالِمُ->ROOT']
  - Limitation: Arbitration only; no invention. Syntax depth limits role resolution.

- **Stage:** L13_VALIDATION
  - Claim: Validation: valid. No issues; all key stages consistent.
  - Evidence: ['global_validity=valid', 'issue_count=0', 'final_confidence=1.0']


## ما وجده النظام وما لم يجده

### ما وجده ✅

- [L5_WORD_TYPING] Word typing (kind) from morphology.
- [L6_PHONOLOGY] Phonology (CV, units) from L6.
- [L7_SYLLABIFICATION] Syllable count from L7.
- [L8_ROOT_EXTRACTION] Root(s) extracted from L8 (resolver/pattern).
- [L8B_VERB_BAB_GOVERNANCE] Passive voice detected by rule sound_trilateral_passive. Bab resolved from lexic
- [L9_WAZN_MATCHING] Wazn/template from L9 (pattern match).
- [L10_SYNTAX] Syntax: word forms and isnadi links from L10.
- [L10B_DEEP_SYNTAX] Resolved dependency relations from L10 isnadi and rule-based harf_jar/idafa. Pas
- [L11_I3RAB] I3rab per token from L11 (c2e i3rab_text).
- [L11B_CAUSAL_I3RAB] Resolved grammatical roles from L10B/L11 and rule-based governing factors. Passi
- [SEMANTIC_ROLE_PROJECTION] Semantic role projection: PATIENT inferred from passive syntactic structure.
- [L12_SEMANTIC_RHETORICAL] Sentence type and rhetoric signals from L12.
- [L12B_ANALOGICAL_REASONING] Analogical inference: ism fa'il pattern similarity, syntactic role inference, or
- [L13_COGNITIVE_FUSION] Cognitive fusion: hierarchical evidence arbitration; dominant source per token.
- [L13_VALIDATION] Validation: valid. No issues; all key stages consistent.

### ما لم يجده أو وجده جزئياً ⚠️

- [L4_OPERATORS] No operator tokens; L4 word list from c2b.

## ملاحظات للطالب

هذا التقرير أنتجه نظام التحليل اللغوي آلياً. الجذور والأوزان والإعراب مأخوذة من مخرجات المسار. إذا ظهر "—" فمعناه أن المرحلة لم تُعطِ نتيجة لهذه الكلمة (مثلاً حرف لا جذر له، أو كلمة مُعرّبة لم يُستخرج إعرابها بعد). الصلاحية والثقة تلخصان مدى اتساق النتائج. إن وُجدت تحذيرات أو قيود في التفسير فهي توضح ما الذي بقي جزئياً أو غير مؤكد.