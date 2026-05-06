"""
اختبارات الأساس الرياضي — Foundation Tests
============================================
تغطي:
1. الأنطولوجيا: Ω / R / T / τ
2. مخرجات النظام: شهادة / فرضية / صفر معرفي
3. النوى المفاهيمية: sample من النوى العشرين
4. وحدات يونيكود: ArabicUnit / ArabicText
5. استخلاص الأثر: TraceExtractor
6. خط الأنابيب: AnalysisPipeline (end-to-end)
7. التسلسل: serialize/load
"""

import pytest

# ---- imports من حزمة foundation ----
from foundation.ontology import (
    KnowledgeUniverse,
    Reality,
    RealityKind,
    Trace,
    TraceLevel,
    trace_fn,
)
from foundation.outputs import (
    OutputKind,
    SystemOutput,
    Shahada,
    Hypothesis,
    EpistemicZero,
    OutputList,
    SHAHADA_CONFIDENCE_THRESHOLD,
)
from foundation.nuclei import (
    ShahadaNucleus,
    SifrNucleus,
    FaradiyyaNucleus,
    TasawwurNucleus,
    IrabVectorNucleus,
    QiyasNucleus,
    TaarudTarjihNucleus,
    LowerLayersNucleus,
)
from foundation.unicode_units import (
    ArabicUnit,
    ArabicText,
    TokenUnit,
    UnitKind,
)
from foundation.trace import TraceExtractor, RichTrace
from foundation.pipeline import (
    AnalysisPipeline,
    PipelineStage,
    StagedAnalysis,
    STAGE_NAMES_AR,
    STAGE_NAMES_EN,
)
from foundation.serialization import (
    serialize_analysis,
    load_analysis,
    format_analysis_text,
    format_trace_units,
)


# ===========================================================================
# 1. الأنطولوجيا
# ===========================================================================

class TestOntology:
    """اختبارات الكون المعرفي والواقع والأثر ودالة الأثر."""

    def test_reality_creation(self):
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        assert r.raw_text == "الكِتَابُ مُفِيدٌ"
        assert r.kind == RealityKind.TEXT
        assert r.uid.startswith("R:")
        assert r.is_arabic()

    def test_reality_empty_is_not_arabic(self):
        r = Reality(raw_text="")
        assert not r.is_arabic()

    def test_reality_latin_text_not_arabic(self):
        r = Reality(raw_text="Hello world")
        assert not r.is_arabic()

    def test_trace_fn_surface(self):
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        t = trace_fn(r)
        assert isinstance(t, Trace)
        assert t.source_uid == r.uid
        assert t.level == TraceLevel.SURFACE
        assert t.tokens == ["الكِتَابُ", "مُفِيدٌ"]
        assert t.features["token_count"] == 2
        assert t.features["has_harakat"] is True

    def test_trace_fn_empty_text(self):
        r = Reality(raw_text="  ")
        t = trace_fn(r)
        assert t.tokens == []
        assert t.is_empty()

    def test_trace_uid_unique(self):
        r1 = Reality(raw_text="نص أول")
        r2 = Reality(raw_text="نص ثانٍ")
        t1 = trace_fn(r1)
        t2 = trace_fn(r2)
        assert t1.uid != t2.uid

    def test_knowledge_universe_register(self):
        omega = KnowledgeUniverse()
        r = Reality(raw_text="الكِتَابُ")
        omega.register(r)
        assert len(omega) == 1
        assert omega.get(r.uid) is r

    def test_knowledge_universe_apply_trace(self):
        omega = KnowledgeUniverse()
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        omega.register(r)
        t = omega.apply_trace_fn(r)
        assert isinstance(t, Trace)
        assert len(omega) == 2  # واقع + أثر
        assert len(omega.traces) == 1

    def test_knowledge_universe_register_invalid(self):
        omega = KnowledgeUniverse()
        with pytest.raises(TypeError):
            omega.register("not a reality")  # type: ignore


# ===========================================================================
# 2. مخرجات النظام
# ===========================================================================

class TestOutputs:
    """اختبارات الشهادة والفرضية والصفر المعرفي."""

    def test_shahada_creation(self):
        out = Shahada("مُفِيدٌ خبر مرفوع", confidence=0.95, stage="الحكم")
        assert out.kind == OutputKind.SHAHADA
        assert out.confidence == 0.95
        assert out.stage == "الحكم"

    def test_hypothesis_creation(self):
        out = Hypothesis("قد يكون فعلاً", confidence=0.6)
        assert out.kind == OutputKind.HYPOTHESIS
        assert out.confidence == 0.6
        assert not out.is_epistemic_zero()

    def test_epistemic_zero_creation(self):
        out = EpistemicZero("النص فارغ")
        assert out.kind == OutputKind.EPISTEMIC_ZERO
        assert out.confidence == 0.0
        assert out.is_epistemic_zero()
        assert out.content is None

    def test_hypothesis_promotion_above_threshold(self):
        out = Hypothesis("نتيجة", confidence=SHAHADA_CONFIDENCE_THRESHOLD + 0.05)
        promoted = out.promote()
        assert promoted.kind == OutputKind.SHAHADA

    def test_hypothesis_no_promotion_below_threshold(self):
        out = Hypothesis("نتيجة", confidence=SHAHADA_CONFIDENCE_THRESHOLD - 0.05)
        not_promoted = out.promote()
        assert not_promoted.kind == OutputKind.HYPOTHESIS

    def test_shahada_promote_stays_shahada(self):
        out = Shahada("ثابت", confidence=0.9)
        same = out.promote()
        assert same.kind == OutputKind.SHAHADA

    def test_output_list(self):
        ol = OutputList()
        ol.add(Shahada("1", confidence=0.9))
        ol.add(Hypothesis("2", confidence=0.6))
        ol.add(EpistemicZero("فارغ"))
        assert len(ol) == 3
        assert len(ol.shahadas()) == 1
        assert len(ol.hypotheses()) == 1
        assert len(ol.zeros()) == 1
        best = ol.best()
        assert best is not None
        assert best.confidence == 0.9


# ===========================================================================
# 3. النوى المفاهيمية
# ===========================================================================

class TestNuclei:
    """اختبارات النوى العشرين (sample)."""

    def test_shahada_nucleus(self):
        n = ShahadaNucleus()
        assert n.name_ar == "الشهادة"
        assert n.name_en == "Shahada"
        assert n.certainty_threshold == 0.80

    def test_sifr_nucleus(self):
        n = SifrNucleus(reason="لا دليل")
        assert n.name_ar == "الصفر المعرفي"
        assert n.reason == "لا دليل"
        assert not n.is_absolute

    def test_faradiyya_nucleus(self):
        n = FaradiyyaNucleus(confidence=0.6)
        assert n.name_ar == "الفرضية"
        assert n.testable is True

    def test_irab_vector_nucleus(self):
        n = IrabVectorNucleus(
            token="الكِتَابُ",
            case_name="رفع",
            confidence=0.9,
        )
        assert n.case_vector[0] == 0.9  # رفع في موضع 0
        assert n.case_vector[1] == 0.0  # نصب = 0

    def test_qiyas_nucleus(self):
        n = QiyasNucleus(
            asl="الخمر",
            far_="النبيذ",
            illa="الإسكار",
            hukm_asl="حرام",
        )
        assert n.asl == "الخمر"
        assert n.illa == "الإسكار"
        assert not n.is_valid

    def test_taarud_tarjih_apply(self):
        n = TaarudTarjihNucleus(
            candidates=["حكم أ", "حكم ب"],
            weights=[0.6, 0.9],
        )
        winner = n.apply()
        assert winner == "حكم ب"
        assert n.winner == "حكم ب"

    def test_lower_layers_bind(self):
        n = LowerLayersNucleus()
        n.bind_engine("صوتي", "PhonemesEngine")
        assert n.engine_bindings["صوتي"] == "PhonemesEngine"

    def test_nucleus_summary(self):
        n = ShahadaNucleus()
        summary = n.summary()
        assert "الشهادة" in summary
        assert "Shahada" in summary


# ===========================================================================
# 4. وحدات يونيكود
# ===========================================================================

class TestUnicodeUnits:
    """اختبارات ArabicUnit وArabicText."""

    def test_arabic_unit_letter(self):
        u = ArabicUnit.from_char("ك", pos=0)
        assert u.kind == UnitKind.LETTER
        assert u.codepoint == 0x0643
        assert u.codepoint_str == "U+0643"
        assert u.is_letter()
        assert not u.is_diacritic()

    def test_arabic_unit_fatha(self):
        u = ArabicUnit.from_char("\u064E")  # فتحة
        assert u.kind == UnitKind.HARAKA
        assert u.is_diacritic()
        assert u.name_ar == "فتحة"

    def test_arabic_unit_shadda(self):
        u = ArabicUnit.from_char("\u0651")  # شدة
        assert u.kind == UnitKind.SHADDA

    def test_arabic_unit_tanwin(self):
        u = ArabicUnit.from_char("\u064C")  # تنوين ضم
        assert u.kind == UnitKind.TANWIN

    def test_arabic_unit_sukun(self):
        u = ArabicUnit.from_char("\u0652")  # سكون
        assert u.kind == UnitKind.SUKUN

    def test_arabic_unit_space(self):
        u = ArabicUnit.from_char(" ")
        assert u.kind == UnitKind.SPACE

    def test_arabic_unit_invalid_multi(self):
        with pytest.raises(ValueError):
            ArabicUnit.from_char("كت")

    def test_arabic_text_from_string(self):
        text = ArabicText.from_string("كَ")
        assert len(text) == 2  # كاف + فتحة
        assert text.units[0].char == "ك"
        assert text.units[1].kind == UnitKind.HARAKA

    def test_arabic_text_tokens(self):
        text = ArabicText.from_string("الكِتَابُ مُفِيدٌ")
        tokens = text.tokens()
        assert len(tokens) == 2
        assert tokens[0].raw == "الكِتَابُ"
        assert tokens[1].raw == "مُفِيدٌ"

    def test_token_letters_only(self):
        text = ArabicText.from_string("مُفِيدٌ")
        tokens = text.tokens()
        assert len(tokens) == 1
        bare = tokens[0].letters_only()
        assert "م" in bare
        assert "ف" in bare
        # لا حركات
        assert "\u064F" not in bare

    def test_arabic_text_stats(self):
        text = ArabicText.from_string("كِتَابٌ")
        stats = text.stats()
        assert stats["total_units"] > 0
        assert stats["letter_count"] > 0
        assert stats["token_count"] == 1

    def test_arabic_text_codepoints(self):
        text = ArabicText.from_string("ك")
        tokens = text.tokens()
        cps = tokens[0].codepoints()
        assert "U+0643" in cps


# ===========================================================================
# 5. استخلاص الأثر
# ===========================================================================

class TestTraceExtractor:
    """اختبارات TraceExtractor."""

    def setup_method(self):
        self.extractor = TraceExtractor()

    def test_extract_surface(self):
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        rt = self.extractor.extract(r, TraceLevel.SURFACE)
        assert isinstance(rt, RichTrace)
        assert len(rt.tokens) == 2
        assert rt.base.level == TraceLevel.SURFACE

    def test_extract_token_analyses(self):
        r = Reality(raw_text="كِتَابٌ")
        rt = self.extractor.extract(r)
        assert len(rt.token_analyses) == 1
        ta = rt.token_analyses[0]
        assert ta["token"] == "كِتَابٌ"
        assert len(ta["units"]) > 0

    def test_unit_analysis_has_cause_effect(self):
        r = Reality(raw_text="كِتَابٌ")
        rt = self.extractor.extract(r)
        units = rt.token_analyses[0]["units"]
        for u in units:
            assert "cause" in u
            assert "effect" in u
            assert "function" in u

    def test_extract_caches(self):
        r = Reality(raw_text="كِتَابٌ")
        rt1 = self.extractor.extract(r)
        rt2 = self.extractor.extract(r)
        assert rt1 is rt2  # نفس الكائن من الـ cache

    def test_extract_full_has_all_levels(self):
        r = Reality(raw_text="الكِتَابُ")
        rt = self.extractor.extract_full(r)
        assert "surface" in rt.level_data
        assert "phonemic" in rt.level_data
        assert "morphemic" in rt.level_data
        assert "syntactic" in rt.level_data
        assert "semantic" in rt.level_data

    def test_extract_phonemic_has_harakat(self):
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        rt = self.extractor.extract(r, TraceLevel.PHONEMIC)
        assert "phonemic" in rt.level_data
        phonemic = rt.level_data["phonemic"]
        assert "harakat_sequence" in phonemic
        assert isinstance(phonemic["harakat_sequence"], list)


# ===========================================================================
# 6. خط الأنابيب (end-to-end)
# ===========================================================================

class TestPipeline:
    """اختبارات AnalysisPipeline الشاملة."""

    def setup_method(self):
        self.pipeline = AnalysisPipeline()

    def test_run_basic(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        assert isinstance(analysis, StagedAnalysis)
        assert analysis.input_text == "الكِتَابُ مُفِيدٌ"

    def test_all_11_stages_present(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        stages = [sr.stage for sr in analysis.stage_results]
        for stage in PipelineStage:
            assert stage in stages, f"المرحلة {stage} مفقودة"

    def test_stage_1_arabic_text_is_shahada(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        stage1 = analysis.get_stage(PipelineStage.OBSERVED_REALITY)
        assert stage1 is not None
        assert stage1.output.kind == OutputKind.SHAHADA

    def test_stage_1_empty_text_is_zero(self):
        analysis = self.pipeline.run("   ")
        stage1 = analysis.get_stage(PipelineStage.OBSERVED_REALITY)
        assert stage1 is not None
        assert stage1.output.kind == OutputKind.EPISTEMIC_ZERO

    def test_stage_2_produces_trace(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        assert analysis.rich_trace is not None
        stage2 = analysis.get_stage(PipelineStage.CONFIRMED_TRACE)
        assert stage2 is not None
        assert not stage2.is_zero

    def test_final_output_not_none(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        assert analysis.final_output is not None

    def test_final_output_is_shahada_or_hypothesis(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        assert analysis.final_output.kind in (
            OutputKind.SHAHADA,
            OutputKind.HYPOTHESIS,
        )

    def test_summary_contains_stage_names(self):
        analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")
        summary = analysis.summary()
        assert "واقع مشهود" in summary
        assert "أثر مثبت" in summary

    def test_stage_names_complete(self):
        assert len(STAGE_NAMES_AR) == 11
        assert len(STAGE_NAMES_EN) == 11

    def test_non_arabic_text(self):
        analysis = self.pipeline.run("Hello world")
        stage1 = analysis.get_stage(PipelineStage.OBSERVED_REALITY)
        # يُعطي فرضية لا شهادة
        assert stage1 is not None
        assert stage1.output.kind in (
            OutputKind.HYPOTHESIS,
            OutputKind.EPISTEMIC_ZERO,
        )

    def test_single_word(self):
        analysis = self.pipeline.run("كِتَابٌ")
        assert analysis.final_output is not None

    def test_pipeline_stop_on_zero(self):
        """مع stop_on_zero=True، النص الفارغ يوقف السلسلة مبكراً."""
        pipeline = AnalysisPipeline(stop_on_zero=True)
        analysis = pipeline.run("")
        # مرحلة واحدة فقط (واقع مشهود)
        assert len(analysis.stage_results) == 1

    def test_pipeline_no_stop_on_zero(self):
        """مع stop_on_zero=False، جميع المراحل تُنفَّذ حتى مع صفر."""
        pipeline = AnalysisPipeline(stop_on_zero=False)
        analysis = pipeline.run("")
        assert len(analysis.stage_results) == 11


# ===========================================================================
# 7. التسلسل
# ===========================================================================

class TestSerialization:
    """اختبارات serialize/load."""

    def setup_method(self):
        self.pipeline = AnalysisPipeline()
        self.analysis = self.pipeline.run("الكِتَابُ مُفِيدٌ")

    def test_serialize_returns_valid_json(self):
        import json
        json_str = serialize_analysis(self.analysis)
        data = json.loads(json_str)
        assert "input_text" in data
        assert "stages" in data
        assert len(data["stages"]) == 11

    def test_serialize_contains_arabic(self):
        json_str = serialize_analysis(self.analysis)
        assert "واقع مشهود" in json_str

    def test_load_analysis_from_str(self):
        json_str = serialize_analysis(self.analysis)
        loaded = load_analysis(json_str)
        assert loaded["input_text"] == "الكِتَابُ مُفِيدٌ"
        assert len(loaded["stages"]) == 11

    def test_load_analysis_from_dict(self):
        data = self.analysis.to_dict()
        loaded = load_analysis(data)
        assert loaded == data

    def test_format_analysis_text(self):
        text = format_analysis_text(self.analysis)
        assert "الكِتَابُ مُفِيدٌ" in text
        assert "واقع مشهود" in text

    def test_format_trace_units(self):
        text = format_trace_units(self.analysis)
        assert "U+" in text  # يحتوي نقاط كود
        assert len(text) > 10

    def test_save_and_load_file(self, tmp_path):
        from foundation.serialization import save_analysis
        path = tmp_path / "analysis.json"
        saved = save_analysis(self.analysis, path)
        assert saved.exists()
        loaded = load_analysis(saved)
        assert loaded["input_text"] == "الكِتَابُ مُفِيدٌ"


# ===========================================================================
# 8. اختبارات تكاملية
# ===========================================================================

class TestIntegration:
    """اختبارات تكاملية متعددة الأمثلة."""

    EXAMPLES = [
        "الكِتَابُ مُفِيدٌ",
        "قَرَأَ الطَّالِبُ الدَّرْسَ",
        "لَا إِلَهَ إِلَّا اللَّهُ",
        "كِتَابٌ",
        "بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ",
    ]

    def test_pipeline_on_all_examples(self):
        pipeline = AnalysisPipeline()
        for text in self.EXAMPLES:
            analysis = pipeline.run(text)
            assert analysis is not None, f"فشل على: {text}"
            assert analysis.final_output is not None, f"لا مخرج لـ: {text}"
            assert len(analysis.stage_results) == 11

    def test_unicode_analysis_on_all_examples(self):
        for text in self.EXAMPLES:
            at = ArabicText.from_string(text)
            assert len(at) > 0
            stats = at.stats()
            assert stats["letter_count"] > 0

    def test_trace_extractor_on_all_examples(self):
        extractor = TraceExtractor()
        for text in self.EXAMPLES:
            r = Reality(raw_text=text)
            rt = extractor.extract(r)
            assert len(rt.tokens) > 0

    def test_serialization_round_trip(self):
        import json
        pipeline = AnalysisPipeline()
        for text in self.EXAMPLES:
            analysis = pipeline.run(text)
            json_str = serialize_analysis(analysis)
            loaded = load_analysis(json_str)
            assert loaded["input_text"] == text
