"""
الدالة الجامعة — Unified Reasoning Pipeline
============================================
يُطبِّق هذا الملف الدالة الجامعة المُعرَّفة في «الوثيقة الرياضية التأسيسية»:

    1.  واقع مشهود         → ObservedReality
    2.  أثر مثبت           → ConfirmedTrace
    3.  تصور متعين          → DeterminedConception
    4.  مفهوم محدود         → BoundedConcept
    5.  دلالة مضبوطة        → ConstrainedSignification
    6.  نسبة ذات طرفين      → BinaryRelation
    7.  حكم مرشح           → CandidateRuling
    8.  تحقيق مناط          → ManatActualization
    9.  حكم مطبق           → AppliedRuling
    10. قياس               → Analogy  (عند وجود علة وفرع)
    11. أثر الحكم في الواقع  → BehavioralEffect

كل مرحلة:
- تأخذ مدخل من المرحلة السابقة
- تُنتج StageResult يحمل SystemOutput + بيانات الحالة
- يمكن أن تتوقف إذا كانت المخرجات صفراً معرفياً

الاستخدام:
    pipeline = AnalysisPipeline()
    result = pipeline.run("الكِتَابُ مُفِيدٌ")
    print(result.summary())
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional

from .ontology import Reality, RealityKind, TraceLevel
from .outputs import (
    OutputKind,
    SystemOutput,
    Shahada,
    Hypothesis,
    EpistemicZero,
    OutputList,
)
from .trace import TraceExtractor, RichTrace
from .unicode_units import ArabicText


# ---------------------------------------------------------------------------
# ثوابت حساب درجة الثقة
# ---------------------------------------------------------------------------

# المرحلة 2: حساب ثقة الأثر
BASE_TRACE_CONFIDENCE: float = 0.5
TOKEN_CONFIDENCE_INCREMENT: float = 0.1

# الأفعال العربية — بادئات الفعل المضارع وصيغ الفعل الماضي
VERB_PREFIXES = ("فَ", "يَ", "تَ", "نَ", "أَ", "سَ")


# ---------------------------------------------------------------------------
# أسماء المراحل
# ---------------------------------------------------------------------------

class PipelineStage(Enum):
    """المراحل الإحدى عشرة للدالة الجامعة."""
    OBSERVED_REALITY       = 1   # واقع مشهود
    CONFIRMED_TRACE        = 2   # أثر مثبت
    DETERMINED_CONCEPTION  = 3   # تصور متعين
    BOUNDED_CONCEPT        = 4   # مفهوم محدود
    SIGNIFICATION          = 5   # دلالة مضبوطة
    BINARY_RELATION        = 6   # نسبة ذات طرفين
    CANDIDATE_RULING       = 7   # حكم مرشح
    MANAT_ACTUALIZATION    = 8   # تحقيق مناط
    APPLIED_RULING         = 9   # حكم مطبق
    ANALOGY                = 10  # قياس
    BEHAVIORAL_EFFECT      = 11  # أثر الحكم في الواقع والسلوك


STAGE_NAMES_AR: Dict[PipelineStage, str] = {
    PipelineStage.OBSERVED_REALITY:      "واقع مشهود",
    PipelineStage.CONFIRMED_TRACE:       "أثر مثبت",
    PipelineStage.DETERMINED_CONCEPTION: "تصور متعين",
    PipelineStage.BOUNDED_CONCEPT:       "مفهوم محدود",
    PipelineStage.SIGNIFICATION:         "دلالة مضبوطة",
    PipelineStage.BINARY_RELATION:       "نسبة ذات طرفين",
    PipelineStage.CANDIDATE_RULING:      "حكم مرشح",
    PipelineStage.MANAT_ACTUALIZATION:   "تحقيق مناط",
    PipelineStage.APPLIED_RULING:        "حكم مطبق",
    PipelineStage.ANALOGY:               "قياس عند وجود علة وفرع",
    PipelineStage.BEHAVIORAL_EFFECT:     "أثر الحكم في الواقع والسلوك",
}

STAGE_NAMES_EN: Dict[PipelineStage, str] = {
    PipelineStage.OBSERVED_REALITY:      "Observed Reality",
    PipelineStage.CONFIRMED_TRACE:       "Confirmed Trace",
    PipelineStage.DETERMINED_CONCEPTION: "Determined Conception",
    PipelineStage.BOUNDED_CONCEPT:       "Bounded Concept",
    PipelineStage.SIGNIFICATION:         "Constrained Signification",
    PipelineStage.BINARY_RELATION:       "Binary Relation",
    PipelineStage.CANDIDATE_RULING:      "Candidate Ruling",
    PipelineStage.MANAT_ACTUALIZATION:   "Manat Actualization",
    PipelineStage.APPLIED_RULING:        "Applied Ruling",
    PipelineStage.ANALOGY:               "Analogy",
    PipelineStage.BEHAVIORAL_EFFECT:     "Behavioral Effect",
}


# ---------------------------------------------------------------------------
# نتيجة مرحلة مفردة
# ---------------------------------------------------------------------------

@dataclass
class StageResult:
    """
    نتيجة تنفيذ مرحلة واحدة من الدالة الجامعة.

    stage   — رقم المرحلة واسمها
    output  — مخرج النظام (شهادة | فرضية | صفر)
    data    — بيانات داخلية للمرحلة (للتفتيش والتتبع)
    """
    stage: PipelineStage
    output: SystemOutput
    data: Dict[str, Any] = field(default_factory=dict)

    @property
    def stage_name_ar(self) -> str:
        return STAGE_NAMES_AR[self.stage]

    @property
    def is_zero(self) -> bool:
        return self.output.kind == OutputKind.EPISTEMIC_ZERO

    def __repr__(self) -> str:
        return (
            f"StageResult({self.stage.value}: {self.stage_name_ar!r}, "
            f"output={self.output.kind.value}, conf={self.output.confidence:.2f})"
        )


# ---------------------------------------------------------------------------
# نتيجة التحليل الكامل
# ---------------------------------------------------------------------------

@dataclass
class StagedAnalysis:
    """
    نتيجة التحليل الكامل عبر جميع مراحل الدالة الجامعة.

    input_text    — النص المُدخَل
    reality       — كائن الواقع
    rich_trace    — الأثر الغني
    stage_results — نتائج المراحل بالترتيب
    final_output  — المخرج النهائي
    outputs       — قائمة كل مخرجات النظام
    """
    input_text: str
    reality: Reality
    rich_trace: Optional[RichTrace] = None
    stage_results: List[StageResult] = field(default_factory=list)
    final_output: Optional[SystemOutput] = None
    outputs: OutputList = field(default_factory=OutputList)

    def get_stage(self, stage: PipelineStage) -> Optional[StageResult]:
        for r in self.stage_results:
            if r.stage == stage:
                return r
        return None

    def completed_stages(self) -> List[PipelineStage]:
        return [r.stage for r in self.stage_results]

    def summary(self) -> str:
        """ملخص نصي قابل للقراءة."""
        lines = [
            "=" * 60,
            f"التحليل: {self.input_text}",
            "=" * 60,
        ]
        for sr in self.stage_results:
            kind_icon = {"شهادة": "✓", "فرضية": "~", "صفر_معرفي": "✗"}.get(
                sr.output.kind.value, "?"
            )
            lines.append(
                f"  [{sr.stage.value:2d}] {sr.stage_name_ar:20s}  "
                f"{kind_icon} {sr.output.kind.value:12s}  "
                f"conf={sr.output.confidence:.2f}"
            )
        lines.append("-" * 60)
        if self.final_output:
            lines.append(
                f"النتيجة النهائية: {self.final_output.kind.value} "
                f"(ثقة={self.final_output.confidence:.2f})"
            )
        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "input_text": self.input_text,
            "reality_uid": self.reality.uid,
            "trace_uid": self.rich_trace.uid if self.rich_trace else None,
            "stages": [
                {
                    "stage_number": sr.stage.value,
                    "stage_name_ar": sr.stage_name_ar,
                    "stage_name_en": STAGE_NAMES_EN[sr.stage],
                    "output_kind": sr.output.kind.value,
                    "confidence": sr.output.confidence,
                    "content": str(sr.output.content),
                    "justification": sr.output.justification,
                    "data": sr.data,
                }
                for sr in self.stage_results
            ],
            "final_output": {
                "kind": self.final_output.kind.value,
                "confidence": self.final_output.confidence,
                "content": str(self.final_output.content),
            } if self.final_output else None,
        }


# ---------------------------------------------------------------------------
# خط الأنابيب الرئيسي
# ---------------------------------------------------------------------------

class AnalysisPipeline:
    """
    خط أنابيب التحليل — يُنفِّذ الدالة الجامعة كاملةً.

    الاستخدام:
        pipeline = AnalysisPipeline()
        analysis = pipeline.run("الكِتَابُ مُفِيدٌ")
        print(analysis.summary())

    يمكن تخصيص أي مرحلة بتمرير handler مخصص في stage_overrides.
    """

    def __init__(
        self,
        trace_level: TraceLevel = TraceLevel.SURFACE,
        stop_on_zero: bool = True,
    ) -> None:
        """
        المعاملات:
            trace_level    — مستوى استخلاص الأثر
            stop_on_zero   — إيقاف السلسلة عند أول صفر معرفي
        """
        self.trace_level = trace_level
        self.stop_on_zero = stop_on_zero
        self._extractor = TraceExtractor()

    # ------------------------------------------------------------------
    # نقطة الدخول
    # ------------------------------------------------------------------

    def run(self, text: str, source: Optional[str] = None) -> StagedAnalysis:
        """
        يُنفِّذ الدالة الجامعة الكاملة على نص عربي.

        المعاملات:
            text   — النص العربي المُراد تحليله
            source — مصدر النص (اختياري)

        يُعيد: StagedAnalysis
        """
        # إنشاء الواقع
        reality = Reality(
            raw_text=text,
            kind=RealityKind.TEXT,
            source=source,
        )

        analysis = StagedAnalysis(
            input_text=text,
            reality=reality,
        )

        # تنفيذ المراحل بالترتيب
        self._run_stage_1(analysis)
        if self.stop_on_zero and self._last_is_zero(analysis):
            return self._finalize(analysis)

        self._run_stage_2(analysis)
        if self.stop_on_zero and self._last_is_zero(analysis):
            return self._finalize(analysis)

        self._run_stage_3(analysis)
        self._run_stage_4(analysis)
        self._run_stage_5(analysis)
        self._run_stage_6(analysis)
        self._run_stage_7(analysis)
        self._run_stage_8(analysis)
        self._run_stage_9(analysis)
        self._run_stage_10(analysis)
        self._run_stage_11(analysis)

        return self._finalize(analysis)

    # ------------------------------------------------------------------
    # المراحل
    # ------------------------------------------------------------------

    def _run_stage_1(self, analysis: StagedAnalysis) -> None:
        """المرحلة 1: واقع مشهود — التحقق من صحة الإدخال."""
        text = analysis.input_text.strip()
        is_arabic = any("\u0600" <= ch <= "\u06FF" for ch in text)

        if not text:
            result = StageResult(
                stage=PipelineStage.OBSERVED_REALITY,
                output=EpistemicZero("النص فارغ", stage="واقع مشهود",
                                      trace_uid=analysis.reality.uid),
            )
        elif not is_arabic:
            result = StageResult(
                stage=PipelineStage.OBSERVED_REALITY,
                output=Hypothesis(
                    f"نص غير عربي: {text[:20]}",
                    confidence=0.3,
                    stage="واقع مشهود",
                    trace_uid=analysis.reality.uid,
                    justification="النص لا يحتوي على حروف عربية",
                ),
                data={"is_arabic": False},
            )
        else:
            result = StageResult(
                stage=PipelineStage.OBSERVED_REALITY,
                output=Shahada(
                    text,
                    confidence=1.0,
                    stage="واقع مشهود",
                    trace_uid=analysis.reality.uid,
                    justification="نص عربي صحيح مُدخَل",
                ),
                data={"is_arabic": True, "char_count": len(text)},
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_2(self, analysis: StagedAnalysis) -> None:
        """المرحلة 2: أثر مثبت — استخلاص الأثر من الواقع."""
        rich_trace = self._extractor.extract(
            analysis.reality, self.trace_level
        )
        analysis.rich_trace = rich_trace

        if rich_trace.base.is_empty():
            result = StageResult(
                stage=PipelineStage.CONFIRMED_TRACE,
                output=EpistemicZero(
                    "الأثر فارغ",
                    stage="أثر مثبت",
                    trace_uid=rich_trace.uid,
                ),
            )
        else:
            conf = min(1.0, BASE_TRACE_CONFIDENCE + len(rich_trace.tokens) * TOKEN_CONFIDENCE_INCREMENT)
            result = StageResult(
                stage=PipelineStage.CONFIRMED_TRACE,
                output=Shahada(
                    f"أثر مُثبَت: {len(rich_trace.tokens)} كلمة، "
                    f"{len(rich_trace.arabic_text)} وحدة",
                    confidence=conf,
                    stage="أثر مثبت",
                    trace_uid=rich_trace.uid,
                    justification="الأثر مُستخلَص بنجاح",
                ),
                data=rich_trace.to_dict(),
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_3(self, analysis: StagedAnalysis) -> None:
        """المرحلة 3: تصور متعين — تحديد الوحدات الأساسية."""
        trace = analysis.rich_trace
        if trace is None:
            analysis.stage_results.append(StageResult(
                stage=PipelineStage.DETERMINED_CONCEPTION,
                output=EpistemicZero("لا أثر", stage="تصور متعين"),
            ))
            return

        tokens = trace.tokens
        token_analyses = trace.token_analyses
        conceived = [t["letters_only"] for t in token_analyses if t.get("letters_only")]

        result = StageResult(
            stage=PipelineStage.DETERMINED_CONCEPTION,
            output=Shahada(
                conceived,
                confidence=0.9,
                stage="تصور متعين",
                trace_uid=trace.uid,
                justification="الوحدات الأساسية مُتعيَّنة",
            ),
            data={"conceived_units": conceived, "token_count": len(tokens)},
        )
        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_4(self, analysis: StagedAnalysis) -> None:
        """المرحلة 4: مفهوم محدود — تصنيف الوحدات."""
        trace = analysis.rich_trace
        if trace is None:
            analysis.stage_results.append(StageResult(
                stage=PipelineStage.BOUNDED_CONCEPT,
                output=EpistemicZero("لا أثر", stage="مفهوم محدود"),
            ))
            return

        # تصنيف بسيط: هل الجملة فعلية أم اسمية؟
        first_token = trace.tokens[0] if trace.tokens else ""
        is_verbal = any(first_token.startswith(p) for p in VERB_PREFIXES)

        concept = "جملة فعلية" if is_verbal else "جملة اسمية أو غير محددة"

        result = StageResult(
            stage=PipelineStage.BOUNDED_CONCEPT,
            output=Hypothesis(
                concept,
                confidence=0.65,
                stage="مفهوم محدود",
                trace_uid=trace.uid if trace else "",
                justification="تصنيف أولي بناءً على أول كلمة",
            ),
            data={"concept": concept, "first_token": first_token},
        )
        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_5(self, analysis: StagedAnalysis) -> None:
        """المرحلة 5: دلالة مضبوطة — العلاقة بين اللفظ والمعنى."""
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""
        tokens = trace.tokens if trace else []

        # في v0.1: نُثبِّت دلالة عامة على الكلمات
        dalala_entries = [
            {"lafz": tok, "mana": f"[دلالة {tok} غير مُحدَّدة في v0.1]"}
            for tok in tokens
        ]

        result = StageResult(
            stage=PipelineStage.SIGNIFICATION,
            output=Hypothesis(
                dalala_entries,
                confidence=0.5,
                stage="دلالة مضبوطة",
                trace_uid=trace_uid,
                justification="دلالة أولية — الربط الكامل بالمعجم في v0.2",
            ),
            data={"dalala": dalala_entries},
        )
        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_6(self, analysis: StagedAnalysis) -> None:
        """المرحلة 6: نسبة ذات طرفين — العلاقة الإسنادية."""
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""
        tokens = trace.tokens if trace else []

        if len(tokens) >= 2:
            relation = {
                "subject": tokens[0],
                "predicate": tokens[1] if len(tokens) > 1 else "؟",
                "type": "إسناد",
            }
            conf = 0.7
            justification = "علاقة إسنادية مُستخلَصة (تحليل أعمق في v0.2)"
        else:
            relation = {"note": "لا يكفي الكلمات لتشكيل نسبة"}
            conf = 0.3
            justification = "عدد الكلمات غير كافٍ للنسبة الإسنادية"

        result = StageResult(
            stage=PipelineStage.BINARY_RELATION,
            output=Hypothesis(
                relation,
                confidence=conf,
                stage="نسبة ذات طرفين",
                trace_uid=trace_uid,
                justification=justification,
            ),
            data={"relation": relation},
        )
        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_7(self, analysis: StagedAnalysis) -> None:
        """المرحلة 7: حكم مرشح — الحكم الأولي قبل التحقق."""
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""

        # الحكم المرشح مبني على الدلالة والنسبة
        stage5 = analysis.get_stage(PipelineStage.SIGNIFICATION)
        stage6 = analysis.get_stage(PipelineStage.BINARY_RELATION)

        combined_conf = min(
            (stage5.output.confidence if stage5 else 0.5),
            (stage6.output.confidence if stage6 else 0.5),
        )

        ruling = {
            "ruling_text": "يحتمل الإخبار",
            "is_applied": False,
            "confidence": combined_conf,
        }

        result = StageResult(
            stage=PipelineStage.CANDIDATE_RULING,
            output=Hypothesis(
                ruling,
                confidence=combined_conf,
                stage="حكم مرشح",
                trace_uid=trace_uid,
                justification="حكم مرشح بانتظار تحقيق المناط",
            ),
            data={"candidate_ruling": ruling},
        )
        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_8(self, analysis: StagedAnalysis) -> None:
        """المرحلة 8: تحقيق المناط — التثبت من انطباق العلة."""
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""

        # في v0.1: التثبت يعتمد على وجود أثر مُثبَت كافٍ
        stage2 = analysis.get_stage(PipelineStage.CONFIRMED_TRACE)
        has_trace = (
            stage2 is not None
            and stage2.output.kind != OutputKind.EPISTEMIC_ZERO
        )

        if has_trace:
            result = StageResult(
                stage=PipelineStage.MANAT_ACTUALIZATION,
                output=Shahada(
                    "المناط محقَّق: الأثر ثابت والإسناد ممكن",
                    confidence=0.75,
                    stage="تحقيق مناط",
                    trace_uid=trace_uid,
                    justification="تحقق المناط بوجود أثر كافٍ",
                ),
                data={"manat_verified": True},
            )
        else:
            result = StageResult(
                stage=PipelineStage.MANAT_ACTUALIZATION,
                output=EpistemicZero(
                    "لم يتحقق المناط: لا أثر كافٍ",
                    stage="تحقيق مناط",
                    trace_uid=trace_uid,
                ),
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_9(self, analysis: StagedAnalysis) -> None:
        """المرحلة 9: حكم مطبق — الحكم بعد التحقق."""
        stage7 = analysis.get_stage(PipelineStage.CANDIDATE_RULING)
        stage8 = analysis.get_stage(PipelineStage.MANAT_ACTUALIZATION)
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""

        manat_ok = (
            stage8 is not None
            and stage8.output.kind != OutputKind.EPISTEMIC_ZERO
        )

        if not manat_ok:
            result = StageResult(
                stage=PipelineStage.APPLIED_RULING,
                output=EpistemicZero(
                    "الحكم لا يُطبَّق: المناط لم يتحقق",
                    stage="حكم مطبق",
                ),
            )
        else:
            cand_conf = stage7.output.confidence if stage7 else 0.5
            applied_conf = min(1.0, cand_conf + 0.1)
            applied_out = Shahada(
                "حكم مطبق: الإخبار بالإسناد",
                confidence=applied_conf,
                stage="حكم مطبق",
                trace_uid=trace_uid,
                justification="الحكم مُطبَّق بعد تحقق المناط",
            ).promote()
            result = StageResult(
                stage=PipelineStage.APPLIED_RULING,
                output=applied_out,
                data={"applied": True},
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_10(self, analysis: StagedAnalysis) -> None:
        """المرحلة 10: قياس — عند وجود علة وفرع."""
        stage9 = analysis.get_stage(PipelineStage.APPLIED_RULING)
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""

        # في v0.1 القياس placeholder — يُفعَّل عند إضافة قاعدة قياس
        if stage9 and stage9.output.kind != OutputKind.EPISTEMIC_ZERO:
            result = StageResult(
                stage=PipelineStage.ANALOGY,
                output=Hypothesis(
                    "لا قياس صريح في هذا السياق (v0.1)",
                    confidence=0.4,
                    stage="قياس",
                    trace_uid=trace_uid,
                    justification="القياس يتطلب علة وفرعاً صريحين — v0.2",
                ),
                data={"qiyas_applicable": False},
            )
        else:
            result = StageResult(
                stage=PipelineStage.ANALOGY,
                output=EpistemicZero(
                    "لا قياس: الحكم لم يُطبَّق",
                    stage="قياس",
                ),
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    def _run_stage_11(self, analysis: StagedAnalysis) -> None:
        """المرحلة 11: أثر الحكم في الواقع والسلوك."""
        stage9 = analysis.get_stage(PipelineStage.APPLIED_RULING)
        trace = analysis.rich_trace
        trace_uid = trace.uid if trace else ""

        if stage9 and stage9.output.kind == OutputKind.SHAHADA:
            effect = {
                "behavioral_effect": "فهم المعنى وتحديد الموقف",
                "reality_effect": "تغيير المعرفة المخزونة",
                "scope": "فردي",
            }
            result = StageResult(
                stage=PipelineStage.BEHAVIORAL_EFFECT,
                output=Shahada(
                    effect,
                    confidence=stage9.output.confidence * 0.9,
                    stage="أثر الحكم",
                    trace_uid=trace_uid,
                    justification="أثر الحكم المُطبَّق في الفهم والسلوك",
                ),
                data={"effect": effect},
            )
        else:
            result = StageResult(
                stage=PipelineStage.BEHAVIORAL_EFFECT,
                output=EpistemicZero(
                    "لا أثر: الحكم لم يُطبَّق",
                    stage="أثر الحكم",
                ),
            )

        analysis.stage_results.append(result)
        analysis.outputs.add(result.output)

    # ------------------------------------------------------------------
    # الإنهاء
    # ------------------------------------------------------------------

    @staticmethod
    def _last_is_zero(analysis: StagedAnalysis) -> bool:
        if not analysis.stage_results:
            return False
        return analysis.stage_results[-1].is_zero

    @staticmethod
    def _finalize(analysis: StagedAnalysis) -> StagedAnalysis:
        best = analysis.outputs.best()
        if best:
            analysis.final_output = best.promote()
        else:
            analysis.final_output = EpistemicZero(
                "جميع المراحل أفضت إلى صفر معرفي"
            )
        return analysis
