"""
مخرجات النظام — System Outputs
================================
يُعرِّف هذا الملف مخرجات نظام «العقل الباني» الثلاثة:

    1. شهادة   (Shahada)      — نتيجة مُتحقَّق منها قابلة للإثبات
    2. فرضية   (Hypothesis)   — نتيجة مُحتمَلة تحتاج مزيداً من التحقق
    3. صفر معرفي (EpistemicZero) — غياب الأثر أو انعدام المعرفة الكافية

كل مخرج يحمل:
- درجة ثقة (confidence ∈ [0, 1])
- المرحلة التي أنتجته
- الأثر الذي استُند إليه
- تبريراً نصياً (justification)

هذا التمييز الثلاثي مأخوذ من الوثيقة التأسيسية مباشرةً ويُطابق التقليدَ
المنطقي/الفقهي: (يقين | ظن | جهل).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional


class OutputKind(Enum):
    """
    نوع المخرج

    SHAHADA        — شهادة: يقين منطقي (confidence ≥ threshold)
    HYPOTHESIS     — فرضية: احتمال معقول (0 < confidence < threshold)
    EPISTEMIC_ZERO — صفر معرفي: لا أثر كافٍ أو تعارض لا يُرجَّح
    """
    SHAHADA = "شهادة"
    HYPOTHESIS = "فرضية"
    EPISTEMIC_ZERO = "صفر_معرفي"


# الحدّ الأدنى للثقة لترقية فرضية إلى شهادة
SHAHADA_CONFIDENCE_THRESHOLD: float = 0.80


@dataclass
class SystemOutput:
    """
    المخرج العام للنظام
    ====================
    يُغلِّف نتيجة أي مرحلة في سلسلة التحليل.

    الحقول:
        kind           — نوع المخرج (شهادة / فرضية / صفر معرفي)
        content        — المحتوى الرئيسي للمخرج (نص أو بنية)
        confidence     — درجة الثقة [0, 1]
        stage          — اسم المرحلة المُنتِجة
        trace_uid      — uid الأثر المُستند إليه
        justification  — تبرير نصي موجز
        metadata       — بيانات وصفية إضافية
    """
    kind: OutputKind
    content: Any
    confidence: float = 0.0
    stage: str = ""
    trace_uid: str = ""
    justification: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)

    # ------------------------------------------------------------------
    # تحويل ديناميكي
    # ------------------------------------------------------------------

    def promote(self) -> "SystemOutput":
        """
        يُحاوِل ترقية فرضية إلى شهادة إذا تجاوزت درجة الثقة العتبة.
        يُعيد نسخةً جديدة (لا يُعدِّل المخرج الأصلي).
        """
        if (
            self.kind == OutputKind.HYPOTHESIS
            and self.confidence >= SHAHADA_CONFIDENCE_THRESHOLD
        ):
            return SystemOutput(
                kind=OutputKind.SHAHADA,
                content=self.content,
                confidence=self.confidence,
                stage=self.stage,
                trace_uid=self.trace_uid,
                justification=self.justification + " [مُرقَّى إلى شهادة]",
                metadata=dict(self.metadata),
            )
        return self

    def is_epistemic_zero(self) -> bool:
        return self.kind == OutputKind.EPISTEMIC_ZERO

    def __repr__(self) -> str:
        preview = str(self.content)[:40]
        return (
            f"SystemOutput({self.kind.value}, conf={self.confidence:.2f}, "
            f"stage={self.stage!r}, content={preview!r})"
        )


# ---------------------------------------------------------------------------
# منشئات مُختصَرة
# ---------------------------------------------------------------------------

def Shahada(
    content: Any,
    *,
    confidence: float = 1.0,
    stage: str = "",
    trace_uid: str = "",
    justification: str = "",
    metadata: Optional[Dict[str, Any]] = None,
) -> SystemOutput:
    """
    شهادة — مخرج متيقَّن (confidence ≥ 0.80 عادةً).

    مثال:
        out = Shahada("الكِتَابُ اسم مرفوع", confidence=0.95, stage="الحكم")
    """
    return SystemOutput(
        kind=OutputKind.SHAHADA,
        content=content,
        confidence=confidence,
        stage=stage,
        trace_uid=trace_uid,
        justification=justification,
        metadata=metadata or {},
    )


def Hypothesis(
    content: Any,
    *,
    confidence: float = 0.5,
    stage: str = "",
    trace_uid: str = "",
    justification: str = "",
    metadata: Optional[Dict[str, Any]] = None,
) -> SystemOutput:
    """
    فرضية — مخرج مُحتمَل يحتاج مزيداً من التحقق.

    مثال:
        out = Hypothesis("قد يكون الفعل لازماً", confidence=0.6, stage="المفهوم")
    """
    return SystemOutput(
        kind=OutputKind.HYPOTHESIS,
        content=content,
        confidence=confidence,
        stage=stage,
        trace_uid=trace_uid,
        justification=justification,
        metadata=metadata or {},
    )


def EpistemicZero(
    reason: str = "لا أثر كافٍ",
    *,
    stage: str = "",
    trace_uid: str = "",
    metadata: Optional[Dict[str, Any]] = None,
) -> SystemOutput:
    """
    صفر معرفي — غياب الأثر أو عدم إمكانية الحكم.

    يُمثِّل الحالةَ التي لا يكفي فيها الأثر لإصدار شهادة أو فرضية.
    وهو مخرج صريح لا غموض فيه: «لم يثبت».

    مثال:
        out = EpistemicZero("النص فارغ أو غير قابل للتحليل", stage="الأثر")
    """
    return SystemOutput(
        kind=OutputKind.EPISTEMIC_ZERO,
        content=None,
        confidence=0.0,
        stage=stage,
        trace_uid=trace_uid,
        justification=reason,
        metadata=metadata or {},
    )


# ---------------------------------------------------------------------------
# قائمة المخرجات
# ---------------------------------------------------------------------------

@dataclass
class OutputList:
    """
    قائمة مرتبة من مخرجات النظام لتتبع تراكم النتائج عبر المراحل.
    """
    outputs: List[SystemOutput] = field(default_factory=list)

    def add(self, output: SystemOutput) -> None:
        self.outputs.append(output)

    def shahadas(self) -> List[SystemOutput]:
        return [o for o in self.outputs if o.kind == OutputKind.SHAHADA]

    def hypotheses(self) -> List[SystemOutput]:
        return [o for o in self.outputs if o.kind == OutputKind.HYPOTHESIS]

    def zeros(self) -> List[SystemOutput]:
        return [o for o in self.outputs if o.kind == OutputKind.EPISTEMIC_ZERO]

    def best(self) -> Optional[SystemOutput]:
        """يُعيد المخرج الأعلى ثقةً."""
        valid = [o for o in self.outputs if not o.is_epistemic_zero()]
        return max(valid, key=lambda o: o.confidence, default=None)

    def __len__(self) -> int:
        return len(self.outputs)

    def __repr__(self) -> str:
        return (
            f"OutputList(total={len(self)}, shahadas={len(self.shahadas())}, "
            f"hypotheses={len(self.hypotheses())}, zeros={len(self.zeros())})"
        )
