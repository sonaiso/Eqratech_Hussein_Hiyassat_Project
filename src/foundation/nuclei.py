"""
النوى المفاهيمية — Conceptual Nuclei
======================================
يُعرِّف هذا الملف النوى العشرين المذكورة في «الوثيقة الرياضية التأسيسية للعقل الباني».

كل نواة هي dataclass يحمل:
- الاسم العربي والإنجليزي
- وصفاً موجزاً يربطها بالإطار الرياضي
- بيانات خاصة بها
- علاقتها بالمراحل والطبقات

النوى (بالترتيب التأسيسي):
 1. الشهادة             (Shahada)
 2. الصفر              (Sifr / EpistemicZero)
 3. الفرضية            (Faradiyya / Hypothesis)
 4. الانتقال والبوابة   (TransitionGate)
 5. التصور             (Tasawwur / Conception)
 6. المفهوم            (Mafhum / Concept)
 7. المجال             (Majal / Domain)
 8. الدلالة            (Dalala / Signification)
 9. النسبة             (Nisba / Ratio/Relation)
10. الحكم              (Hukm / Ruling/Judgment)
11. تحقيق المناط       (TahqiqManat)
12. القياس             (Qiyas / Analogy)
13. العوامل المئة      (MiataAmil / Hundred Factors)
14. الإعراب كمتجه     (IrabVector)
15. الإفادة            (Ifada / Utility)
16. أثر الحكم والسلوك  (AatharHukm / Effect on Behavior)
17. التعارض والترجيح   (TaarudTarjih / Conflict & Preponderance)
18. أهلية المستدل والملكة (Ahliyya / Reasoner Competence)
19. الواقع             (Waqi'a / Reality-Nucleus)
20. الطبقات اللغوية الدنيا (LowerLayers)
"""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional


# ---------------------------------------------------------------------------
# الفئة الأساسية
# ---------------------------------------------------------------------------

@dataclass
class Nucleus(ABC):
    """
    النواة الأساسية لكل مفهوم في نظام «العقل الباني».

    كل نواة تُمثِّل وحدةً مفاهيمية مستقلة تدخل في بناء التحليل.
    """
    name_ar: str = field(init=False)
    name_en: str = field(init=False)
    description: str = field(init=False)
    active: bool = True
    metadata: Dict[str, Any] = field(default_factory=dict)

    def summary(self) -> str:
        return f"[{self.name_ar} / {self.name_en}] {self.description}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(active={self.active})"


# ---------------------------------------------------------------------------
# النوى العشرون
# ---------------------------------------------------------------------------

@dataclass
class ShahadaNucleus(Nucleus):
    """
    1. الشهادة
    نواة اليقين والإثبات. تُمثِّل المعرفة المتحقَّق منها بأثر صريح.
    تُقابل الشهادةَ في المنطق الكلاسيكي: معلومة ثابتة بدليل.
    """
    # درجة اليقين المطلوبة للاعتراف بالشهادة
    certainty_threshold: float = 0.80
    # الأثر المُثبِت
    confirming_trace: Optional[str] = None

    def __post_init__(self) -> None:
        self.name_ar = "الشهادة"
        self.name_en = "Shahada"
        self.description = "نواة اليقين والإثبات — معرفة ثابتة بأثر صريح"


@dataclass
class SifrNucleus(Nucleus):
    """
    2. الصفر المعرفي
    نواة غياب الأثر أو انعدام المعرفة الكافية.
    لا يعني الخطأ بل يعني «لم يثبت بعد» — حالة إبستيمية صريحة.
    """
    reason: str = "لا أثر كافٍ"
    is_absolute: bool = False  # صفر مطلق (لا دليل ممكن) أم صفر مؤقت؟

    def __post_init__(self) -> None:
        self.name_ar = "الصفر المعرفي"
        self.name_en = "EpistemicZero"
        self.description = "غياب الأثر أو انعدام المعرفة الكافية — «لم يثبت»"


@dataclass
class FaradiyyaNucleus(Nucleus):
    """
    3. الفرضية
    نواة الاحتمال المعقول. نتيجة مُحتمَلة تحتاج مزيداً من التحقق.
    تُقابل «الظن» في التراث الأصولي.
    """
    confidence: float = 0.5
    testable: bool = True  # هل الفرضية قابلة للاختبار؟
    conditions: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.name_ar = "الفرضية"
        self.name_en = "Hypothesis"
        self.description = "احتمال معقول يحتاج تحققاً — «الظن المعتبر»"


@dataclass
class TransitionGateNucleus(Nucleus):
    """
    4. الانتقال والبوابة
    نواة الحركة من حالة إلى أخرى في سلسلة التحليل.
    تُطابق بوابات نظام المقام (BaseGate) في الطبقات الأدنى.
    """
    gate_name: str = ""
    source_stage: str = ""
    target_stage: str = ""
    cost: float = 0.0  # كلفة الانتقال (∞ = مستحيل)
    hard_constraint: bool = False  # هل هو قيد صلب؟

    def __post_init__(self) -> None:
        self.name_ar = "الانتقال والبوابة"
        self.name_en = "TransitionGate"
        self.description = "نواة الحركة بين المراحل — بوابة الانتقال"

    def is_passable(self) -> bool:
        return self.cost < float("inf")


@dataclass
class TasawwurNucleus(Nucleus):
    """
    5. التصور
    نواة الإدراك الأولي قبل الحكم.
    تُقابل المرحلة الثالثة من الدالة الجامعة: «تصور متعيَّن».
    """
    conceived_units: List[str] = field(default_factory=list)
    is_complete: bool = False  # هل التصور كامل أم ناقص؟

    def __post_init__(self) -> None:
        self.name_ar = "التصور"
        self.name_en = "Tasawwur"
        self.description = "الإدراك الأولي للوحدات — «تصور متعيَّن»"


@dataclass
class MafhumNucleus(Nucleus):
    """
    6. المفهوم
    نواة المعنى المحدود. التصور بعد تقييده بحد فاصل.
    يُقابل «المفهوم المحدود» في المرحلة الرابعة.
    """
    definition: str = ""
    genus: str = ""       # الجنس القريب
    differentia: str = "" # الفصل المميِّز
    examples: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.name_ar = "المفهوم"
        self.name_en = "Mafhum"
        self.description = "المعنى المحدود بحد فاصل — تصور مُقيَّد"


@dataclass
class MajalNucleus(Nucleus):
    """
    7. المجال
    نواة الفضاء الذي يعمل فيه المفهوم أو الحكم.
    يُقابل نطاق التطبيق (scope/domain) في المنطق الصوري.
    """
    domain_name: str = ""
    lower_bound: Optional[Any] = None
    upper_bound: Optional[Any] = None
    members: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.name_ar = "المجال"
        self.name_en = "Majal"
        self.description = "فضاء تطبيق المفهوم أو الحكم — النطاق"


@dataclass
class DalalaNucleus(Nucleus):
    """
    8. الدلالة
    نواة العلاقة بين اللفظ والمعنى — الدلالة المضبوطة.
    تُقابل المرحلة الخامسة: «دلالة مضبوطة».
    الأنواع: مطابقة | تضمّن | التزام.
    """
    dalala_type: str = "مطابقة"  # مطابقة | تضمن | التزام
    lafz: str = ""   # اللفظ
    mana: str = ""   # المعنى

    def __post_init__(self) -> None:
        self.name_ar = "الدلالة"
        self.name_en = "Dalala"
        self.description = "علاقة اللفظ بالمعنى — «دلالة مضبوطة»"


@dataclass
class NisbaNucleus(Nucleus):
    """
    9. النسبة
    نواة العلاقة ذات الطرفين (إسناد).
    تُقابل المرحلة السادسة: «نسبة ذات طرفين».
    تُقابل علاقة ISN (إسناد) في نظرية النحو.
    """
    subject: str = ""    # المُسنَد إليه
    predicate: str = ""  # المُسنَد
    relation_type: str = "إسناد"  # إسناد | تضمين | تقييد
    polarity: str = "إيجاب"  # إيجاب | سلب

    def __post_init__(self) -> None:
        self.name_ar = "النسبة"
        self.name_en = "Nisba"
        self.description = "العلاقة ذات الطرفين — «نسبة مُسنَدة»"


@dataclass
class HukmNucleus(Nucleus):
    """
    10. الحكم
    نواة الحكم المنطقي/الشرعي على الواقع.
    يمر بمرحلتين: «حكم مُرشَّح» ثم «حكم مُطبَّق».
    """
    ruling_text: str = ""
    is_applied: bool = False  # مرشح أم مطبق؟
    manat: str = ""  # المناط (علة الحكم)
    confidence: float = 1.0

    def __post_init__(self) -> None:
        self.name_ar = "الحكم"
        self.name_en = "Hukm"
        self.description = "الحكم المنطقي على الواقع — مُرشَّح ثم مُطبَّق"


@dataclass
class TahqiqManatNucleus(Nucleus):
    """
    11. تحقيق المناط
    نواة التثبت من انطباق علة الحكم على الواقع الجزئي.
    تُقابل المرحلة الثامنة من الدالة الجامعة.
    """
    hukm_uid: str = ""       # الحكم الكلي
    waqi_instance: str = ""  # الواقع الجزئي
    illa: str = ""           # العلة المحققة
    tahqiq_result: bool = False  # هل تحقق المناط؟

    def __post_init__(self) -> None:
        self.name_ar = "تحقيق المناط"
        self.name_en = "TahqiqManat"
        self.description = "التثبت من انطباق العلة على الواقع الجزئي"


@dataclass
class QiyasNucleus(Nucleus):
    """
    12. القياس
    نواة الاستدلال بإلحاق فرع بأصل لاشتراكهما في علة.
    الأركان: أصل | فرع | علة | حكم الفرع.
    تُقابل المرحلة العاشرة: «قياس عند وجود علة وفرع».
    """
    asl: str = ""          # الأصل
    far_: str = ""         # الفرع
    illa: str = ""         # العلة المشتركة
    hukm_asl: str = ""     # حكم الأصل
    hukm_far: str = ""     # حكم الفرع (المُستنبَط)
    is_valid: bool = False # هل القياس صحيح؟

    def __post_init__(self) -> None:
        self.name_ar = "القياس"
        self.name_en = "Qiyas"
        self.description = "إلحاق فرع بأصل لاشتراكهما في علة"


@dataclass
class MiataamilNucleus(Nucleus):
    """
    13. العوامل المئة
    نواة منظومة العوامل النحوية (المئة عامل) التي تُحرِّك الكلمات.
    كل عامل يُسند حركةً إعرابية لمعمول معين.
    """
    factor_name: str = ""      # اسم العامل
    factor_type: str = "لفظي" # لفظي | معنوي
    mamul: str = ""            # المعمول
    case_assigned: str = ""    # الحركة المُسنَدة

    def __post_init__(self) -> None:
        self.name_ar = "العوامل المئة"
        self.name_en = "MiataAmil"
        self.description = "منظومة العوامل النحوية المُحرِّكة للكلمات"


@dataclass
class IrabVectorNucleus(Nucleus):
    """
    14. الإعراب كمتجه
    نواة تمثيل الإعراب كمتجه في فضاء الميزات.
    تُحوِّل الحالة الإعرابية من وصف نصي إلى تمثيل رياضي.

    المتجه: (رفع, نصب, جر, جزم, بناء) + درجة الثقة
    """
    token: str = ""
    case_name: str = ""     # اسم الحالة الإعرابية بالعربية
    case_vector: List[float] = field(default_factory=lambda: [0.0, 0.0, 0.0, 0.0, 0.0])
    # ترتيب المتجه: [رفع, نصب, جر, جزم, بناء]
    sign: str = ""          # علامة الإعراب (ُ / َ / ِ / ْ / ...)
    cause: str = ""         # سبب الإعراب
    confidence: float = 1.0

    CASE_INDEX = {"رفع": 0, "نصب": 1, "جر": 2, "جزم": 3, "بناء": 4}

    def __post_init__(self) -> None:
        self.name_ar = "الإعراب كمتجه"
        self.name_en = "IrabVector"
        self.description = "تمثيل الإعراب كمتجه في فضاء الميزات"
        # تعبئة المتجه إذا عُرف اسم الحالة
        if self.case_name and self.case_name in self.CASE_INDEX:
            idx = self.CASE_INDEX[self.case_name]
            if len(self.case_vector) == 5:
                self.case_vector[idx] = self.confidence


@dataclass
class IfadaNucleus(Nucleus):
    """
    15. الإفادة
    نواة الفائدة أو الغرض من الملفوظ.
    تُقابل مفهوم «الفائدة» في النحو العربي: الجملة المفيدة هي ما حَسُن السكوت عليه.
    """
    benefit_type: str = "تامة"  # تامة | ناقصة | صفر
    communicative_goal: str = ""  # إخبار | استفهام | إنشاء | ...
    is_complete_sentence: bool = False

    def __post_init__(self) -> None:
        self.name_ar = "الإفادة"
        self.name_en = "Ifada"
        self.description = "الفائدة من الملفوظ — الغرض التواصلي"


@dataclass
class AatharHukmNucleus(Nucleus):
    """
    16. أثر الحكم والسلوك
    نواة تأثير الحكم في الواقع والسلوك.
    تُقابل المرحلة الحادية عشرة (الأخيرة) من الدالة الجامعة.
    """
    behavioral_effect: str = ""  # التغيير السلوكي المتوقع
    reality_effect: str = ""     # التغيير الواقعي
    scope: str = "فردي"          # فردي | جماعي | كوني
    reversible: bool = True

    def __post_init__(self) -> None:
        self.name_ar = "أثر الحكم والسلوك"
        self.name_en = "AatharHukm"
        self.description = "تأثير الحكم في الواقع والسلوك — المرحلة الأخيرة"


@dataclass
class TaarudTarjihNucleus(Nucleus):
    """
    17. التعارض والترجيح
    نواة تعارض الأدلة أو الأحكام وآلية الترجيح بينها.
    تُقابل مبدأ «argmin E» عند تعدد المرشحين.
    """
    candidates: List[str] = field(default_factory=list)  # المتعارضات
    weights: List[float] = field(default_factory=list)    # أوزان الترجيح
    winner: Optional[str] = None  # الراجح بعد الترجيح
    tie_break_rule: str = "الأقوى دليلاً"

    def __post_init__(self) -> None:
        self.name_ar = "التعارض والترجيح"
        self.name_en = "TaarudTarjih"
        self.description = "تعارض الأدلة وآلية الترجيح — argmin المتعدد"

    def apply(self) -> Optional[str]:
        """يُطبِّق الترجيح ويُعيد الراجح."""
        if not self.candidates:
            return None
        if self.weights and len(self.weights) == len(self.candidates):
            idx = self.weights.index(max(self.weights))
            self.winner = self.candidates[idx]
        elif self.candidates:
            self.winner = self.candidates[0]
        return self.winner


@dataclass
class AhliyyaNucleus(Nucleus):
    """
    18. أهلية المستدل والملكة
    نواة تقييم أهلية المحلل/المستدل وملكته العلمية.
    تُؤثر في وزن المخرجات: كلما كانت الملكة أقوى زادت ثقة النتيجة.
    """
    reasoner_id: str = "system"
    competence_level: float = 1.0  # [0, 1]
    domain_expertise: List[str] = field(default_factory=list)
    qualified: bool = True

    def __post_init__(self) -> None:
        self.name_ar = "أهلية المستدل والملكة"
        self.name_en = "AhliyyaReasoner"
        self.description = "أهلية المحلل وملكته — مُعدِّل وزن المخرجات"

    def weight_output(self, base_confidence: float) -> float:
        """يُعدِّل درجة الثقة بحسب أهلية المستدل."""
        return min(1.0, base_confidence * self.competence_level)


@dataclass
class WaqiaNucleus(Nucleus):
    """
    19. الواقع (نواة)
    نواة الواقع المُشاهَد — نقطة البداية في الدالة الجامعة.
    تُقابل المرحلة الأولى: «واقع مشهود».
    تُشير إلى كائن Reality في طبقة الأنطولوجيا.
    """
    reality_uid: str = ""
    observable: bool = True  # هل الواقع مُشاهَد مباشرة؟
    certainty: float = 1.0

    def __post_init__(self) -> None:
        self.name_ar = "الواقع"
        self.name_en = "WaqiaNucleus"
        self.description = "الواقع المشهود — نقطة انطلاق الدالة الجامعة"


@dataclass
class LowerLayersNucleus(Nucleus):
    """
    20. الطبقات اللغوية الدنيا
    نواة الطبقات الأساسية: الصوتي → الصرفي → النحوي → الدلالي.
    تُمثِّل ربط نظام «العقل الباني» بمحركات Eqratech الموجودة.
    """
    layers_active: List[str] = field(
        default_factory=lambda: ["صوتي", "صرفي", "نحوي", "دلالي"]
    )
    engine_bindings: Dict[str, str] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.name_ar = "الطبقات اللغوية الدنيا"
        self.name_en = "LowerLinguisticLayers"
        self.description = "الطبقات الأساسية مرتبطة بمحركات Eqratech"

    def bind_engine(self, layer: str, engine_class: str) -> None:
        """يربط طبقةً بمحرك Eqratech."""
        self.engine_bindings[layer] = engine_class
