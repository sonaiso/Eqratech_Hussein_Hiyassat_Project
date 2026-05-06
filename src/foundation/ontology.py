"""
الأنطولوجيا الرياضية — Mathematical Ontology
==============================================
يُعرِّف هذا الملف المفاهيم الأساسية الأربعة في «الوثيقة الرياضية التأسيسية للعقل الباني»:

    Ω  — الكون المعرفي   (KnowledgeUniverse)
    R  — الواقع          (Reality)
    T  — الأثر           (Trace)
    τ  — دالة الأثر      (trace_fn: R → T)

العلاقة الجوهرية:
    - الواقع R هو مجموعة جزئية من Ω:  R ⊆ Ω
    - الأثر T هو مجموعة جزئية من Ω:   T ⊆ Ω
    - τ تُحوِّل كل واقع r ∈ R إلى أثر t ∈ T:  τ(r) = t

يتبع النهج الرياضي: يُعامَل كل مفهوم لغوي كعنصر في فضاء المعرفة.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set
from enum import Enum
import unicodedata


# ---------------------------------------------------------------------------
# الكون المعرفي  Ω
# ---------------------------------------------------------------------------

class KnowledgeUniverse:
    """
    الكون المعرفي Ω
    ================
    الفضاء الكلي الذي تنتمي إليه جميع الواقعات والآثار والمفاهيم.

    في الصياغة الرياضية:
        Ω = { ω | ω قابل للتمثيل معرفياً }

    عملياً، يحمل:
    - مجموعة الواقعات المُسجَّلة (instances of Reality)
    - مجموعة الآثار المُستخلَصة (instances of Trace)
    - فهرساً للعلاقات بينهما

    مثال:
        omega = KnowledgeUniverse()
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        omega.register(r)
    """

    def __init__(self) -> None:
        self._realities: List[Reality] = []
        self._traces: List[Trace] = []
        self._registry: Dict[str, Any] = {}

    # ------------------------------------------------------------------
    # تسجيل العناصر في الكون المعرفي
    # ------------------------------------------------------------------

    def register(self, element: "Reality | Trace") -> None:
        """يضيف عنصراً (واقعاً أو أثراً) إلى الكون المعرفي."""
        if isinstance(element, Reality):
            self._realities.append(element)
            self._registry[element.uid] = element
        elif isinstance(element, Trace):
            self._traces.append(element)
            self._registry[element.uid] = element
        else:
            raise TypeError(f"Expected Reality or Trace, got {type(element)}")

    def apply_trace_fn(self, reality: "Reality") -> "Trace":
        """
        يُطبِّق دالة الأثر τ على واقع ويُسجِّل الأثر في Ω.

        هذا تطبيق مباشر لـ:   τ : R → T
        """
        t = trace_fn(reality)
        self.register(t)
        return t

    # ------------------------------------------------------------------
    # استعلامات
    # ------------------------------------------------------------------

    @property
    def realities(self) -> List["Reality"]:
        return list(self._realities)

    @property
    def traces(self) -> List["Trace"]:
        return list(self._traces)

    def get(self, uid: str) -> Optional[Any]:
        return self._registry.get(uid)

    def __len__(self) -> int:
        return len(self._registry)

    def __repr__(self) -> str:
        return (
            f"KnowledgeUniverse(Ω, realities={len(self._realities)}, "
            f"traces={len(self._traces)})"
        )


# ---------------------------------------------------------------------------
# الواقع  R
# ---------------------------------------------------------------------------

class RealityKind(Enum):
    """
    نوع الواقع المُشاهَد.

    - TEXT:        نص عربي مُدخَل مباشرة
    - UTTERANCE:   ملفوظ لغوي موثَّق
    - STRUCTURE:   بنية مستخلَصة (جملة، تركيب)
    - COMPOUND:    واقع مركَّب من واقعات أبسط
    """
    TEXT = "نص"
    UTTERANCE = "ملفوظ"
    STRUCTURE = "بنية"
    COMPOUND = "مركب"


@dataclass
class Reality:
    """
    الواقع r ∈ R
    =============
    مثيل واقعي مُشاهَد قابل للتحليل.  R ⊆ Ω.

    الحقول الإلزامية:
        raw_text   — النص الخام كما وَرَد (يشمل علامات الضبط إن وُجدت)

    الحقول الاختيارية:
        kind       — نوع الواقع (افتراضي: TEXT)
        source     — مصدر النص (مرجع، سياق، ...)
        metadata   — بيانات وصفية إضافية
        uid        — معرّف فريد (يُحسَب تلقائياً إن لم يُعطَ)

    مثال:
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ", kind=RealityKind.TEXT)
    """
    raw_text: str
    kind: RealityKind = RealityKind.TEXT
    source: Optional[str] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    uid: str = field(default="", init=False)

    def __post_init__(self) -> None:
        if not self.uid:
            # uid = نوع + hash مُختصَر
            self.uid = f"R:{self.kind.value}:{hash(self.raw_text) & 0xFFFF:04X}"

    def is_arabic(self) -> bool:
        """يتحقق إذا كان النص يحتوي على حروف عربية."""
        return any("\u0600" <= ch <= "\u06FF" for ch in self.raw_text)

    def char_count(self) -> int:
        return len(self.raw_text)

    def __repr__(self) -> str:
        preview = self.raw_text[:30] + ("…" if len(self.raw_text) > 30 else "")
        return f"Reality(uid={self.uid!r}, text={preview!r})"


# ---------------------------------------------------------------------------
# الأثر  T
# ---------------------------------------------------------------------------

class TraceLevel(Enum):
    """
    مستوى الأثر (عمق التحليل).

    - SURFACE:     الأثر السطحي (الحروف والكلمات فقط)
    - PHONEMIC:    الأثر الصوتي (الفونيمات)
    - MORPHEMIC:   الأثر الصرفي (الجذر والوزن)
    - SYNTACTIC:   الأثر النحوي (العلاقات الإعرابية)
    - SEMANTIC:    الأثر الدلالي (المعنى والسياق)
    - FULL:        الأثر الشامل (كل المستويات)
    """
    SURFACE = "سطحي"
    PHONEMIC = "صوتي"
    MORPHEMIC = "صرفي"
    SYNTACTIC = "نحوي"
    SEMANTIC = "دلالي"
    FULL = "شامل"


@dataclass
class Trace:
    """
    الأثر t ∈ T
    ============
    الأثر المُثبَت الناتج عن تطبيق دالة الأثر τ على واقع.  T ⊆ Ω.

    يحمل المعلومات المُستخلَصة من الواقع عند مستوى تحليل معين.

    الحقول:
        source_uid   — uid الواقع الذي نشأ منه هذا الأثر
        level        — مستوى الأثر
        tokens       — قائمة الوحدات المُستخلَصة
        features     — خصائص مُستخلَصة (dict قابل للتوسع)
        uid          — معرّف فريد
    """
    source_uid: str
    level: TraceLevel = TraceLevel.SURFACE
    tokens: List[str] = field(default_factory=list)
    features: Dict[str, Any] = field(default_factory=dict)
    uid: str = field(default="", init=False)

    def __post_init__(self) -> None:
        if not self.uid:
            token_hash = hash(tuple(self.tokens)) & 0xFFFF
            self.uid = f"T:{self.level.value}:{self.source_uid}:{token_hash:04X}"

    def is_empty(self) -> bool:
        """أثر فارغ = لا كلمات مُستخلَصة (الـ features لا تُحسَب)."""
        return not self.tokens

    def __repr__(self) -> str:
        return (
            f"Trace(uid={self.uid!r}, level={self.level.value!r}, "
            f"tokens={self.tokens[:5]!r}{'…' if len(self.tokens) > 5 else ''})"
        )


# ---------------------------------------------------------------------------
# دالة الأثر  τ : R → T
# ---------------------------------------------------------------------------

def trace_fn(reality: Reality, level: TraceLevel = TraceLevel.SURFACE) -> Trace:
    """
    دالة الأثر  τ : R → T
    =======================
    تُحوِّل واقعاً r ∈ R إلى أثر t ∈ T.

    التطبيق الأولي (v0.1):
    - يُجزِّئ النص إلى كلمات (tokens سطحية)
    - يُستخلَص معلومات يونيكود أساسية

    المعاملات:
        reality   — الواقع المراد تتبُّعه
        level     — مستوى التحليل المطلوب (افتراضي: SURFACE)

    تُعيد:
        Trace — الأثر المُثبَت

    مثال:
        r = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        t = trace_fn(r)
        # t.tokens == ['الكِتَابُ', 'مُفِيدٌ']
    """
    text = reality.raw_text.strip()

    # التجزئة السطحية (كلمات)
    tokens = text.split() if text else []

    # خصائص أساسية
    features: Dict[str, Any] = {
        "char_count": len(text),
        "token_count": len(tokens),
        "has_harakat": any(
            "\u064B" <= ch <= "\u0652" or ch == "\u0670" for ch in text
        ),
        "has_shadda": "\u0651" in text,
        "unicode_blocks": _unicode_blocks(text),
        "source_kind": reality.kind.value,
    }

    if level != TraceLevel.SURFACE:
        # مستويات أعمق تُفعَّل في المستقبل بربط محركات Eqratech
        features["deep_level"] = level.value
        features["note"] = "deep analysis reserved for v0.2+"

    return Trace(
        source_uid=reality.uid,
        level=level,
        tokens=tokens,
        features=features,
    )


# ---------------------------------------------------------------------------
# دوال مساعدة
# ---------------------------------------------------------------------------

def _unicode_blocks(text: str) -> FrozenSet[str]:
    """يُحدِّد كتل يونيكود الموجودة في النص."""
    blocks: Set[str] = set()
    for ch in text:
        cp = ord(ch)
        if 0x0600 <= cp <= 0x06FF:
            blocks.add("Arabic")
        elif 0x0750 <= cp <= 0x077F:
            blocks.add("Arabic_Supplement")
        elif 0xFB50 <= cp <= 0xFDFF:
            blocks.add("Arabic_Presentation_Forms_A")
        elif 0xFE70 <= cp <= 0xFEFF:
            blocks.add("Arabic_Presentation_Forms_B")
        elif 0x0020 <= cp <= 0x007F:
            blocks.add("Basic_Latin")
        else:
            blocks.add("Other")
    return frozenset(blocks)
