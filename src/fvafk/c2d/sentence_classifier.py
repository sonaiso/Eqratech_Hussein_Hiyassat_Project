from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import List, Optional


class SentenceType(Enum):
    KHABARIYYA = "خبرية"
    AMR        = "أمر"
    NAHY       = "نهي"
    ISTIFHAM   = "استفهام"
    NIDA       = "نداء"
    TAMANNI    = "تمني"
    TAAJJUB    = "تعجب"
    QASAM      = "قسم"
    SHART      = "شرط"
    TAWKID     = "توكيد"
    TARAJI     = "ترجي"
    SABABIYYA  = "سببية"
    MADH       = "مدح"
    DHAMM      = "ذم"
    UNKNOWN    = "غير معروف"


def _bare(s: str) -> str:
    return "".join(c for c in s if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)).strip()


# ========== قواعد كشف فعل الأمر (_looks_imperative) ==========
#
# 1) شرط أساسي: الكلمة (بعد نزع الشكل _bare) تبدأ بهمزة وصل: ا أو أ.
#
# 2) استثناء: إذا بدأت الكلمة بـ «ال» لا تُعدّ أمراً (اسم معرف).
#
# 3) علامات البناء المعتمدة (أي واحدة تكفي لاعتبار الكلمة فعل أمر):
#
#    أ) واو الجماعة — الكلمة تنتهي بـ «وا»
#       أمثلة: اكتبوا، ادرسوا، أقيموا، ادعوا، اسعوا.
#       البناء: حذف النون.
#
#    ب) ألف الاثنين — الكلمة تنتهي بـ «ا» وطولها ≥ 3
#       أمثلة: اكتبا، ادرسا، اسعيا، ارْمِيَا، ادْعُوَا.
#       البناء: حذف النون (أو بقاء حرف العلة في المعتل).
#
#    ج) نا الفاعلين — وجود «نا» داخل الكلمة
#       أمثلة: اهدنا، اقتربنا (إن وردت بهذه الصيغة).
#
#    د) ياء المخاطبة — الكلمة تنتهي بـ «ي» وطولها ≥ 3
#       أمثلة: اكتبي، ادرسي، اذهبي، انجحي، اسعي، ارْمِي.
#       البناء: حذف النون.
#
#    هـ) نون النسوة أو نون التوكيد — الكلمة تنتهي بـ «ن» وطولها ≥ 3
#       أمثلة: اكتبْنَ، ارسمْنَ، اذهبْنَ، انجحْنَ؛ انْهَضَنَّ، اشْكُرَنَّ.
#       البناء: السكون (نون النسوة) أو الفتح (نون التوكيد).
#
#    و) افعلْ (صحيح الآخر، لم يتصل به شيء) — الكلمة تبدأ با/أ وطولها ≥ 3 ولا تنتهي بوا/ا/ي/ن
#       أمثلة: اكتبْ، ارسمْ، اقرأْ، اجلسْ، احفظْ، اقْرَأْ، اهْدِ.
#       البناء: السكون (يُحذف في _bare فتبقى الصيغة مثل اكتب، اقرأ).
#
# 4) معتل الآخر: اسعَ، ادعُ، اسقِ؛ اسعوا، ادعوا — تُقبَل عبر انتهاء «وا» أو «ا» أو طول ≥3 مع بدء با/أ.


def _looks_imperative(fb: str) -> bool:
    """فعل الأمر: همزة وصل (ا/أ) ثم إحدى علامات البناء أ–و أعلاه."""
    if len(fb) < 2 or fb[0] not in "اأ":
        return False
    if fb.startswith("ال"):
        return False  # اسم معرف بـ «ال» ليس فعلاً أمراً
    return (
        fb.endswith("وا")  # واو الجماعة — يُبنى على حذف النون
        or (fb.endswith("ا") and len(fb) >= 3)  # ألف الاثنين — اكتبا، ادرسا، اسعيا
        or "نا" in fb  # نا الفاعلين
        or (fb.endswith("ي") and len(fb) >= 3)  # ياء المخاطبة — اكتبي، ادرسي؛ يُبنى على حذف النون
        or (fb.endswith("ن") and len(fb) >= 3)  # نون النسوة أو نون التوكيد — اكتبْنَ، انْهَضَنَّ
        or len(fb) >= 3  # افعلْ — السكون (يُحذف في _bare)
    )


_BARE_ISTIFHAM  = frozenset({"هل","من","ما","ماذا","كيف","أين","متى","كم","أي","أيان","أنى"})
_BARE_NIDA      = frozenset({"يا","أيا","هيا","وا"})
_BARE_TAMANNI   = frozenset({"ليت", "ليتما", "ليتني", "ليتنا"})
_BARE_QASAM     = frozenset({"والله", "بالله", "تالله", "وربي"})
_BARE_SHART     = frozenset({"لو", "لولا", "إذا", "مهما", "أينما", "حيثما", "أنى", "وإن"})
_BARE_TAWKID    = frozenset({"إن", "إنَّ", "أن", "أنَّ", "إنما", "أنما", "لأن", "كأن", "كأنَّ", "لكن", "لكنَّ"})
_BARE_TARAJI    = frozenset({"لعل", "لعلَّ", "لعلي", "لعلنا", "لعلك", "لعله", "لعلها", "لعلهم", "عسى"})
_BARE_SABABIYYA = frozenset({"لأن", "إذ", "حتى", "لأنه", "لأنها", "لأنهم"})
_BARE_MADH      = frozenset({"نعم","حبذا"})
_BARE_DHAMM     = frozenset({"بئس","ساء"})


@dataclass
class ClassificationResult:
    sentence_type: SentenceType
    confidence:    float
    trigger_word:  Optional[str] = None
    notes:         List[str]     = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "sentence_type": self.sentence_type.value,
            "confidence":    round(self.confidence, 2),
            "trigger_word":  self.trigger_word,
            "notes":         self.notes,
        }


class SentenceClassifier:
    def classify(self, tokens: List[str]) -> ClassificationResult:
        if not tokens:
            return ClassificationResult(SentenceType.UNKNOWN, 0.0)
        first = tokens[0]
        fb    = _bare(first)
        all_b = [_bare(t) for t in tokens]
        if fb in _BARE_QASAM or (len(fb) >= 3 and fb.startswith("وال")):
            return ClassificationResult(SentenceType.QASAM,    0.95, first)
        if fb in _BARE_NIDA:
            if len(tokens) >= 2 and all_b[1] in _BARE_TAMANNI:
                return ClassificationResult(SentenceType.TAMANNI, 0.92, tokens[1])  # يا ليتنا
            return ClassificationResult(SentenceType.NIDA,     0.95, first)
        # تعجب: مَا أَفْعَلَ أو أَفْعِلْ بِ — قبل استفهام حتى لا تُصنَّف «ما» استفهاماً
        if len(tokens) >= 2 and fb == "ما" and len(all_b[1]) >= 3 and all_b[1].startswith("أ"):
            return ClassificationResult(SentenceType.TAAJJUB,  0.90, first)
        if len(fb) >= 3 and fb.startswith("أ") and fb not in _BARE_ISTIFHAM and any(ab.startswith("ب") for ab in all_b):
            return ClassificationResult(SentenceType.TAAJJUB,  0.88, first)
        if fb in _BARE_ISTIFHAM:
            return ClassificationResult(SentenceType.ISTIFHAM, 0.95, first)
        if fb in _BARE_TAMANNI:
            return ClassificationResult(SentenceType.TAMANNI,  0.95, first)
        if fb in _BARE_MADH:
            return ClassificationResult(SentenceType.MADH,     0.95, first)
        if fb in _BARE_DHAMM:
            return ClassificationResult(SentenceType.DHAMM,    0.95, first)
        if fb in _BARE_TAWKID:
            return ClassificationResult(SentenceType.TAWKID,  0.92, first)
        if fb in _BARE_TARAJI:
            return ClassificationResult(SentenceType.TARAJI,  0.92, first)
        if fb in _BARE_SHART:
            return ClassificationResult(SentenceType.SHART,    0.90, first)
        for t, tb in zip(tokens, all_b):
            if tb in _BARE_SABABIYYA or tb.startswith("لأن") or tb.startswith("فب"):
                return ClassificationResult(SentenceType.SABABIYYA, 0.85, t)
        if len(tokens) >= 2 and all_b[1].startswith("ف"):
            return ClassificationResult(SentenceType.SABABIYYA, 0.75, tokens[1])
        if len(tokens) >= 2 and fb == "لا":
            return ClassificationResult(SentenceType.NAHY, 0.90, first)
        if _looks_imperative(fb):
            return ClassificationResult(SentenceType.AMR, 0.88, first)
        return ClassificationResult(SentenceType.KHABARIYYA, 0.70)