"""
وحدات يونيكود العربية — Arabic Unicode Units
==============================================
يُعرِّف هذا الملف التمثيل الدقيق لأي نص عربي على مستوى:
- نقطة الكود (code point)
- الحركات وعلامات الضبط (combining marks / harakat)
- تصنيف كل وحدة (حرف | حركة | تنوين | شدة | ...)
- السبب والأثر والوظيفة لكل وحدة

هذا التحليل هو الطبقة الأدنى (Lower Linguistic Layer) التي تُغذِّي جميع
المراحل الأعلى في الدالة الجامعة.

تغطية يونيكود:
    U+0600–U+06FF  Arabic block
    U+0750–U+077F  Arabic Supplement
    U+064B–U+0652  Harakat (حركات)
    U+0670         Superscript Alef (ألف خنجرية)
    U+0651         Shadda (شدة)
    U+0652         Sukun (سكون)
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass, field
from enum import Enum
from typing import Iterator, List, Optional, Tuple


# ---------------------------------------------------------------------------
# تصنيف الوحدات
# ---------------------------------------------------------------------------

class UnitKind(Enum):
    """
    تصنيف الوحدة اليونيكودية العربية.

    LETTER        — حرف هجائي أساسي
    HARAKA        — حركة قصيرة (فتحة، ضمة، كسرة)
    TANWIN        — تنوين (فتح، ضم، كسر)
    SHADDA        — شدة (تضعيف)
    SUKUN         — سكون
    MADD          — مد (ألف خنجرية U+0670)
    HAMZA         — همزة مستقلة
    ALEF_VARIANTS — أشكال الألف (مد، وصل، ...)
    PUNCTUATION   — علامات ترقيم
    SPACE         — مسافة
    DIGIT         — رقم عربي أو هندي
    OTHER         — غير مصنَّف
    """
    LETTER = "حرف"
    HARAKA = "حركة"
    TANWIN = "تنوين"
    SHADDA = "شدة"
    SUKUN = "سكون"
    MADD = "مد"
    HAMZA = "همزة"
    ALEF_VARIANTS = "ألف"
    PUNCTUATION = "ترقيم"
    SPACE = "مسافة"
    DIGIT = "رقم"
    OTHER = "أخرى"


# ---------------------------------------------------------------------------
# خرائط يونيكود
# ---------------------------------------------------------------------------

# الحركات القصيرة
_HARAKA_MAP: dict[int, Tuple[str, str]] = {
    0x064E: ("فتحة", "fatha"),
    0x064F: ("ضمة", "damma"),
    0x0650: ("كسرة", "kasra"),
}

# التنوين
_TANWIN_MAP: dict[int, Tuple[str, str]] = {
    0x064B: ("تنوين فتح", "fathatan"),
    0x064C: ("تنوين ضم", "dammatan"),
    0x064D: ("تنوين كسر", "kasratan"),
}

# حركات خاصة
_SPECIAL_MAP: dict[int, Tuple[str, UnitKind]] = {
    0x0651: ("شدة", UnitKind.SHADDA),
    0x0652: ("سكون", UnitKind.SUKUN),
    0x0670: ("ألف خنجرية", UnitKind.MADD),
}

# الهمزات
_HAMZA_CODEPOINTS = frozenset([
    0x0621,  # ARABIC LETTER HAMZA ء
    0x0622,  # ARABIC LETTER ALEF WITH MADDA ABOVE آ
    0x0623,  # ARABIC LETTER ALEF WITH HAMZA ABOVE أ
    0x0624,  # ARABIC LETTER WAW WITH HAMZA ABOVE ؤ
    0x0625,  # ARABIC LETTER ALEF WITH HAMZA BELOW إ
    0x0626,  # ARABIC LETTER YEH WITH HAMZA ABOVE ئ
])

# أشكال الألف
_ALEF_CODEPOINTS = frozenset([
    0x0627,  # ARABIC LETTER ALEF ا
    0x0622,  # آ
    0x0623,  # أ
    0x0625,  # إ
    0x0671,  # ARABIC LETTER ALEF WASLA ٱ
    0x0649,  # ARABIC LETTER ALEF MAKSURA ى
])


def _classify(cp: int) -> UnitKind:
    """يُصنِّف نقطة كود عربية إلى UnitKind."""
    if cp in _SPECIAL_MAP:
        return _SPECIAL_MAP[cp][1]
    if cp in _TANWIN_MAP:
        return UnitKind.TANWIN
    if cp in _HARAKA_MAP:
        return UnitKind.HARAKA
    if cp in _HAMZA_CODEPOINTS:
        return UnitKind.HAMZA
    if cp in _ALEF_CODEPOINTS:
        return UnitKind.ALEF_VARIANTS
    if 0x0621 <= cp <= 0x064A:
        return UnitKind.LETTER
    if 0x0600 <= cp <= 0x06FF or 0x0750 <= cp <= 0x077F:
        return UnitKind.LETTER
    if cp == 0x0020 or cp == 0x00A0:
        return UnitKind.SPACE
    if 0x0030 <= cp <= 0x0039 or 0x0660 <= cp <= 0x0669:
        return UnitKind.DIGIT
    if unicodedata.category(chr(cp)).startswith("P"):
        return UnitKind.PUNCTUATION
    return UnitKind.OTHER


# ---------------------------------------------------------------------------
# وحدة يونيكود مفردة
# ---------------------------------------------------------------------------

@dataclass
class ArabicUnit:
    """
    وحدة يونيكود مفردة في نص عربي.

    تحمل:
    - char          : الحرف نفسه
    - codepoint     : نقطة الكود (int)
    - codepoint_str : تمثيل U+XXXX
    - utf8_bytes    : بايتات UTF-8
    - kind          : تصنيف الوحدة
    - name_ar       : الاسم العربي للوحدة
    - name_unicode  : الاسم الرسمي في Unicode
    - position      : موضع الوحدة في النص الأصلي (index)
    - cause         : سبب وجود هذه الوحدة (وظيفتها السياقية)
    - effect        : أثرها على ما حولها
    - function      : وظيفتها اللغوية

    مثال:
        unit = ArabicUnit.from_char('كَ', pos=0)
        # unit.kind == UnitKind.LETTER
        # unit.codepoint_str == 'U+0643'
    """
    char: str
    codepoint: int
    codepoint_str: str
    utf8_bytes: bytes
    kind: UnitKind
    name_ar: str
    name_unicode: str
    position: int = 0
    cause: str = ""
    effect: str = ""
    function: str = ""

    @classmethod
    def from_char(cls, ch: str, pos: int = 0) -> "ArabicUnit":
        """يبني ArabicUnit من حرف واحد."""
        if len(ch) != 1:
            raise ValueError(f"Expected single character, got {ch!r}")
        cp = ord(ch)
        kind = _classify(cp)
        name_ar = _arabic_name(cp, kind)
        try:
            name_uni = unicodedata.name(ch, f"U+{cp:04X}")
        except ValueError:
            name_uni = f"U+{cp:04X}"

        return cls(
            char=ch,
            codepoint=cp,
            codepoint_str=f"U+{cp:04X}",
            utf8_bytes=ch.encode("utf-8"),
            kind=kind,
            name_ar=name_ar,
            name_unicode=name_uni,
            position=pos,
            cause=_default_cause(kind),
            effect=_default_effect(kind),
            function=_default_function(kind),
        )

    def is_diacritic(self) -> bool:
        return self.kind in (UnitKind.HARAKA, UnitKind.TANWIN,
                             UnitKind.SHADDA, UnitKind.SUKUN, UnitKind.MADD)

    def is_letter(self) -> bool:
        return self.kind in (UnitKind.LETTER, UnitKind.HAMZA,
                             UnitKind.ALEF_VARIANTS)

    def utf8_hex(self) -> str:
        return " ".join(f"0x{b:02X}" for b in self.utf8_bytes)

    def __repr__(self) -> str:
        return (
            f"ArabicUnit(char={self.char!r}, cp={self.codepoint_str}, "
            f"kind={self.kind.value}, pos={self.position})"
        )


# ---------------------------------------------------------------------------
# نص عربي كقائمة من الوحدات
# ---------------------------------------------------------------------------

@dataclass
class ArabicText:
    """
    نص عربي مُحلَّل إلى وحدات يونيكود.

    يُوفِّر:
    - تحليل كل حرف/علامة إلى ArabicUnit
    - تجميع الوحدات إلى كلمات (tokens)
    - إحصاءات سريعة

    مثال:
        text = ArabicText.from_string("الكِتَابُ مُفِيدٌ")
        for unit in text.units:
            print(unit)
    """
    raw: str
    units: List[ArabicUnit] = field(default_factory=list)

    @classmethod
    def from_string(cls, text: str) -> "ArabicText":
        """يبني ArabicText من نص عربي."""
        units = [
            ArabicUnit.from_char(ch, pos=i)
            for i, ch in enumerate(text)
        ]
        return cls(raw=text, units=units)

    # ------------------------------------------------------------------
    # تجميع الوحدات
    # ------------------------------------------------------------------

    def letter_units(self) -> List[ArabicUnit]:
        return [u for u in self.units if u.is_letter()]

    def diacritic_units(self) -> List[ArabicUnit]:
        return [u for u in self.units if u.is_diacritic()]

    def tokens(self) -> List["TokenUnit"]:
        """يُجمِّع الوحدات إلى كلمات (tokens) حافظاً لكل كلمة وحداتها."""
        result: List[TokenUnit] = []
        current_chars: List[ArabicUnit] = []
        current_start = 0

        for unit in self.units:
            if unit.kind == UnitKind.SPACE:
                if current_chars:
                    result.append(TokenUnit(
                        raw="".join(u.char for u in current_chars),
                        units=current_chars,
                        start=current_start,
                    ))
                    current_chars = []
            else:
                if not current_chars:
                    current_start = unit.position
                current_chars.append(unit)

        if current_chars:
            result.append(TokenUnit(
                raw="".join(u.char for u in current_chars),
                units=current_chars,
                start=current_start,
            ))

        return result

    # ------------------------------------------------------------------
    # إحصاءات
    # ------------------------------------------------------------------

    def stats(self) -> dict:
        kinds = {}
        for u in self.units:
            kinds[u.kind.value] = kinds.get(u.kind.value, 0) + 1
        return {
            "total_units": len(self.units),
            "letter_count": len(self.letter_units()),
            "diacritic_count": len(self.diacritic_units()),
            "token_count": len(self.tokens()),
            "by_kind": kinds,
        }

    def __iter__(self) -> Iterator[ArabicUnit]:
        return iter(self.units)

    def __len__(self) -> int:
        return len(self.units)

    def __repr__(self) -> str:
        preview = self.raw[:30] + ("…" if len(self.raw) > 30 else "")
        return f"ArabicText({preview!r}, units={len(self.units)})"


@dataclass
class TokenUnit:
    """
    كلمة (token) مُجمَّعة من وحدات يونيكود.

    raw   — شكل الكلمة الكامل (مع الحركات)
    units — قائمة ArabicUnit المكوِّنة للكلمة
    start — موضع البداية في النص الأصلي
    """
    raw: str
    units: List[ArabicUnit]
    start: int = 0

    def letters_only(self) -> str:
        """يُعيد الكلمة بدون حركات."""
        return "".join(u.char for u in self.units if u.is_letter())

    def harakat_sequence(self) -> List[str]:
        """يُعيد تسلسل الحركات في الكلمة."""
        return [u.char for u in self.units if u.is_diacritic()]

    def codepoints(self) -> List[str]:
        return [u.codepoint_str for u in self.units]

    def __repr__(self) -> str:
        return f"TokenUnit(raw={self.raw!r}, start={self.start})"


# ---------------------------------------------------------------------------
# دوال مساعدة داخلية
# ---------------------------------------------------------------------------

def _arabic_name(cp: int, kind: UnitKind) -> str:
    """يُعيد الاسم العربي لنقطة الكود."""
    names = {
        0x064E: "فتحة",
        0x064F: "ضمة",
        0x0650: "كسرة",
        0x064B: "تنوين فتح",
        0x064C: "تنوين ضم",
        0x064D: "تنوين كسر",
        0x0651: "شدة",
        0x0652: "سكون",
        0x0670: "ألف خنجرية",
        0x0621: "همزة",
        0x0622: "ألف مد",
        0x0623: "ألف همزة فوق",
        0x0624: "واو همزة",
        0x0625: "ألف همزة تحت",
        0x0626: "ياء همزة",
        0x0627: "ألف",
        0x0628: "باء",
        0x0629: "تاء مربوطة",
        0x062A: "تاء",
        0x062B: "ثاء",
        0x062C: "جيم",
        0x062D: "حاء",
        0x062E: "خاء",
        0x062F: "دال",
        0x0630: "ذال",
        0x0631: "راء",
        0x0632: "زاي",
        0x0633: "سين",
        0x0634: "شين",
        0x0635: "صاد",
        0x0636: "ضاد",
        0x0637: "طاء",
        0x0638: "ظاء",
        0x0639: "عين",
        0x063A: "غين",
        0x0641: "فاء",
        0x0642: "قاف",
        0x0643: "كاف",
        0x0644: "لام",
        0x0645: "ميم",
        0x0646: "نون",
        0x0647: "هاء",
        0x0648: "واو",
        0x0649: "ألف مقصورة",
        0x064A: "ياء",
        0x0671: "ألف وصل",
        0x0020: "مسافة",
    }
    return names.get(cp, kind.value)


def _default_cause(kind: UnitKind) -> str:
    causes = {
        UnitKind.LETTER: "أصل الكلمة",
        UnitKind.HARAKA: "العامل النحوي أو الصرفي",
        UnitKind.TANWIN: "التنكير وعدم الإضافة",
        UnitKind.SHADDA: "إدغام أو تضعيف",
        UnitKind.SUKUN: "وقوع آخر الكلمة أو السكون الأصلي",
        UnitKind.MADD: "مد الصوت للتمييز",
        UnitKind.HAMZA: "بنية الكلمة الأصلية",
        UnitKind.ALEF_VARIANTS: "الحالة الإعرابية أو الإملائية",
        UnitKind.SPACE: "الفصل بين الكلمات",
        UnitKind.PUNCTUATION: "الوقف أو التنظيم النصي",
        UnitKind.DIGIT: "العدد",
        UnitKind.OTHER: "غير محدد",
    }
    return causes.get(kind, "غير محدد")


def _default_effect(kind: UnitKind) -> str:
    effects = {
        UnitKind.LETTER: "تشكيل المقطع الصوتي",
        UnitKind.HARAKA: "تحديد الإعراب والبنية الصرفية",
        UnitKind.TANWIN: "الدلالة على التنكير",
        UnitKind.SHADDA: "مضاعفة الحرف صوتياً",
        UnitKind.SUKUN: "إغلاق المقطع الصوتي",
        UnitKind.MADD: "تطويل الصوت",
        UnitKind.HAMZA: "الفصل بين المقاطع الصوتية",
        UnitKind.ALEF_VARIANTS: "الاتصال أو الانفصال",
        UnitKind.SPACE: "الحد بين الوحدات المعجمية",
        UnitKind.PUNCTUATION: "تنظيم الجملة والفقرة",
        UnitKind.DIGIT: "تمثيل الكمية",
        UnitKind.OTHER: "غير محدد",
    }
    return effects.get(kind, "غير محدد")


def _default_function(kind: UnitKind) -> str:
    functions = {
        UnitKind.LETTER: "بناء الجذر والوزن",
        UnitKind.HARAKA: "الإعراب والضبط",
        UnitKind.TANWIN: "التنكير",
        UnitKind.SHADDA: "التضعيف",
        UnitKind.SUKUN: "الوقف",
        UnitKind.MADD: "المد",
        UnitKind.HAMZA: "الهمز",
        UnitKind.ALEF_VARIANTS: "الوصل أو الفصل",
        UnitKind.SPACE: "الفصل",
        UnitKind.PUNCTUATION: "التنظيم",
        UnitKind.DIGIT: "العدد",
        UnitKind.OTHER: "غير محدد",
    }
    return functions.get(kind, "غير محدد")
