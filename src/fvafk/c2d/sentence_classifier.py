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
    SABABIYYA  = "سببية"
    MADH       = "مدح"
    DHAMM      = "ذم"
    UNKNOWN    = "غير معروف"


def _bare(s: str) -> str:
    return "".join(c for c in s if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)).strip()


_BARE_ISTIFHAM  = frozenset({"هل","من","ما","ماذا","كيف","أين","متى","كم","أي","أيان","أنى"})
_BARE_NIDA      = frozenset({"يا","أيا","هيا","وا"})
_BARE_TAMANNI   = frozenset({"ليت","ليتما"})
_BARE_QASAM     = frozenset({"والله","بالله","تالله","وربي"})
_BARE_SHART     = frozenset({"إن","لو","لولا","إذا","مهما","أينما","حيثما","أنى"})
_BARE_SABABIYYA = frozenset({"لأن","إذ","حتى"})
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
        if fb in _BARE_QASAM:
            return ClassificationResult(SentenceType.QASAM,    0.95, first)
        if fb in _BARE_NIDA:
            return ClassificationResult(SentenceType.NIDA,     0.95, first)
        if fb in _BARE_ISTIFHAM:
            return ClassificationResult(SentenceType.ISTIFHAM, 0.95, first)
        if fb in _BARE_TAMANNI:
            return ClassificationResult(SentenceType.TAMANNI,  0.95, first)
        if fb in _BARE_MADH:
            return ClassificationResult(SentenceType.MADH,     0.95, first)
        if fb in _BARE_DHAMM:
            return ClassificationResult(SentenceType.DHAMM,    0.95, first)
        if fb in _BARE_SHART:
            return ClassificationResult(SentenceType.SHART,    0.90, first)
        for t, tb in zip(tokens, all_b):
            if tb in _BARE_SABABIYYA:
                return ClassificationResult(SentenceType.SABABIYYA, 0.85, t)
        if len(tokens) >= 2 and fb == "لا":
            return ClassificationResult(SentenceType.NAHY, 0.90, first)
        return ClassificationResult(SentenceType.KHABARIYYA, 0.70)