# -*- coding: utf-8 -*-
"""
Verb morphology: tense, voice, person, number, gender from diacritics and structure.
No hardcoded word lists — rules only.
"""
from __future__ import annotations

import unicodedata
from typing import Optional

from fvafk.c2d.sentence_classifier import _looks_imperative

from .models import VerbFeatures


def _bare(s: str) -> str:
    return "".join(
        c for c in (s or "")
        if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)
    ).replace("-", "").strip()


def _get_vowel_at(s: str, i: int) -> Optional[str]:
    """Return combining vowel (fatha/damma/kasra/sukun) after character at i if any."""
    if not s or i < 0 or i >= len(s):
        return None
    s = unicodedata.normalize("NFD", s)
    j = i + 1
    while j < len(s) and unicodedata.category(s[j]) == "Mn":
        cat = unicodedata.category(s[j])
        if cat == "Mn":
            # \u064E fatha, \u064F damma, \u0650 kasra, \u0652 sukun
            return s[j]
        j += 1
    return None


def _last_short_vowel(word: str) -> Optional[str]:
    """Last short vowel (حركة) in word (fatha/damma/kasra/sukun)."""
    nfd = unicodedata.normalize("NFD", word)
    for i in range(len(nfd) - 1, -1, -1):
        if unicodedata.category(nfd[i]) == "Mn":
            return nfd[i]
    return None


def _starts_with_mudari(s: str) -> bool:
    """مضارع: ي / ت / ن / أ / ا (حروف المضارعة؛ ا = ألف بعد نزع الشكل قد تكون أ)."""
    b = _bare(s)
    if not b:
        return False
    return b[0] in "يتنأا"


def _has_damma_early(word: str, max_chars: int = 10) -> bool:
    """True if word has damma in first max_chars (NFD) — e.g. أَكْتُبُ."""
    nfd = unicodedata.normalize("NFD", word)
    for i, c in enumerate(nfd):
        if i >= max_chars:
            break
        if c == "\u064F":
            return True
    return False


def _detect_tense(word: str, stripped: str) -> str:
    """زمن: ماضي | مضارع | أمر."""
    bare = _bare(word)
    st = _bare(stripped) if stripped else bare
    if not st:
        return "ماضي"
    # مضارع: ي/ت/ن/أ (حروف المضارعة)
    if _starts_with_mudari(st):
        # أَكْتُبُ (first person) = word starts with أ (U+0623) + damma in word; اكْتُبْ (imperative) = ا (U+0627)
        if st[0] in "أا" and _looks_imperative(st):
            first_char = word.strip()[0] if word else ""
            if first_char == "\u0623" and _has_damma_early(word):
                return "مضارع"
            return "أمر"
        return "مضارع"
    # أمر: همزة وصل (ا/أ) + _looks_imperative
    if _looks_imperative(st):
        return "أمر"
    # ماضي
    return "ماضي"


def _detect_voice_madi(word: str, stripped: str) -> str:
    """مجهول ماضي: فُعِلَ — first letter damma, second letter kasra."""
    nfd = unicodedata.normalize("NFD", word)
    letters = [i for i, c in enumerate(nfd) if unicodedata.category(c) != "Mn" and c not in " \t"]
    if len(letters) < 3:
        return "معلوم"
    # After first root letter: damma?
    j = letters[0] + 1
    v1 = None
    while j < len(nfd) and unicodedata.category(nfd[j]) == "Mn":
        v1 = nfd[j]
        j += 1
    # After second letter: kasra?
    k = letters[1] + 1
    v2 = None
    while k < len(nfd) and unicodedata.category(nfd[k]) == "Mn":
        v2 = nfd[k]
        k += 1
    if v1 == "\u064F" and v2 == "\u0650":  # damma on first, kasra on second
        return "مجهول"
    return "معلوم"


def _detect_voice_mudari(word: str, stripped: str) -> str:
    """مجهول مضارع: يُفْعَلُ — ي/ت/ن/أ with damma + fatha on second root letter."""
    bare = _bare(word)
    if not _starts_with_mudari(bare) or len(bare) < 3:
        return "معلوم"
    nfd = unicodedata.normalize("NFD", word)
    letters = [i for i, c in enumerate(nfd) if unicodedata.category(c) != "Mn" and c not in " \t"]
    if len(letters) < 3:
        return "معلوم"
    # First letter (مضارعة) should have damma for passive
    j = letters[0] + 1
    v0 = None
    while j < len(nfd) and unicodedata.category(nfd[j]) == "Mn":
        v0 = nfd[j]
        j += 1
    # Second root letter (letters[1] might be after prefix): fatha
    idx_second = letters[1] if len(letters) > 1 else letters[0]
    k = idx_second + 1
    v_second = None
    while k < len(nfd) and unicodedata.category(nfd[k]) == "Mn":
        v_second = nfd[k]
        k += 1
    if v0 == "\u064F" and v_second == "\u064E":
        return "مجهول"
    return "معلوم"


def _detect_voice(word: str, stripped: str, tense: str) -> str:
    """بناء: معلوم | مجهول."""
    if tense == "ماضي":
        return _detect_voice_madi(word, stripped)
    if tense == "مضارع":
        return _detect_voice_mudari(word, stripped)
    return "معلوم"


def _detect_person(word: str, stripped: str, tense: str) -> int:
    """شخص: 1 | 2 | 3."""
    bare = _bare(stripped) if stripped else _bare(word)
    if not bare:
        return 3
    if tense == "مضارع":
        if word and word[0] == "\u0623":
            return 1
        if bare[0] == "ن":
            return 1
        if bare[0] == "ت":
            return 2
        if bare[0] == "ي":
            return 3
        if bare[0] in "أا":
            return 1
        return 3
    if tense == "أمر":
        return 2
    return 3


def _detect_gender(word: str, stripped: str, tense: str) -> str:
    """جنس: مذكر | مؤنث."""
    bare = _bare(stripped) if stripped else _bare(word)
    if not bare:
        return "مذكر"
    # مؤنث ماضي: ends with ت
    if tense == "ماضي" and (bare.endswith("ت") or bare.endswith("تْ")):
        return "مؤنث"
    # مؤنث مضارع: starts with ت (for 3rd fem)
    if tense == "مضارع" and len(bare) >= 2 and bare[0] == "ت" and bare[1] not in "ون":
        # تَفْعَلُ = قد تكون مؤنث غائب
        return "مؤنث"
    if tense == "أمر":
        if bare.endswith("ي") and len(bare) >= 3:
            return "مؤنث"
        if bare.endswith("ن") and len(bare) >= 3:
            return "مؤنث"
    return "مذكر"


def _detect_number(word: str, stripped: str, tense: str) -> str:
    """عدد: مفرد | مثنى | جمع."""
    bare = _bare(stripped) if stripped else _bare(word)
    if not bare or len(bare) < 2:
        return "مفرد"
    # جمع ماضي: وا (before checking single ا for مثنى)
    if bare.endswith("وا"):
        return "جمع"
    # جمع مضارع: ون
    if bare.endswith("ون"):
        return "جمع"
    # مثنى ماضي: ends with ا (كتَبَا) — not وا
    if tense == "ماضي" and bare.endswith("ا") and len(bare) >= 4:
        return "مثنى"
    # مثنى مضارع: ان / ين
    if bare.endswith("ان") or bare.endswith("ين"):
        return "مثنى"
    # نون النسوة
    if bare.endswith("ن") and len(bare) >= 4 and tense == "أمر":
        return "جمع"
    return "مفرد"


def _infer_pattern(word: str, stripped: str, tense: str) -> str:
    """Best-effort verb pattern label (فَعَلَ, فَعَلَتْ, يَفْعَلُ, etc.)."""
    if tense == "ماضي":
        return "فَعَلَ"
    if tense == "مضارع":
        return "يَفْعَلُ"
    if tense == "أمر":
        return "افْعَلْ"
    return "فَعَلَ"


def analyze_verb(word: str, stripped: str, root: str) -> VerbFeatures:
    """
    Analyze verb and return tense, voice, person, number, gender, pattern.
    Uses diacritics from word; no hardcoded word lists.
    """
    tense = _detect_tense(word, stripped)
    voice = _detect_voice(word, stripped, tense)
    person = _detect_person(word, stripped, tense)
    number = _detect_number(word, stripped, tense)
    gender = _detect_gender(word, stripped, tense)
    pattern = _infer_pattern(word, stripped, tense)
    return VerbFeatures(
        tense=tense,
        voice=voice,
        person=person,
        number=number,
        gender=gender,
        pattern=pattern,
    )
