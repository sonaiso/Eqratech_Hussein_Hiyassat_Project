from __future__ import annotations

import re
import unicodedata
from typing import Dict, List, Tuple

FATHA = "\u064e"
DAMMA = "\u064f"
KASRA = "\u0650"
SUKUN = "\u0652"
SHADDA = "\u0651"
TANWIN_FATH = "\u064b"
TANWIN_DAMM = "\u064c"
TANWIN_KASR = "\u064d"

SHORT_VOWELS = {FATHA, DAMMA, KASRA, TANWIN_FATH, TANWIN_DAMM, TANWIN_KASR}
ALL_MARKS = {
    FATHA,
    DAMMA,
    KASRA,
    SUKUN,
    SHADDA,
    TANWIN_FATH,
    TANWIN_DAMM,
    TANWIN_KASR,
}

ALIF = "\u0627"
WAW = "\u0648"
YA = "\u064a"
ALIF_MAQSURA = "\u0649"
ALIF_MADDA = "\u0622"
ALIF_WASLA = "\u0671"

WASL_NOUNS = {
    "اسم",
    "ابن",
    "ابنة",
    "امرؤ",
    "امرأة",
    "اثنان",
    "اثنتان",
    "ايم",
    "ايمن",
}

EXCLUDE_EXACT = {"حم", "دمت", "ص", "طس", "طسم", "طه", "عسق", "على", "ق"}
MUQATTAAT = {
    "الم",
    "المص",
    "الر",
    "المر",
    "كهيعص",
    "طه",
    "طسم",
    "طس",
    "يس",
    "حم",
    "حم عسق",
    "عسق",
    "ق",
    "ن",
    "ص",
}
MUQATTAAT_NOSPACE = {s.replace(" ", "") for s in MUQATTAAT}

ARABIC_TOKEN_RE = re.compile(r"[\u0600-\u06FF]+", re.UNICODE)


def is_arabic_letter(ch: str) -> bool:
    return ("\u0600" <= ch <= "\u06FF") and unicodedata.category(ch).startswith("L")


def normalize_word(w: str) -> str:
    w = unicodedata.normalize("NFC", str(w))
    w = w.replace("\u0640", "")
    return w.strip()


def strip_marks(text: str) -> str:
    return "".join(ch for ch in text if not (unicodedata.combining(ch) and ch in ALL_MARKS))


def split_letters_and_marks(text: str):
    out: List[Tuple[str, List[str]]] = []
    base = None
    marks: List[str] = []
    for ch in text:
        if unicodedata.combining(ch) != 0 and ch in ALL_MARKS:
            if base is not None:
                marks.append(ch)
            continue
        if base is not None:
            out.append((base, marks))
        base = ch
        marks = []
    if base is not None:
        out.append((base, marks))
    return out


def expand_shadda(units):
    expanded = []
    for letter, marks in units:
        if SHADDA in marks:
            second_marks = [m for m in marks if m != SHADDA]
            expanded.append((letter, [SUKUN]))
            expanded.append((letter, second_marks))
        else:
            expanded.append((letter, marks))
    return expanded


def has_any(marks, target):
    return any(m in target for m in marks)


def normalize_missing_harakat(word: str) -> str:
    w = normalize_word(word)
    if w == "ولا":
        return "و" + FATHA + "ل" + FATHA + "ا"
    if w.startswith("ل" + SUKUN + "ي" + FATHA):
        return "ل" + KASRA + w[2:]
    return w


def normalize_initial_hamza(word: str) -> str:
    w = normalize_word(word)
    bare = strip_marks(w)
    if not bare or bare[0] not in {"ا", "أ", "إ", "آ", ALIF_WASLA}:
        return w
    if bare[0] != "ا":
        return w
    is_wasl = False
    if bare.startswith("ال"):
        is_wasl = True
    else:
        for prefix in ("است", "ان", "افت", "اف"):
            if bare.startswith(prefix):
                is_wasl = True
                break
        else:
            if any(bare.startswith(n) for n in WASL_NOUNS):
                is_wasl = True
    idx = w.find("ا")
    if idx == -1:
        return w
    replacement = ALIF_WASLA if is_wasl else "أ"
    return w[:idx] + replacement + w[idx + 1 :]


def should_exclude(token: str) -> bool:
    w = normalize_word(token)
    bare = strip_marks(w)
    bare_nospace = bare.replace(" ", "")
    if re.search(r"[A-Za-z]", w):
        return True
    if bare in EXCLUDE_EXACT:
        return True
    if len(bare) == 1 and is_arabic_letter(bare):
        return True
    if bare_nospace in MUQATTAAT_NOSPACE:
        return True
    return False


def cv_pattern(word: str) -> str:
    w = normalize_word(word)
    units = expand_shadda(split_letters_and_marks(w))
    out: List[str] = []
    prev_marks: List[str] = []
    first_idx = None
    for i, (ch, _) in enumerate(units):
        if is_arabic_letter(ch):
            first_idx = i
            break
    if first_idx is not None:
        first_letter = units[first_idx][0]
        if first_letter in {ALIF_WASLA, "أ", "إ", "آ"}:
            out.extend(["C", "V"])
            units = units[:first_idx] + units[first_idx + 1 :]
    for letter, marks in units:
        if not is_arabic_letter(letter):
            prev_marks = marks
            continue
        is_madd = False
        if letter == ALIF:
            is_madd = has_any(prev_marks, {FATHA, TANWIN_FATH})
        elif letter == WAW:
            is_madd = has_any(prev_marks, {DAMMA, TANWIN_DAMM})
        elif letter in {YA, ALIF_MAQSURA}:
            is_madd = has_any(prev_marks, {KASRA, TANWIN_KASR})
        if letter == ALIF_MADDA:
            out.append("C")
        elif is_madd:
            out.append("V")
        else:
            out.append("C")
            if has_any(marks, SHORT_VOWELS):
                out.append("V")
        prev_marks = marks
    return "".join(out)


def advanced_cv_pattern(word: str) -> str:
    w = normalize_word(word)
    units = expand_shadda(split_letters_and_marks(w))
    out: List[str] = []
    prev_marks: List[str] = []

    first_idx = None
    for i, (ch, _) in enumerate(units):
        if is_arabic_letter(ch):
            first_idx = i
            break
    if first_idx is not None:
        first_letter = units[first_idx][0]
        if first_letter in {ALIF_WASLA, "أ", "إ", "آ"}:
            out.extend(["C", "V", "a"])
            units = units[:first_idx] + units[first_idx + 1 :]

    for letter, marks in units:
        if not is_arabic_letter(letter):
            prev_marks = marks
            continue

        symbol = _symbol_from_marks(marks)
        is_madd = False
        if letter == ALIF:
            is_madd = has_any(prev_marks, {FATHA, TANWIN_FATH})
            if is_madd:
                symbol = _symbol_from_marks(prev_marks) or symbol or "a"
        elif letter == WAW:
            is_madd = has_any(prev_marks, {DAMMA, TANWIN_DAMM})
            if is_madd:
                symbol = _symbol_from_marks(prev_marks) or symbol or "o"
        elif letter in {YA, ALIF_MAQSURA}:
            is_madd = has_any(prev_marks, {KASRA, TANWIN_KASR})
            if is_madd:
                symbol = _symbol_from_marks(prev_marks) or symbol or "i"

        if letter == ALIF_MADDA:
            out.append("C")
            out.append("V")
            out.append("a")
        elif is_madd:
            out.append("V")
            out.append(symbol or "a")
        else:
            out.append("C")
            if symbol:
                out.append("V")
                out.append(symbol)

        prev_marks = marks

    return "".join(out)


def _symbol_from_marks(marks: List[str]) -> str:
    if not marks:
        return ""
    mapping = [
        (FATHA, "a"),
        (TANWIN_FATH, "a"),
        (DAMMA, "o"),
        (TANWIN_DAMM, "o"),
        (KASRA, "i"),
        (TANWIN_KASR, "i"),
    ]
    for mark, symbol in mapping:
        if mark in marks:
            return symbol
    return ""


def follows_cv_law(cv: str) -> Tuple[bool, str]:
    if not cv:
        return False, "empty_cv"
    if len(cv) < 2 or cv[0] != "C" or cv[1] != "V":
        return False, "does_not_start_with_CV"
    i = 0
    while True:
        k = None
        for j in range(i + 2, len(cv) - 1):
            if cv[j] == "C" and cv[j + 1] == "V":
                k = j
                break
        if k is None:
            return True, "ok"
        i = k


def analyze_text_for_cv(text: str) -> List[Dict[str, str]]:
    seen = set()
    results: List[Dict[str, str]] = []
    for match in ARABIC_TOKEN_RE.finditer(text):
        token = normalize_word(match.group(0))
        if not token or token in seen:
            continue
        seen.add(token)
        if should_exclude(token):
            results.append(
                {
                    "word": token,
                    "normalized": token,
                    "cv": None,
                    "ok": False,
                    "reason": "excluded",
                }
            )
            continue
        normalized = normalize_initial_hamza(token)
        normalized = normalize_missing_harakat(normalized)
        cv = cv_pattern(normalized)
        ok, reason = follows_cv_law(cv)
        results.append(
            {
                "word": token,
                "normalized": normalized,
                "cv": cv,
                "ok": ok,
                "reason": reason,
            }
        )
    return results
