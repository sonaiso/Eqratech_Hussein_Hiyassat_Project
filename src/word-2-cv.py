#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
import csv
import sys
import unicodedata

# -----------------------------
# Harakat / marks
# -----------------------------
FATHA = "\u064e"
DAMMA = "\u064f"
KASRA = "\u0650"
SUKUN = "\u0652"
SHADDA = "\u0651"
TANWIN_FATH = "\u064b"
TANWIN_DAMM = "\u064c"
TANWIN_KASR = "\u064d"

SHORT_VOWELS = {FATHA, DAMMA, KASRA, TANWIN_FATH, TANWIN_DAMM, TANWIN_KASR}
ALL_MARKS = {FATHA, DAMMA, KASRA, SUKUN, SHADDA, TANWIN_FATH, TANWIN_DAMM, TANWIN_KASR}

# Long vowels
ALIF = "\u0627"
WAW = "\u0648"
YA = "\u064a"
ALIF_MAQSURA = "\u0649"

ALIF_MADDA = "\u0622"   # آ
ALIF_WASLA = "\u0671"   # ٱ

SUN_LETTERS = {
    "ت", "ث", "د", "ذ", "ر", "ز", "س", "ش",
    "ص", "ض", "ط", "ظ", "ل", "ن"
}

# -----------------------------
# Basic helpers
# -----------------------------
def is_arabic_letter(ch: str) -> bool:
    return ("\u0600" <= ch <= "\u06FF") and unicodedata.category(ch).startswith("L")

def normalize_word(w: str) -> str:
    w = unicodedata.normalize("NFC", str(w))
    w = w.replace("\u0640", "")  # tatweel
    return w.strip()

def strip_harakat_only(w: str) -> str:
    return "".join(ch for ch in w if not (unicodedata.combining(ch) and ch in ALL_MARKS))

def strip_all_marks(w: str) -> str:
    return "".join(ch for ch in w if not (unicodedata.combining(ch) and ch in ALL_MARKS))

def split_letters_and_marks(text: str):
    out = []
    base = None
    marks = []
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
            expanded.append((letter, [SUKUN]))       # first consonant
            expanded.append((letter, second_marks))  # second consonant with remaining marks
        else:
            expanded.append((letter, marks))
    return expanded

def has_any(marks, s):
    return any(m in s for m in marks)

# -----------------------------
# Missing-harakat normalization (your last correction)
# -----------------------------
def normalize_missing_harakat(word: str) -> str:
    """
    Fix cases where your source text lost harakat:
    - ولا -> وَلَا
    - لْيَ... -> لِيَ... (lam is kasra, not sukun)
    """
    w = normalize_word(word)

    if w == "ولا":
        return "و" + FATHA + "ل" + FATHA + "ا"   # وَلَا

    if w.startswith("ل" + SUKUN + "ي" + FATHA):
        return "ل" + KASRA + w[2:]  # replace "لْ" with "لِ"

    return w

# -----------------------------
# Exclusions (your request)
# -----------------------------
# Note: do not list bare "على" — it matches the common preposition عَلَى after strip_harakat_only.
EXCLUDE_EXACT = {"حم", "دمت", "ص", "طس", "طسم", "طه", "عسق", "ق"}
MUQATTAAT = {
    "الم", "المص", "الر", "المر", "كهيعص", "طه", "طسم", "طس", "يس",
    "حم", "حم عسق", "عسق", "ق", "ن", "ص"
}
MUQATTAAT_NOSPACE = {s.replace(" ", "") for s in MUQATTAAT}

def should_exclude(token: str) -> bool:
    w = normalize_word(token)
    bare = strip_harakat_only(w)
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

# -----------------------------
# Initial Hamza Normalization
# -----------------------------
WASL_NOUNS = {"اسم", "ابن", "ابنة", "امرؤ", "امرأة", "اثنان", "اثنتان", "ايم", "ايمن"}

def normalize_initial_hamza(word: str) -> str:
    """
    If word starts with bare 'ا' (no hamza), decide:
      - wasl  -> convert to 'ٱ'
      - qat'  -> convert to 'أ'
    """
    w = normalize_word(word)
    bare = strip_all_marks(w)
    if not bare:
        return w

    if bare[0] in {"أ", "إ", "آ", ALIF_WASLA}:
        return w
    if bare[0] != "ا":
        return w

    is_wasl = False
    if bare.startswith("ال"):
        is_wasl = True
    elif bare.startswith(("است", "ان", "افت", "اف")):
        is_wasl = True
    else:
        for n in WASL_NOUNS:
            if bare.startswith(n):
                is_wasl = True
                break

    idx = w.find("ا")
    if idx == -1:
        return w

    return w[:idx] + (ALIF_WASLA if is_wasl else "أ") + w[idx + 1 :]

# -----------------------------
# CV generator
# -----------------------------
def apply_al_tareef_pronunciation(units):
    """
    Pronunciation-aware handling of definite article:
    - if word starts with ٱل / ال
    - and the next consonant is a sun letter:
        remove the lam from pronunciation
        keep / enforce shadda on the following letter
    - if moon letter:
        keep lam as pronounced consonant
    """
    if len(units) < 3:
        return units

    first_letter = units[0][0]
    second_letter = units[1][0]
    third_letter, third_marks = units[2]

    if first_letter not in {ALIF_WASLA, ALIF}:
        return units

    if second_letter != "ل":
        return units

    if not is_arabic_letter(third_letter):
        return units

    if third_letter in SUN_LETTERS:
        if SHADDA not in third_marks:
            third_marks = [SHADDA] + third_marks
        return [units[0], (third_letter, third_marks)] + units[3:]

    return units

def _symbol_from_marks(marks: list) -> str:
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


def normalize_long_vowels(cv: str) -> str:
    if not cv:
        return ""
    return (
        cv.replace("VaVa", "VA")
        .replace("ViVi", "VI")
        .replace("VoVo", "VO")
    )


def cv_pattern_and_advanced(word: str) -> tuple[str, str]:
    """
    Single source of truth for CV + cv_advanced (vowel-quality).
    Same preprocessing as legacy cv_pattern: article pronunciation, shadda, initial hamza/wasl.
    """
    w = normalize_word(word)
    units = split_letters_and_marks(w)
    units = apply_al_tareef_pronunciation(units)
    units = expand_shadda(units)

    simple: list[str] = []
    advanced: list[str] = []
    prev_marks: list = []

    first_idx = None
    for i, (ch, _m) in enumerate(units):
        if is_arabic_letter(ch):
            first_idx = i
            break

    if first_idx is not None:
        first_letter = units[first_idx][0]
        if first_letter in {ALIF_WASLA, "أ", "إ", "آ"}:
            simple.extend(["C", "V"])
            fm = units[first_idx][1]
            sym0 = _symbol_from_marks(fm) or "a"
            advanced.extend(["C", "V", sym0])
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
        elif letter == YA or letter == ALIF_MAQSURA:
            is_madd = has_any(prev_marks, {KASRA, TANWIN_KASR})
            if is_madd:
                symbol = _symbol_from_marks(prev_marks) or symbol or "i"

        if letter == ALIF_MADDA:
            simple.append("C")
            advanced.extend(["C", "V", "a"])
        elif is_madd:
            simple.append("V")
            advanced.extend(["V", symbol or "a"])
        else:
            simple.append("C")
            advanced.append("C")
            if has_any(marks, SHORT_VOWELS):
                simple.append("V")
                if symbol:
                    advanced.extend(["V", symbol])

        prev_marks = marks

    return "".join(simple), normalize_long_vowels("".join(advanced))


def cv_pattern(word: str) -> str:
    """
    Pronunciation-aware CV:
    - WRITTEN harakat only
    - Shadda => CC
    - Madd letters => V only if previous has matching written haraka
    - Initial (ٱ/أ/إ/آ) => force starting CV (C+V) and remove that letter unit
    - Definite article:
        * moon lam stays
        * sun lam assimilates into next letter
    """
    return cv_pattern_and_advanced(word)[0]


def cv_advanced_pattern(word: str) -> str:
    """Vowel-quality CV (a/i/o) aligned with cv_pattern preprocessing."""
    return cv_pattern_and_advanced(word)[1]


def analyze_token_for_pipeline(token: str) -> dict:
    """
    One token -> cv / cv_advanced / normalization. Used by fvafk pipeline (L6).
    Excludes muqattaat etc. via should_exclude (same as batch main).
    """
    w = normalize_word(token)
    if should_exclude(token):
        return {
            "cv": "",
            "cv_advanced": "",
            "word_input": w,
            "word_normalized": w,
            "excluded": True,
            "cv_law_ok": False,
            "cv_law_reason": "excluded",
        }
    w_norm = normalize_initial_hamza(w)
    w_norm = normalize_missing_harakat(w_norm)
    cv_s, cv_a = cv_pattern_and_advanced(w_norm)
    ok, reason = follows_cv_law(cv_s)
    return {
        "cv": cv_s,
        "cv_advanced": cv_a,
        "word_input": w,
        "word_normalized": w_norm,
        "excluded": False,
        "cv_law_ok": ok,
        "cv_law_reason": reason,
    }

# -----------------------------
# CV-law validator
# -----------------------------
def follows_cv_law(cv: str):
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

# -----------------------------
# TXT tokenization
# -----------------------------
ARABIC_TOKEN_RE = re.compile(r"[\u0600-\u06FF]+", re.UNICODE)

def extract_unique_words(txt_path: str):
    unique = set()
    with open(txt_path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            for m in ARABIC_TOKEN_RE.finditer(line):
                w = normalize_word(m.group(0))
                if w:
                    unique.add(w)
    return sorted(unique)

def write_csv(rows, out_path, header):
    with open(out_path, "w", encoding="utf-8", newline="") as f:
        wr = csv.writer(f)
        wr.writerow(header)
        for r in rows:
            wr.writerow(r)

# -----------------------------
# Main
# -----------------------------
def main():
    if len(sys.argv) != 2:
        print("Usage: python3 one_shot_word2cv.py /path/to/input.txt")
        sys.exit(1)

    input_txt = sys.argv[1]
    words = extract_unique_words(input_txt)

    working = []
    notworking = []
    excluded = []

    for w in words:
        if should_exclude(w):
            excluded.append((w,))
            continue

        w_norm = normalize_initial_hamza(w)
        w_norm = normalize_missing_harakat(w_norm)  # ✅ THIS WAS MISSING
        cv, _cv_adv = cv_pattern_and_advanced(w_norm)
        ok, reason = follows_cv_law(cv)

        if ok:
            working.append((w, w_norm, cv))
        else:
            notworking.append((w, w_norm, cv, reason))

    write_csv(working, "cv-working.csv", ["word_original", "word_normalized", "cv"])
    write_csv(notworking, "cv-notworking.csv", ["word_original", "word_normalized", "cv", "reason"])
    write_csv(excluded, "cv-excluded.csv", ["word"])

    print(f"Unique words: {len(words)}")
    print(f"Excluded: {len(excluded)} -> cv-excluded.csv")
    print(f"Working: {len(working)} -> cv-working.csv")
    print(f"Not working: {len(notworking)} -> cv-notworking.csv")

if __name__ == "__main__":
    main()
