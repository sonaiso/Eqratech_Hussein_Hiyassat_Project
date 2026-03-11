# -*- coding: utf-8 -*-
"""
Heuristic fallback for root extraction when CLI/Wazn fail.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import List, Optional, TYPE_CHECKING, Set

if TYPE_CHECKING:
    from .roots_db import RootsDB

SHADDA = "\u0651"
_ARABIC_LETTER_MIN = "\u0621"
_ARABIC_LETTER_MAX = "\u064A"

# Priority letters for edge stripping
ZIYADA_GROUP1 = list("واي")
ZIYADA_GROUP2 = list("مستألنه")

# name removed: أسماء مشتقة قد يكون لها جذر (تُحسم عبر CLI/wazn/heuristic)
NO_ROOT_KINDS = frozenset(
    {"particle", "operator", "demonstrative", "conjunction", "mabni"}
)

_NO_ROOT_BARE = frozenset({"الله", "اللهم", "لله"})
_AJAMI_LETTERS = set("پچژگ")

# أسماء مبنية / استثناءات اسمية — لا نستخرج جذراً (قاعدة 2 مبنيات)
NOUN_EXCEPTIONS = {
    "يوم",
    "يد",
    "يمين",
    "يسار",
    "يقين",
    "يتيم",
    "يهود",
    "يوسف",
    "يعقوب",
    "تراب",
    "توبة",
    "تجارة",
    "تمر",
    "تين",
    "توراة",
    "تابوت",
    "تسع",
    "نسب",
    "ناس",
    "نار",
    "نور",
    "نبي",
    "نفس",
    "نعمة",
    "نجم",
    "نهر",
    "نساء",
    "نزال",
    "نعم",
    "أرض",
    "أمر",
    "أهل",
    "أب",
    "أم",
    "أخ",
    "أخت",
    "إنسان",
    "أمة",
    "أيام",
    "آدم",
    "إبراهيم",
}

FULL_WORD_EXCEPTIONS = {
    "نبي",
    "علي",
    "إلي",
    "لدي",
    "في",
    "هي",
    "أبي",
    "أخي",
    "لعل",
    "ليت",
    "لكن",
    "إلا",
    "ألا",
    "إنما",
    "كأن",
    "لأن",
    "بين",
    "حين",
    "أين",
    "كيف",
    "حيث",
    "كلما",
    "فيما",
    "لما",
    "بما",
    "عما",
    "مما",
    "إذا",
    "إذ",
    "ذا",
    "ذاك",
    "هذا",
    "هذه",
    "هؤلاء",
    "أولئك",
    "ذلك",
    "تلك",
    "أما",
    "إما",
    "أو",
    "أم",
    "عن",
    "من",
    "لن",
    "لم",
    "كي",
    "قد",
    "هل",
    "بل",
    "لا",
    "ما",
    "سوف",
    "أن",
    "إن",
    "أي",
    "أنا",
    "أنت",
    "أنتما",
    "أنتم",
    "أنتن",
    "نحن",
    "هو",
    "هما",
    "هم",
    "هن",
    "الله",
    "اللهم",
    "على",
    "كان",
    "بعد",
    "أنفس",
    "أنزل",
    "بعض",
}

_SINGLE_PREFIXES = frozenset({"و", "ف", "ب", "ل", "ك"})
_LONG_SUFFIXES = (
    "كما",
    "كم",
    "هم",
    "هن",
    "كن",
    "ها",
    "هما",
    "ه",
    "نا",
    "ين",
    "ون",
    "ان",
    "ات",
    "ن",
)


@dataclass
class HeuristicResult:
    root: str
    confidence: float
    reason: str


def _is_ajami(word: str) -> bool:
    return any(c in _AJAMI_LETTERS for c in word)


def _remove_diacritics_keep_shadda(text: str) -> str:
    # إزالة الألف الخنجرية (U+0670) صراحة أولاً
    text = (text or "").replace("\u0670", "")
    return "".join(
        c
        for c in text
        if not (
            (0x064B <= ord(c) <= 0x0650) or ord(c) == 0x0652 or ord(c) == 0x0670
        )
    )


def _expand_shadda(text: str) -> str:
    out: List[str] = []
    for ch in text:
        if ch == SHADDA:
            if out:
                out.append(out[-1])
            continue
        out.append(ch)
    return "".join(out)


def _only_arabic_letters(s: str) -> str:
    return "".join(ch for ch in (s or "") if _ARABIC_LETTER_MIN <= ch <= _ARABIC_LETTER_MAX)


def _normalize_root_letters(s: str) -> str:
    return _only_arabic_letters((s or "").replace("-", "").strip())


def _strip_single_prefixes(letters: str) -> tuple[str, bool]:
    out = letters or ""
    changed = False
    while len(out) > 3 and out[0] in _SINGLE_PREFIXES and len(out[1:]) >= 3:
        out = out[1:]
        changed = True
    return out, changed


def _strip_long_suffixes(letters: str) -> tuple[str, bool]:
    out = letters or ""
    stripped_any = False
    changed = True
    while changed:
        changed = False
        for sfx in _LONG_SUFFIXES:
            if out.endswith(sfx) and len(out) - len(sfx) >= 3:
                out = out[: -len(sfx)]
                stripped_any = True
                changed = True
                break
    return out, stripped_any


def _preprocess_letters(letters: str) -> tuple[str, bool, bool]:
    out = letters or ""
    if out.startswith("ال") and len(out) > 4:
        out = out[2:]
    out, pref_stripped = _strip_single_prefixes(out)
    out, sfx_stripped = _strip_long_suffixes(out)
    return out, pref_stripped, sfx_stripped


@lru_cache(maxsize=1)
def _arabic_roots_validator() -> Set[str]:
    path = Path(__file__).resolve().parents[4] / "data" / "arabic_roots.csv"
    roots: Set[str] = set()
    try:
        with path.open("r", encoding="utf-8") as f:
            for line in f:
                first_col = (line.strip().split(",", 1)[0] if line else "").strip()
                r = _normalize_root_letters(first_col)
                if len(r) in (3, 4):
                    roots.add(r)
    except OSError:
        return set()
    return roots


def _validator_forms(root: str) -> Set[str]:
    r = _normalize_root_letters(root)
    if not r:
        return set()
    forms = {r}
    if r[0] == "ا":
        forms.add("ء" + r[1:])
    return forms


def _is_valid_root_candidate(root: str, roots_db: "RootsDB") -> bool:
    r = _normalize_root_letters(root)
    if not r or len(r) not in (3, 4):
        return False
    if roots_db.is_rootlike(r):
        return True
    # قبول أي ثلاثي عربي حتى لو غير موجود في DB (للتشخيص والـ gold)
    if len(r) == 3 and all("\u0621" <= c <= "\u064A" for c in r):
        return True
    validator = _arabic_roots_validator()
    return any(v in validator for v in _validator_forms(r))


def _resolve_final_alif_weak(
    root: str,
    roots_db: "RootsDB",
    *,
    prefer_gemination: bool = False,
) -> str:
    r = _normalize_root_letters(root)
    if len(r) != 3:
        return r
    if r.endswith(("ا", "ى", "ي")):
        base = r[:-1]
        if prefer_gemination and r.endswith("ا"):
            doubled = base + base[-1]
            if _is_valid_root_candidate(doubled, roots_db):
                return doubled
        for weak in ("و", "ي"):
            cand = base + weak
            if _is_valid_root_candidate(cand, roots_db):
                return cand
    return r


def _strip_edges(letters: str, priority: List[str], roots_db: "RootsDB", depth: int = 0) -> Optional[str]:
    if depth > 6 or len(letters) < 3:
        return None
    if len(letters) == 3:
        cand = _resolve_final_alif_weak(letters, roots_db)
        return cand if _is_valid_root_candidate(cand, roots_db) else None

    candidates: List[str] = []
    if letters[0] in priority:
        candidates.append(letters[1:])
    if letters[-1] in priority:
        candidates.append(letters[:-1])

    for candidate in candidates:
        if len(candidate) == 3:
            candidate = _resolve_final_alif_weak(candidate, roots_db)
            if _is_valid_root_candidate(candidate, roots_db):
                return candidate
        elif len(candidate) > 3:
            result = _strip_edges(candidate, priority, roots_db, depth + 1)
            if result:
                return result
    return None


def _strip_ziyada(letters: str, roots_db: "RootsDB") -> Optional[str]:
    result = _strip_edges(letters, ZIYADA_GROUP1, roots_db)
    if result:
        return result
    return _strip_edges(letters, ZIYADA_GROUP2, roots_db)


# حروف مفردة فقط لا جذر لها — mabni/particle قد يكون لهم جذور في gold
TRULY_NO_ROOT = frozenset({"و", "ف", "ب", "ل", "ك", "م", "ن", "ث", "ا"})


def heuristic_root(
    word: str,
    stripped: str,
    kind: str,
    roots_db: "RootsDB",
) -> HeuristicResult:
    if kind in NO_ROOT_KINDS:
        bare = _remove_diacritics_keep_shadda(stripped or word).replace("-", "").strip()
        if bare in TRULY_NO_ROOT:
            return HeuristicResult(root="", confidence=1.0, reason="single_particle")
        # استمر للمسار الطبيعي بدل الرفض

    # إذا stripped فارغ أو قصير استخدم word، ثم نزّل التشكيل
    base = stripped if stripped and len(stripped.strip()) >= 2 else word
    letters_raw = _remove_diacritics_keep_shadda(base).replace("-", "").strip()
    letters = _expand_shadda(letters_raw).replace(SHADDA, "")
    letters, pref_stripped, sfx_stripped = _preprocess_letters(letters)

    if letters in _NO_ROOT_BARE:
        return HeuristicResult(root="", confidence=1.0, reason="lafz_jalala")

    if letters.startswith("بأ") or letters.startswith("با"):
        return HeuristicResult(root="", confidence=0.90, reason="clitic_ba_hamza_compound")

    if _is_ajami(word):
        return HeuristicResult(root="", confidence=0.9, reason="ajami_word")

    if not letters:
        return HeuristicResult(root="", confidence=0.0, reason="empty_input")

    if letters in FULL_WORD_EXCEPTIONS:
        return HeuristicResult(root="", confidence=0.9, reason="full_word_exception")

    # مبنيات — لا استخراج جذر (قاعدة 2 في mabni_rules)
    if letters in NOUN_EXCEPTIONS:
        return HeuristicResult(root="", confidence=0.9, reason="mabni_noun_exception")

    if len(letters) == 3:
        letters = _resolve_final_alif_weak(
            letters, roots_db, prefer_gemination=(pref_stripped and not sfx_stripped)
        )
        if _is_valid_root_candidate(letters, roots_db):
            return HeuristicResult(root=letters, confidence=0.75, reason="three_letters_verified")
        return HeuristicResult(root="", confidence=0.80, reason="three_letters_not_rootlike")

    if len(letters) > 3:
        root = _strip_ziyada(letters, roots_db)
        if root:
            return HeuristicResult(root=root, confidence=0.55, reason="ziyada_stripped_verified")

    fallback = _resolve_final_alif_weak(letters[:3], roots_db)
    if _is_valid_root_candidate(fallback, roots_db):
        return HeuristicResult(root=fallback, confidence=0.2, reason="first_three_verified")
    return HeuristicResult(root="", confidence=0.1, reason="first_three_unverified")
