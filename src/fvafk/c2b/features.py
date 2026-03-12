"""
Feature extraction (Plan A, V1).

Deterministic heuristics for morphology/grammar features to be included in CLI output.
This is intentionally conservative: when unsure, we return `None`/`unknown`.
"""

from __future__ import annotations

import unicodedata
from typing import Any, Dict, Optional, TYPE_CHECKING

from .morpheme import Pattern
from .root_extractor import RootExtractionResult
from .word_classifier import WordKind

if TYPE_CHECKING:
    from .mabni_rules import MabniResult


def _strip_diacritics(text: str) -> str:
    return "".join(
        ch for ch in unicodedata.normalize("NFC", text)
        if unicodedata.combining(ch) == 0
    ).replace("ـ", "").strip()


def _detect_case_from_token(token: str) -> Optional[str]:
    # Prefer explicit tanwin if present in original surface.
    if "ٌ" in token:
        return "nominative"
    if "ً" in token:
        return "accusative"
    if "ٍ" in token:
        return "genitive"
    # Infer from last short vowel (حركة) when no tanwin: ضمة→مرفوع، فتحة→منصوب، كسرة→مجرور
    if not token:
        return None
    normalized = unicodedata.normalize("NFD", token)
    for i in range(len(normalized) - 1, -1, -1):
        c = normalized[i]
        if unicodedata.category(c) != "Mn":
            break
        if c == "\u064F":  # damma ُ
            return "nominative"
        if c == "\u064E":  # fatha َ
            return "accusative"
        if c == "\u0650":  # kasra ِ
            return "genitive"
    return None


def _infer_definiteness(bare: str) -> Optional[bool]:
    if bare.startswith("ال") or bare.startswith("ٱل"):
        return True
    return None


def _suffix_parts(suffix: Optional[str]) -> list[str]:
    if not suffix:
        return []
    return [p for p in suffix.split("+") if p]


def _suffix_tail(suffix: Optional[str]) -> Optional[str]:
    parts = _suffix_parts(suffix)
    return parts[-1] if parts else None


def _infer_number(bare: str, *, suffix: Optional[str] = None, pattern: Optional[Pattern] = None) -> Optional[str]:
    suf = _suffix_tail(suffix) or ""
    # Strong cues from extracted suffix
    if suf == "ان":
        return "dual"
    if suf in {"ون", "ين", "ات"}:
        return "plural"

    # Surface fallback
    if bare.endswith("ان") and len(bare) > 3:
        return "dual"
    if bare.endswith(("ون", "ين", "ات")) and len(bare) > 3:
        return "plural"

    # Pattern cue (if available)
    if pattern and "plural" in (pattern.pattern_type.value or ""):
        return "plural"

    return "singular"


# Words that are feminine by convention (سماعي) despite lacking a تاء مربوطة.
_FEMININE_SAMAIC: frozenset = frozenset({
    "أرض", "شمس", "نار", "نفس", "روح", "يد", "عين", "أذن",
    "دار", "حرب", "بئر", "ريح", "سماء", "أم",
})


def _infer_gender(bare: str, *, suffix: Optional[str] = None) -> Optional[str]:
    suf = _suffix_tail(suffix)
    # Feminine markers
    if bare.endswith("ات") or (suf == "ات"):
        return "feminine"
    if bare.endswith("ة"):
        return "feminine"
    # Masculine plural endings
    if bare.endswith(("ون", "ين")) or suf in {"ون", "ين"}:
        return "masculine"
    # Feminine by convention (سماعي) — strip ال prefix before lookup
    lookup = bare[2:] if bare.startswith("ال") else bare
    if lookup in _FEMININE_SAMAIC:
        return "feminine"
    # Default for analysable content words with no feminine marker
    if len(bare) < 2:
        return None
    return "masculine"


def _infer_case(bare: str, *, token: str, suffix: Optional[str] = None) -> Optional[str]:
    # IMPORTANT: suffix cues must override last-vowel cues (e.g., كَاتِبُونَ is nominative)
    suf = _suffix_tail(suffix) or ""

    # Dual + sound masculine plural endings
    if suf == "ون" or bare.endswith("ون") or suf == "ان" or bare.endswith("ان"):
        return "nominative"
    if suf == "ين" or bare.endswith("ين"):
        return "accusative_or_genitive"

    # Otherwise: case from diacritics/tanwin/short vowel
    return _detect_case_from_token(token)


_DETACHED_PRONOUN_FEATURES: Dict[str, Dict[str, Any]] = {
    "انا": {"person": 1, "number": "singular"},
    "نحن": {"person": 1, "number": "plural"},
    "انت": {"person": 2, "number": "singular"},
    "انتما": {"person": 2, "number": "dual"},
    "انتم": {"person": 2, "number": "plural", "gender": "masculine"},
    "انتن": {"person": 2, "number": "plural", "gender": "feminine"},
    "هو": {"person": 3, "number": "singular", "gender": "masculine"},
    "هي": {"person": 3, "number": "singular", "gender": "feminine"},
    "هما": {"person": 3, "number": "dual"},
    "هم": {"person": 3, "number": "plural", "gender": "masculine"},
    "هن": {"person": 3, "number": "plural", "gender": "feminine"},
}


_ATTACHED_PRONOUN_SUFFIXES: Dict[str, Dict[str, Any]] = {
    "ه": {"person": 3, "number": "singular", "gender": "masculine"},
    "ها": {"person": 3, "number": "singular", "gender": "feminine"},
    "هما": {"person": 3, "number": "dual"},
    "هم": {"person": 3, "number": "plural", "gender": "masculine"},
    "هن": {"person": 3, "number": "plural", "gender": "feminine"},
    "ك": {"person": 2, "number": "singular"},
    "كم": {"person": 2, "number": "plural", "gender": "masculine"},
    "كن": {"person": 2, "number": "plural", "gender": "feminine"},
    "كما": {"person": 2, "number": "dual"},
    "نا": {"person": 1, "number": "plural"},
    "ني": {"person": 1, "number": "singular"},
    "ي": {"person": 1, "number": "singular"},
}


def _attached_pronoun_from_suffix(suffix: str) -> Optional[Dict[str, Any]]:
    # Prefer matching the last part if suffix contains multiple pieces (e.g., "ك+هم").
    tail = _suffix_tail(suffix) or suffix
    info = _ATTACHED_PRONOUN_SUFFIXES.get(tail)
    if not info:
        return None
    return {"suffix": tail, **info}


def _apply_mabni_rules(features: Dict[str, Any], mabni_result: Optional["MabniResult"]) -> None:
    """Rule 1 & 4: For mabniyat, no case from vowel; number/gender from DB."""
    if not mabni_result or not getattr(mabni_result, "is_mabni", False):
        return
    features["case"] = None
    features["number"] = getattr(mabni_result, "number", None) or features.get("number")
    features["gender"] = getattr(mabni_result, "gender", None) or features.get("gender")
    features["is_mabni"] = True
    features["i3rab_status"] = getattr(mabni_result, "i3rab_status", "مبني")


def extract_features(
    token: str,
    extraction: RootExtractionResult,
    pattern: Optional[Pattern],
    kind: WordKind,
    mabni_result: Optional["MabniResult"] = None,
) -> Dict[str, Any]:
    bare = _strip_diacritics(token)
    features: Dict[str, Any] = {
        "kind": kind.value if hasattr(kind, "value") else str(kind),
        "normalized": extraction.normalized_word,
        "stripped": extraction.stripped_word,
    }

    # Root-related (if any)
    if extraction.root:
        features["root_type"] = extraction.root.root_type.name.lower()

    # Pattern-related (if any)
    if pattern:
        # keep what PatternMatcher already computed in `pattern.features`
        features.update(pattern.features or {})
        features.setdefault("pattern_type", pattern.pattern_type.name)

    # Pronouns: do not apply noun/verb heuristics that assume singular by default.
    if kind == WordKind.PRONOUN:
        p = _DETACHED_PRONOUN_FEATURES.get(bare)
        if p:
            features["pronoun"] = {"surface": token, "bare": bare, **p}
            features["number"] = p.get("number")
            features["gender"] = p.get("gender", "unknown")
            features["definite"] = None
            features["case"] = None
        else:
            features["number"] = None
            features["gender"] = "unknown"
            features["definite"] = None
            features["case"] = None
        _apply_mabni_rules(features, mabni_result)
        return features

    # Closed-class items that are not analyzed morphologically.
    if kind in {WordKind.DEMONSTRATIVE, WordKind.NAME, WordKind.PARTICLE}:
        features["definite"] = _infer_definiteness(bare)
        features["number"] = None
        features["gender"] = "unknown"
        features["case"] = _detect_case_from_token(token)
        # If a suffix is present and matches a known clitic pronoun, expose it.
        if extraction.suffix:
            ap = _attached_pronoun_from_suffix(extraction.suffix)
            if ap:
                features["attached_pronoun"] = ap
        _apply_mabni_rules(features, mabni_result)
        return features

    # V1 heuristics
    features["definite"] = _infer_definiteness(bare)
    features["number"] = _infer_number(bare, suffix=extraction.suffix or None, pattern=pattern)
    _gender = _infer_gender(bare, suffix=extraction.suffix or None)
    mabni_kind = getattr(WordKind, "MABNI", None)
    if _gender is None:
        if kind in {WordKind.NOUN, WordKind.VERB}:
            _gender = "masculine"
        elif kind in {WordKind.PARTICLE, WordKind.OPERATOR} or (mabni_kind is not None and kind == mabni_kind):
            _gender = ""
        else:
            _gender = ""
    features["gender"] = _gender
    features["case"] = _infer_case(bare, token=token, suffix=extraction.suffix or None)

    # Keep category consistent with POS decision at the CLI layer.
    if kind in {WordKind.VERB, WordKind.NOUN}:
        features["category"] = kind.value

    # Pronouns (detached) and clitics (attached)
    if extraction.suffix:
        ap = _attached_pronoun_from_suffix(extraction.suffix)
        if ap:
            features["attached_pronoun"] = ap

    _apply_mabni_rules(features, mabni_result)
    return features

