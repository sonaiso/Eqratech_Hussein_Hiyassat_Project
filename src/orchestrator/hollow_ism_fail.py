# -*- coding: utf-8 -*-
"""
Hollow-verb active participle (اسم الفاعل الأجوف) — root recovery and classification support.

اسم الفاعل من الأجوف يُرَدّ إلى أصل الفعل لا إلى ظاهره الكتابي:
صائم = ص-و-م ، قائل = ق-و-ل ، بائع = ب-ي-ع.
الهمزة في هذا النمط ناتجة صرفيًا وليست عين الجذر.

If the word matches the hollow active-participle surface pattern (e.g. فَائِل with hamza),
classify as ISM_FAIL(hollow), recover the triliteral root from the verbal origin / lexicon,
not from the surface hamza as middle radical. A confirmed correct root in arabic_word_state
must not be replaced by a surface-wrong middle (e.g. ص-ي-م for صائم).
"""

from __future__ import annotations

import re
from typing import Optional

_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")

# Documented hollow stems (normalized, no diacritics) → canonical hyphenated root.
# Extend incrementally; unlisted stems still match _RE_HOLLOW_ISM_SHAPE for ISM_FAIL classification.
KNOWN_HOLLOW_ISM_STEM_TO_ROOT: dict[str, str] = {
    "صائم": "ص-و-م",
    "قائل": "ق-و-ل",
    "بائع": "ب-ي-ع",
    "خائف": "خ-و-ف",
    "نائم": "ن-و-م",
}

# Surface shape: Radical + alif + yeh-with-hamza + radical (فَائِل as written).
_RE_HOLLOW_ISM_SHAPE = re.compile(r"^.\u0627\u0626.$")


def normalize_stem_key(stem: str) -> str:
    if not stem or not isinstance(stem, str):
        return ""
    s = _DIACRITICS.sub("", stem.strip()).replace("\u0651", "")
    # Unify alef variants for dictionary lookup only
    for a in ("\u0623", "\u0625", "\u0671", "\u0622"):
        s = s.replace(a, "\u0627")
    return s.strip()


def matches_hollow_ism_fail_shape(stem: str) -> bool:
    """True if stripped stem matches the فَائِل written shape (4 chars: C + ا + ئ + C)."""
    s = normalize_stem_key(stem)
    return bool(s) and bool(_RE_HOLLOW_ISM_SHAPE.match(s))


def is_hollow_ism_fail_candidate(stem: str) -> bool:
    """Listed hollow participle stem or generic فَائِل hamza shape."""
    s = normalize_stem_key(stem)
    if not s:
        return False
    if s in KNOWN_HOLLOW_ISM_STEM_TO_ROOT:
        return True
    return matches_hollow_ism_fail_shape(s)


def is_lexicon_listed_hollow_stem(stem: str) -> bool:
    """Stem appears in the documented KNOWN hollow participle inventory."""
    return normalize_stem_key(stem) in KNOWN_HOLLOW_ISM_STEM_TO_ROOT


def _split_root_letters(root_hyphen: str) -> list[str]:
    if not root_hyphen:
        return []
    parts = [p.strip() for p in root_hyphen.replace("،", ",").split("-") if p.strip()]
    return parts


def _roots_equivalent(a: str, b: str) -> bool:
    """Same three radicals (hyphen form), ignoring trivial spacing."""
    return _split_root_letters(a) == _split_root_letters(b)


def l8_root_likely_surface_hollow_error(current: Optional[str], canonical: str) -> bool:
    """
    True if L8 root shares ف&ل with canonical but middle differs (e.g. ص-ي-م vs ص-و-م).
    """
    if not current or not canonical:
        return False
    ca = _split_root_letters(canonical)
    cu = _split_root_letters(current)
    if len(ca) != 3 or len(cu) != 3:
        return False
    if ca[0] != cu[0] or ca[2] != cu[2]:
        return False
    if ca[1] == cu[1]:
        return False
    # Middle in wrong analysis often ي / ئ / ء from surface hamza
    if cu[1] in ("\u064a", "\u0649", "\u0626", "\u0621", "\u0624"):
        return True
    return False


def resolve_hollow_ism_fail_root(stem: str, current_root: Optional[str]) -> Optional[str]:
    """
    Priority: keep linguistically correct triliteral root; override wrong L8 surface analysis
    for known hollow participles; for unknown shapes keep L8 root.
    """
    s = normalize_stem_key(stem)
    lex = KNOWN_HOLLOW_ISM_STEM_TO_ROOT.get(s)
    if lex:
        if not current_root:
            return lex
        if _roots_equivalent(current_root, lex):
            return current_root
        if l8_root_likely_surface_hollow_error(current_root, lex):
            return lex
        # Canonical lexicon wins for listed stems (documented inventory)
        return lex
    return current_root


def apply_hollow_root_to_word_state_entry(st: dict) -> None:
    """
    Patch st['root'] after L8 when stem is hollow ISM_FAIL; set hollow_ism_fail flag.
    Does not downgrade a root that already matches the canonical lexicon form.
    """
    stem = st.get("stem") or ""
    if not is_hollow_ism_fail_candidate(stem):
        st["hollow_ism_fail"] = False
        return
    st["hollow_ism_fail"] = True
    current = st.get("root")
    raw_l8 = st.get("raw_l8_root")
    resolved = resolve_hollow_ism_fail_root(stem, current if isinstance(current, str) else None)
    if resolved and isinstance(resolved, str):
        st["root"] = resolved
        st["canonical_root"] = resolved
        # Triradical hyphen root counts as present
        letters = [x for x in resolved.replace("-", "") if x.strip()]
        st["root_confirmed"] = len(letters) >= 2
        if raw_l8 is not None and isinstance(raw_l8, str) and raw_l8.strip() and resolved.strip() != raw_l8.strip():
            st["root_correction_source"] = "hollow_ism_fail"
        elif raw_l8 is None and current != resolved:
            st["root_correction_source"] = "hollow_ism_fail"
