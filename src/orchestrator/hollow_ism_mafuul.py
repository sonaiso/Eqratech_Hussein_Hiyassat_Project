# -*- coding: utf-8 -*-
"""
Hollow-verb passive participle (اسم المفعول الأجوف) — root recovery and classification support.

اسم المفعول من الأجوف يُرَدّ إلى أصل الفعل لا إلى مدّ الحرف الظاهر فقط:
مقول = ق-و-ل ، مبيع = ب-ي-ع ، مخوف = خ-و-ف.
الواو/الياء في هذا النمط تعكس أصل الأجوف (واوي / يائي) وليست عين جذر مستقلة من السطح فقط.

If the word matches hollow passive-participle surface (مَفْعُول / مَفْعِيل types after affix strip),
classify as ISM_MAFUUL(hollow), recover the triliteral root from the verbal origin / lexicon.
Confirmed correct roots in arabic_word_state must not be replaced by surface-wrong middles
(e.g. ق-ي-ل for مقول, ب-و-ع for مبيع).
"""

from __future__ import annotations

import re
from typing import Optional

from .hollow_ism_fail import _roots_equivalent, _split_root_letters, normalize_stem_key

# Documented hollow passive-participle stems (after derivational_stem) → canonical root.
KNOWN_HOLLOW_ISM_MAFUUL_STEM_TO_ROOT: dict[str, str] = {
    "مقول": "ق-و-ل",
    "مصون": "ص-و-ن",
    "مخوف": "خ-و-ف",
    "مبيع": "ب-ي-ع",
    "مهيب": "ه-ي-ب",
}

# م + radical + و + radical (hollow wāwī passive participle surface)
_RE_MAFUUL_HOLLOW_WAWI = re.compile(r"^.\u0648.$")

# م + radical + ي + radical (hollow yāʾī passive participle surface)
_RE_MAFUUL_HOLLOW_YAI = re.compile(r"^.\u064a.$")


def _stem_body_after_meem(stem: str) -> str:
    """Stem must start with م; return remainder for pattern match (3 chars → م + 3 = 4)."""
    s = normalize_stem_key(stem)
    if not s.startswith("\u0645") or len(s) != 4:
        return ""
    return s[1:]


def matches_hollow_ism_mafuul_shape(stem: str) -> bool:
    """مفوعل / مفيع hollow surface: 4 letters, م + C + (و|ي) + C."""
    body = _stem_body_after_meem(stem)
    if len(body) != 3:
        return False
    return bool(_RE_MAFUUL_HOLLOW_WAWI.match(body) or _RE_MAFUUL_HOLLOW_YAI.match(body))


def is_hollow_ism_mafuul_candidate(stem: str) -> bool:
    """Listed stem or generic مَفْعُول/مَفْعِيل hollow shape."""
    s = normalize_stem_key(stem)
    if not s:
        return False
    if s in KNOWN_HOLLOW_ISM_MAFUUL_STEM_TO_ROOT:
        return True
    return matches_hollow_ism_mafuul_shape(stem)


def is_lexicon_listed_hollow_mafuul_stem(stem: str) -> bool:
    return normalize_stem_key(stem) in KNOWN_HOLLOW_ISM_MAFUUL_STEM_TO_ROOT


def l8_root_likely_surface_mafuul_hollow_error(current: Optional[str], canonical: str) -> bool:
    """
    True if L8 root shares ف&ل with canonical but middle differs by و/ي confusion
    (e.g. ق-ي-ل vs ق-و-ل, ب-و-ع vs ب-ي-ع).
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
    mids = {ca[1], cu[1]}
    return mids <= {"\u0648", "\u064a", "\u0649"}


def resolve_hollow_ism_mafuul_root(stem: str, current_root: Optional[str]) -> Optional[str]:
    """Override wrong L8 middles for known hollow اسم مفعول stems; else keep current."""
    s = normalize_stem_key(stem)
    lex = KNOWN_HOLLOW_ISM_MAFUUL_STEM_TO_ROOT.get(s)
    if lex:
        if not current_root:
            return lex
        if _roots_equivalent(current_root, lex):
            return current_root
        if l8_root_likely_surface_mafuul_hollow_error(current_root, lex):
            return lex
        return lex
    return current_root


def apply_hollow_mafuul_root_to_word_state_entry(st: dict) -> None:
    """Patch st['root'] after L8 for hollow ISM_MAFUUL stems; set hollow_ism_mafuul flag."""
    stem = st.get("stem") or ""
    if not is_hollow_ism_mafuul_candidate(stem):
        st.setdefault("hollow_ism_mafuul", False)
        return
    st["hollow_ism_mafuul"] = True
    current = st.get("root")
    raw_l8 = st.get("raw_l8_root")
    resolved = resolve_hollow_ism_mafuul_root(stem, current if isinstance(current, str) else None)
    if resolved and isinstance(resolved, str):
        st["root"] = resolved
        st["canonical_root"] = resolved
        letters = [x for x in resolved.replace("-", "") if x.strip()]
        st["root_confirmed"] = len(letters) >= 2
        if raw_l8 is not None and isinstance(raw_l8, str) and raw_l8.strip() and resolved.strip() != raw_l8.strip():
            st["root_correction_source"] = "hollow_ism_mafuul"
        elif raw_l8 is None and current != resolved:
            st["root_correction_source"] = "hollow_ism_mafuul"
