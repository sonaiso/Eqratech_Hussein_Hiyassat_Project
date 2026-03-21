# -*- coding: utf-8 -*-
"""
Canonical derivational stem / wazn inference for ARABIC_WORD_STATE.

Generalized pattern rules only (no sentence-specific strings). Used when L9 fails to
attach a template to long inflected surfaces that still share a derivational stem
with dictionary rows.
"""

from __future__ import annotations

import re
from typing import Any, Dict, Optional, Tuple

from .hollow_ism_fail import is_hollow_ism_fail_candidate, normalize_stem_key

# Stems (no affixes) that are Form-I active participle / مُفْعِل in Quranic inventory (extend conservatively).
KNOWN_MUFTAL_STEM_TO_WAZN: Dict[str, str] = {
    "مسلم": "مُفْعِل",
    "مؤمن": "مُفْعِل",
}

_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")
# Hamza on alif seat (ئ) in hollow participle middle
_RE_HOLLOW_ISM_SHAPE = re.compile(r"^.\u0627\u0626.$")
# Form IV prefix: أ + optional diacritic on hamza, then rest
_RE_FORM4_VERB = re.compile(r"^\u0623\u064e?(.+)$")


def _strip_diacritics(s: str) -> str:
    if not s or not isinstance(s, str):
        return ""
    return _DIACRITICS.sub("", s.strip()).replace("\u0651", "").strip()


def _root_letters_triplets(root_hyphen: Optional[str]) -> Tuple[str, str, str]:
    if not root_hyphen or not isinstance(root_hyphen, str):
        return ("", "", "")
    parts = [p.strip() for p in root_hyphen.replace("،", ",").split("-") if p.strip()]
    if len(parts) != 3:
        return ("", "", "")
    return (parts[0], parts[1], parts[2])


def is_geminate_trilateral_root(root_hyphen: Optional[str]) -> bool:
    """True if root is C-C-C with identical second and third radicals (e.g. ع-د-د)."""
    a, b, c = _root_letters_triplets(root_hyphen)
    return bool(a and b and c and b == c)


def canonical_stem_for_token(surface: str, kind: str) -> str:
    """
    Canonical stem for derivational morphology: nominal path uses derivational_stem;
    finite verbs may strip Form-I-style augment أَ to expose the stem (e.g. أَعَدَّ → عَدَّ).
    """
    from .arabic_word_state import derivational_stem

    k = (kind or "").strip().lower()
    surf = (surface or "").strip()
    if k in ("verb", "فعل"):
        m = _RE_FORM4_VERB.match(surf)
        if m:
            rest = m.group(1).strip()
            if rest and "\u0651" in rest:  # shadda on stem — typical doubled / Form IV
                return rest
    return derivational_stem(surf)


def infer_canonical_derivational_wazn(
    st: Dict[str, Any],
    kind: str,
) -> Tuple[Optional[str], str]:
    """
    Returns (canonical_wazn_or_none, inference_rule_or_empty).
    Does not override a non-empty L9 template unless rule is higher priority for known bad patterns.
    """
    from .arabic_word_state import derivational_stem

    raw_stem = (st.get("canonical_stem") or st.get("stem") or "").strip()
    stem_key = normalize_stem_key(raw_stem or derivational_stem(st.get("surface") or ""))
    root = (st.get("root") or st.get("canonical_root") or "") or ""
    if isinstance(root, dict):
        root = str(root.get("formatted") or "")
    k = (kind or "").strip().lower()

    # 1) Hollow active participle stem → فَاعِل
    if is_hollow_ism_fail_candidate(stem_key) or (stem_key and _RE_HOLLOW_ISM_SHAPE.match(stem_key)):
        return ("فَاعِل", "inferred_hollow_ism_fail_faal")

    # 1b) Lexicon: مُفْعِل stems (مسلم، مؤمن) when L9 left wazn empty on long surfaces
    sk_lex = normalize_stem_key(stem_key)
    if sk_lex in KNOWN_MUFTAL_STEM_TO_WAZN and k in (
        "noun", "اسم", "name", "proper_noun", "proper noun", "علم", "",
    ):
        return (KNOWN_MUFTAL_STEM_TO_WAZN[sk_lex], "inferred_muftal_lexicon")

    # 2) Geminate root + verb family → فَعَّ (display pattern for stem like عَدَّ)
    if k in ("verb", "فعل") and is_geminate_trilateral_root(root):
        return ("فَعَّ", "inferred_geminate_verb_facc")

    # 3) Form VI/VIII-style stem مت… (e.g. متصدق) — مُتَفَعِّل
    sk = stem_key
    if sk.startswith("مت") and len(sk) >= 5:
        return ("مُتَفَعِّل", "inferred_mutafa33al_stem")

    return (None, "")


def apply_canonical_derivation_to_word_state_entry(st: Dict[str, Any], kind: str) -> None:
    """
    Set canonical_stem, canonical_root, canonical_wazn; refresh wazn_template when missing
    or when L9 produced a known-bad geminate display (فَعَلَّ → فَعَّ).
    """
    surface = (st.get("surface") or "").strip()
    st["canonical_stem"] = canonical_stem_for_token(surface, kind)
    st["canonical_root"] = st.get("root")
    existing_tpl = (st.get("wazn_template") or "").strip()
    existing_ww = (st.get("word_wazn") or "").strip()
    cw, rule = infer_canonical_derivational_wazn({**st, "canonical_stem": st["canonical_stem"]}, kind)

    bad_geminate_display = bool(
        existing_tpl
        and is_geminate_trilateral_root(st.get("root"))
        and _l9_template_looks_like_bad_geminate_spelling(existing_tpl)
    )

    if cw:
        st["canonical_wazn"] = cw
        if not _wazn_nonempty(existing_tpl, existing_ww) or bad_geminate_display:
            st["wazn_template"] = cw
            st["word_wazn"] = cw
            st["wazn_confirmed"] = True
        if rule:
            st.setdefault("wazn_inference_rule", rule)
    else:
        # Mirror L9 into canonical when no inference
        wz = existing_ww or existing_tpl
        if wz:
            st["canonical_wazn"] = wz
        else:
            st["canonical_wazn"] = None

    # Keep root alias
    if st.get("root"):
        st["canonical_root"] = st["root"]


def _l9_template_looks_like_bad_geminate_spelling(tpl: str) -> bool:
    """L9 sometimes surfaces geminate verbs as فَعَلَّ instead of stem-level فَعَّ."""
    if not tpl or not isinstance(tpl, str):
        return False
    if "\u0644\u0651" in tpl or "\u0651\u0644" in tpl:
        return True
    if "فَعَلَّ" in tpl or "فعَلَّ" in tpl:
        return True
    nd = _DIACRITICS.sub("", tpl).replace("\u0651", "")
    if "فعلل" in nd:
        return True
    # Over-expanded quadriliteral-style display for triliteral geminate
    if len(nd) >= 5 and nd.startswith("فعل") and nd.endswith("ل"):
        return True
    return False


def _wazn_nonempty(tpl: str, ww: str) -> bool:
    for w in (tpl, ww):
        if w and isinstance(w, str) and w.strip() and w.strip() not in ("—", "-"):
            s = _DIACRITICS.sub("", w.strip()).strip()
            if s:
                return True
    return False
