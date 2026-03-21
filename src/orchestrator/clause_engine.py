# -*- coding: utf-8 -*-
"""
CLAUSE_ENGINE — Stage 16.
Pass 1: conditional decomposition (shart → feil → jawab).
Pass 2 (additive): hal clause (جملة حالية), tamyiz phrase (تمييز عدد), sila (صلة موصول).
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Set, Tuple

from .l14_jamid_mushtaq import has_strong_true_verb_evidence

_WAW = "\u0648"  # و

# Pass 2 — relative / mawsul surfaces (diacritic-tolerant)
_MAWSUL_STRIP_RE = re.compile(r"[\u064b-\u065f\u0670]")

# Tamyiz T1 — aligned with L12 `_NUMBER_LEXEMES` (number → noun)
_NUMBER_LEXEMES_FOR_TAMYIZ = frozenset({
    "واحد", "اثنان", "اثنين", "ثلاثة", "ثلاث", "أربعة", "أربع", "خمسة", "خمس",
    "ستة", "ست", "سبعة", "سبع", "ثمانية", "ثمان", "تسعة", "تسع", "عشرة", "عشر",
    "عشرون", "عشرين", "مئة", "مائة", "ألف",
})


def _strip_diacritics(s: str) -> str:
    if not s:
        return ""
    return _MAWSUL_STRIP_RE.sub("", s)


def _normalize_morph(s: str) -> str:
    t = _strip_diacritics(s or "").replace("\u0623", "\u0627").replace("\u0625", "\u0627").replace("\u0622", "\u0627")
    return t.strip()


def _is_ism_mawsul_surface(surface: str) -> bool:
    """Known اسم موصول / موصول shapes (conservative)."""
    n = _normalize_morph(surface)
    if not n:
        return False
    if n in ("ما", "من", "مهما"):
        return True
    if n.startswith("اي") or n.startswith("\u0623\u064a"):  # أيّ
        return True
    if "الذين" in n or n.startswith("الذين"):
        return True
    if "اللواتي" in n or "اللاتي" in n:
        return True
    if "الذي" in n or n.endswith("الذي"):
        return True
    if "التي" in n and len(n) <= 6:
        return True
    return False


def _l8b_profiles_map(lo: dict) -> Dict[str, dict]:
    l8b_tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    return {
        str(p.get("token_id")): p
        for p in l8b_tr.get("verb_governance_profiles", [])
        if p.get("token_id") is not None
    }


def _l5_words(lo: dict) -> List[dict]:
    l5_tr = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    return l5_tr.get("words") or []


def _is_finite_verb_at(
    idx: int,
    tokens: List[str],
    l8b_profiles: Dict[str, dict],
    l5_words: List[dict],
    lo: dict,
) -> bool:
    if idx < 0 or idx >= len(tokens):
        return False
    sid = str(idx)
    if sid in l8b_profiles:
        return True
    if idx < len(l5_words):
        w = l5_words[idx] if isinstance(l5_words[idx], dict) else {}
        k = (w.get("kind") or "").strip().lower()
        if k in ("verb", "فعل"):
            return True
    return has_strong_true_verb_evidence(sid, tokens[idx] or "", lo)


def _is_present_verb_surface(surface: str) -> bool:
    """Mudāriʿ-style onset (heuristic; not imperfect detection)."""
    s = _strip_diacritics(surface or "")
    if not s:
        return False
    first = s[0]
    # ي ت ن أ آ ا for أَفْعَلَ / افتعل
    if first in (
        "\u064a",  # ي
        "\u062a",  # ت
        "\u0646",  # ن
        "\u0623",  # أ
        "\u0622",  # آ
        "\u0627",  # ا
    ):
        return True
    return False


def _is_present_verb_at(
    idx: int,
    tokens: List[str],
    l8b_profiles: Dict[str, dict],
    l5_words: List[dict],
    lo: dict,
) -> bool:
    if not _is_finite_verb_at(idx, tokens, l8b_profiles, l5_words, lo):
        return False
    p = l8b_profiles.get(str(idx)) or {}
    tf = (p.get("tense_family") or "").strip().lower()
    if tf == "present":
        return True
    surf = tokens[idx] if idx < len(tokens) else ""
    return _is_present_verb_surface(surf)


def _find_parent_clause_id_for_span(clauses: List[dict], s: int, e: int) -> str:
    """Smallest containing clause span wins (feil_shart inside main)."""
    best: Optional[Tuple[int, str]] = None
    for c in clauses:
        try:
            cs = int(c.get("start_token_id"))
            ce = int(c.get("end_token_id"))
        except (TypeError, ValueError):
            continue
        if cs <= s and e <= ce:
            span = ce - cs
            cid = str(c.get("clause_id") or "")
            if best is None or span < best[0]:
                best = (span, cid)
    if best:
        return best[1]
    for c in clauses:
        if (c.get("clause_type") or "").strip() == "main":
            return str(c.get("clause_id") or "main_0")
    return "main_0"


def _dependency_links(lo: dict) -> list:
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    return dsb.get("dependency_links") or []


def _subj_token_for_matrix_verb(lo: dict, verb_idx: int) -> Optional[str]:
    sid = str(verb_idx)
    for lk in _dependency_links(lo):
        if (lk.get("head_id") == sid) and ((lk.get("relation") or "").strip() == "SUBJ"):
            return str(lk.get("dependent_id")) if lk.get("dependent_id") is not None else None
    return None


def _l4_word_hal_hint(lo: dict, idx: int) -> bool:
    """True if L4 marks connective as حال-style (best-effort)."""
    l4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    words = l4.get("words") or []
    if idx >= len(words):
        return False
    w = words[idx] if isinstance(words[idx], dict) else {}
    op = (w.get("operator") or {}) if isinstance(w.get("operator"), dict) else {}
    note = (op.get("note") or op.get("purpose") or "").strip()
    if "حال" in note:
        return True
    cg = (w.get("connective_group") or "").strip().lower()
    return cg in ("hal", "حال")


def _detect_hal_clauses(
    tokens: List[str],
    lo: dict,
    existing_clauses: List[dict],
) -> List[dict]:
    """
    جملة حالية: واو حال + مضارع، أو وَهُوَ + مضارع (token merged);
    implicit مضارع after فاعل/مفعول؛ حال مفرد (تنوين فتح) بين فعل الشرط وجوابه.
    candidate-only; confidence < 0.85.
    """
    if len(tokens) < 2:
        return []
    l8b = _l8b_profiles_map(lo)
    l5w = _l5_words(lo)
    out: List[dict] = []
    hal_n = 0
    n = len(tokens)

    def emit_hal(
        start_t: int,
        end_t: int,
        head_v: int,
        marker: Optional[str],
        rule: str,
        conf: float,
        hal_subj: Optional[str],
        parent_override: Optional[str] = None,
    ) -> None:
        nonlocal hal_n
        parent = parent_override or _find_parent_clause_id_for_span(existing_clauses + out, start_t, end_t)
        out.append({
            "clause_id": f"hal_clause_{hal_n}",
            "clause_type": "hal_clause",
            "arabic_label": "جملة حالية",
            "start_token_id": str(start_t),
            "end_token_id": str(end_t),
            "head_token_id": str(head_v),
            "parent_clause_id": parent,
            "hal_marker": marker,
            "hal_subject_ref": hal_subj,
            "confidence": conf,
            "rule": rule,
            "limitation": "hal_clause_detection_approximate",
            "status": "candidate",
        })
        hal_n += 1

    main_verb_idx = 0
    for idx in range(n):
        if _is_finite_verb_at(idx, tokens, l8b, l5w, lo):
            main_verb_idx = idx
            break
    subj_guess = _subj_token_for_matrix_verb(lo, main_verb_idx)

    i = 0
    while i < n - 1:
        surf = (tokens[i] or "").strip()
        # Separate و
        if surf in ("و", "وَ"):
            if i + 1 < n and _is_present_verb_at(i + 1, tokens, l8b, l5w, lo):
                conf = 0.78 if _l4_word_hal_hint(lo, i) else 0.72
                emit_hal(
                    i, i + 1, i + 1, "و",
                    "waw_hal_present_verb",
                    conf,
                    subj_guess,
                )
                i = i + 2
                continue
        # Merged وَهُوَ-style only (reject وَجَاءَ… and وَالْ…)
        if surf.startswith(_WAW) and len(surf) > 1:
            nm = _normalize_morph(surf)
            if nm.startswith("وال"):
                i += 1
                continue
            if len(nm) < 2 or nm[1] != "\u0647":  # وَهُوَ / وَهُمْ … not وَجَاءُوا
                i += 1
                continue
            if i + 1 < n and _is_present_verb_at(i + 1, tokens, l8b, l5w, lo):
                conf = 0.78 if _l4_word_hal_hint(lo, i) else 0.72
                emit_hal(
                    i, i + 1, i + 1, "و",
                    "waw_hal_present_verb",
                    conf,
                    subj_guess,
                )
                i = i + 2
                continue
        i += 1

    # Implicit hal: subject/object immediately before present verb (no و between)
    for j in range(1, n):
        if not _is_present_verb_at(j, tokens, l8b, l5w, lo):
            continue
        if j == main_verb_idx:
            continue
        prev_tok = tokens[j - 1] or ""
        if "\u064b" in prev_tok:
            continue
        prev_links = any(
            str(lk.get("head_id")) == str(main_verb_idx)
            and str(lk.get("dependent_id")) == str(j - 1)
            and (lk.get("relation") or "").strip() in ("SUBJ", "OBJ")
            for lk in _dependency_links(lo)
        )
        if not prev_links:
            continue
        if j >= 2 and (tokens[j - 2] or "").strip() in ("و", "وَ"):
            continue
        emit_hal(
            j, j, j, None,
            "implicit_hal_present_verb",
            0.65,
            subj_guess,
        )
        break

    # مضارع after منصوب/ظرف تنوين (host) — e.g. عِشَاءً يَبْكُونَ
    for j in range(1, n):
        if not _is_present_verb_at(j, tokens, l8b, l5w, lo):
            continue
        if j <= main_verb_idx:
            continue
        prev_tok = tokens[j - 1] or ""
        if "\u064b" not in prev_tok:
            continue
        if _is_finite_verb_at(j - 1, tokens, l8b, l5w, lo):
            continue
        emit_hal(
            j, j, j, None,
            "hal_present_after_accusative_host",
            0.70,
            subj_guess,
        )
        break

    # Mufrad hal (تنوين فتح) after feil matrix verb and before jawab matrix verb — parent = feil_shart
    feil = next((c for c in existing_clauses if c.get("clause_type") == "feil_shart"), None)
    jawab = next((c for c in existing_clauses if c.get("clause_type") == "jawab_shart"), None)
    if feil is not None and jawab is not None:
        try:
            feil_head_i = int(feil.get("head_token_id") or feil.get("start_token_id"))
            js = int(jawab["start_token_id"])
            je = int(jawab["end_token_id"])
        except (TypeError, ValueError):
            feil_head_i = 0
            js, je = 0, n - 1
        jaw_matrix_i = _first_verb(js, je, l8b, l5w)
        if jaw_matrix_i is None:
            for k in range(js, min(je, n - 1) + 1):
                if _is_finite_verb_at(k, tokens, l8b, l5w, lo):
                    jaw_matrix_i = k
                    break
        if jaw_matrix_i is None:
            jaw_matrix_i = je
        for hi in range(feil_head_i + 1, min(jaw_matrix_i, n)):
            surf = tokens[hi] or ""
            if "\u064b" not in surf:
                continue
            if _is_finite_verb_at(hi, tokens, l8b, l5w, lo):
                continue
            emit_hal(
                hi, hi, hi, None,
                "mufrad_hal_accusative_tanween",
                0.70,
                subj_guess,
                parent_override=str(feil.get("clause_id") or "feil_shart_0"),
            )
            break

    return out


def _norm_number_lexeme_surface(surface: str) -> str:
    n = _normalize_morph(surface or "")
    if n.startswith("ال"):
        n = n[2:]
    return n


def _l5_family_upper(w: dict) -> str:
    if not isinstance(w, dict):
        return ""
    return (w.get("family") or w.get("kind") or "").strip().upper()


def _detect_tamyiz_phrases(
    tokens: List[str],
    lo: dict,
    existing_clauses: List[dict],
) -> List[dict]:
    """تمييز عدد from L12 tamyiz_relation or number lexeme + following noun."""
    out: List[dict] = []
    l12 = (lo.get("L12_GENDER_NUMBER") or {}).get("transformation_result") or {}
    rows = l12.get("token_features") or []
    l5w = _l5_words(lo)
    seen_pairs: Set[Tuple[int, int]] = set()
    tidx = 0
    for row in rows:
        if not isinstance(row, dict):
            continue
        rel = row.get("tamyiz_relation")
        if rel is None or rel == "":
            continue
        try:
            num_i = int(row.get("token_id"))
            noun_i = int(str(rel).strip())
        except (TypeError, ValueError):
            continue
        seen_pairs.add((num_i, noun_i))
        parent = _find_parent_clause_id_for_span(existing_clauses + out, min(num_i, noun_i), max(num_i, noun_i))
        out.append({
            "clause_id": f"tamyiz_{tidx}",
            "clause_type": "tamyiz_phrase",
            "arabic_label": "تمييز العدد",
            "start_token_id": str(num_i),
            "end_token_id": str(noun_i),
            "head_token_id": str(num_i),
            "parent_clause_id": parent,
            "tamyiz_type": "adad",
            "tamyiz_noun_token_id": str(noun_i),
            "confidence": 0.80,
            "rule": "l12_tamyiz_relation",
            "limitation": None,
            "status": "candidate",
        })
        tidx += 1

    # Number lexeme + following noun (Pass 2 surface path)
    for i in range(len(tokens) - 1):
        nlex = _norm_number_lexeme_surface(tokens[i])
        if nlex not in _NUMBER_LEXEMES_FOR_TAMYIZ:
            continue
        if (i, i + 1) in seen_pairs:
            continue
        wnext = l5w[i + 1] if i + 1 < len(l5w) else {}
        fam = _l5_family_upper(wnext)
        kind = (wnext.get("kind") or "").strip().lower()
        if "NOUN" not in fam and kind != "noun":
            continue
        parent = _find_parent_clause_id_for_span(existing_clauses + out, i, i + 1)
        out.append({
            "clause_id": f"tamyiz_{tidx}",
            "clause_type": "tamyiz_phrase",
            "arabic_label": "تمييز العدد",
            "start_token_id": str(i),
            "end_token_id": str(i + 1),
            "head_token_id": str(i),
            "parent_clause_id": parent,
            "tamyiz_type": "adad",
            "tamyiz_noun_token_id": str(i + 1),
            "confidence": 0.80,
            "rule": "number_lexeme_tamyiz_detection",
            "limitation": None,
            "status": "candidate",
        })
        tidx += 1
        seen_pairs.add((i, i + 1))

    return out


def _detect_sila_clauses(
    tokens: List[str],
    lo: dict,
    existing_clauses: List[dict],
) -> List[dict]:
    """اسم موصول + صلة (finite verb within window)."""
    l8b = _l8b_profiles_map(lo)
    l5w = _l5_words(lo)
    out: List[dict] = []
    sila_n = 0
    n = len(tokens)

    for i, surf in enumerate(tokens):
        if not _is_ism_mawsul_surface(surf):
            continue
        vidx: Optional[int] = None
        for j in range(i + 1, min(n, i + 6)):
            if _is_finite_verb_at(j, tokens, l8b, l5w, lo):
                vidx = j
                break
        # Fallback: single-token صلة after مَنْ/مَا when L5/L8B mis-tags the verb
        if vidx is None and i + 1 < n:
            nm_m = _normalize_morph(tokens[i] or "")
            if nm_m in ("من", "ما"):
                cand = tokens[i + 1] or ""
                if not _is_ism_mawsul_surface(cand) and len(_strip_diacritics(cand)) >= 2:
                    vidx = i + 1
        if vidx is None:
            continue
        parent_m = _find_parent_clause_id_for_span(existing_clauses + out, i, i)
        parent_s = _find_parent_clause_id_for_span(existing_clauses + out, i + 1, vidx)
        mid = f"mawsul_{sila_n}"
        sid = f"sila_{sila_n}"
        out.append({
            "clause_id": mid,
            "clause_type": "ism_mawsul",
            "arabic_label": "اسم موصول",
            "start_token_id": str(i),
            "end_token_id": str(i),
            "head_token_id": str(i),
            "parent_clause_id": parent_m,
            "confidence": 0.88,
            "rule": "known_ism_mawsul_surface",
            "limitation": None,
            "status": "candidate",
        })
        out.append({
            "clause_id": sid,
            "clause_type": "sila_mawsul",
            "arabic_label": "صلة الموصول",
            "start_token_id": str(i + 1),
            "end_token_id": str(vidx),
            "head_token_id": str(vidx),
            "parent_clause_id": mid,
            "antecedent_token_id": str(i),
            "i3rab_note": "لا محل لها من الإعراب",
            "confidence": 0.82,
            "rule": "clause_after_ism_mawsul",
            "limitation": None,
            "status": "candidate",
        })
        sila_n += 1

    return out


def _apply_clause_engine_pass2(lo: dict, out: dict, tokens: List[str]) -> None:
    """Append Pass 2 clauses; update flags and clause_count."""
    clauses = list(out.get("clause_analysis") or [])
    hal = _detect_hal_clauses(tokens, lo, clauses)
    tam = _detect_tamyiz_phrases(tokens, lo, clauses + hal)
    sil = _detect_sila_clauses(tokens, lo, clauses + hal + tam)
    merged = clauses + hal + tam + sil
    out["clause_analysis"] = merged
    out["clauses"] = merged
    out["clause_count"] = len(merged)
    out["hal_detected"] = bool(hal)
    out["tamyiz_detected"] = bool(tam)
    out["sila_detected"] = bool(sil)
    amb = list(out.get("ambiguity_log") or [])
    out["ambiguity_log"] = amb


def _is_conditional_trigger(word: dict) -> bool:
    """True only for real conditional triggers; do not treat إنَّ/أنَّ emphasis as conditional."""
    if not isinstance(word, dict):
        return False
    op = (word.get("operator") or {}) if isinstance(word.get("operator"), dict) else {}
    sig = (op.get("effect_signature") or "").strip()
    cg = (word.get("connective_group") or "").strip().lower()
    if sig:
        return sig == "COND"
    return cg == "conditional"


def _is_jawab_trigger(word: dict) -> bool:
    """Conditional answer particle after a real shart trigger."""
    if not isinstance(word, dict):
        return False
    op = (word.get("operator") or {}) if isinstance(word.get("operator"), dict) else {}
    sig = (op.get("effect_signature") or "").strip()
    cg = (word.get("connective_group") or "").strip().lower()
    return sig == "JAZM" or (not sig and cg == "conditional")


def _inna_name_dependent_upper_bound(links: list) -> Optional[int]:
    """Max dependent index of INNA_NAME links (اسم إن scope anchor)."""
    mx: Optional[int] = None
    for lk in links:
        if (lk.get("relation") or "").strip() != "INNA_NAME":
            continue
        d = lk.get("dependent_id")
        try:
            di = int(d)
        except (TypeError, ValueError):
            continue
        mx = di if mx is None else max(mx, di)
    return mx


def _verbs_with_subj_and_obj(
    tokens: list,
    lo: dict,
    links: list,
) -> List[int]:
    """Indices where Stage 15 shows SUBJ+OBJ and L14/L8B says strong finite verb."""
    out: List[int] = []
    for i, surface in enumerate(tokens):
        if not has_strong_true_verb_evidence(str(i), surface or "", lo):
            continue
        sid = str(i)
        has_subj = any(
            (lk.get("head_id") == sid and (lk.get("relation") or "").strip() == "SUBJ")
            for lk in links
        )
        has_obj = any(
            (lk.get("head_id") == sid and (lk.get("relation") or "").strip() == "OBJ")
            for lk in links
        )
        if has_subj and has_obj:
            out.append(i)
    return out


def _verbal_tail_clause_regions(
    tokens: list,
    lo: dict,
    links: list,
) -> List[Dict[str, Any]]:
    """
    When إنّ/أنّ opens the sentence (INNA_NAME), a later finite clause with SUBJ+OBJ
    in Stage 15 is packaged as an embedded verbal clause region (e.g. خبر إن predicate).
    """
    if not tokens:
        return []
    inna_bound = _inna_name_dependent_upper_bound(links)
    if inna_bound is None:
        return []

    verbs = _verbs_with_subj_and_obj(tokens, lo, links)
    if not verbs:
        return []

    # Prefer the rightmost strong verbal core after اسم إن anchor (not sentence-initial lone verb).
    tail_verbs = [v for v in verbs if v > inna_bound]
    if not tail_verbs:
        return []

    v = max(tail_verbs)
    n = len(tokens)
    return [{
        "clause_id": "verbal_tail_0",
        "clause_type": "verbal_embedded",
        "arabic_label": "جملة فعلية (ذيل خبري)",
        "start_token_id": str(v),
        "end_token_id": str(n - 1),
        "head_token_id": str(v),
        "parent_clause_id": "main_0",
        "confidence": 0.75,
        "rule": "strong_verb_subj_obj_after_inna_name",
        "limitation": None,
    }]


def build_clause_output(lo: dict) -> dict:
    """
    Stage 16 Clause Engine — Pass 1 + Pass 2 (additive).
    Pass 1: shart_particle → feil_shart → jawab_particle → jawab_shart
    Pass 2: hal_clause, tamyiz_phrase, ism_mawsul + sila_mawsul (appended; Pass 1 rows unchanged).
    """
    try:
        tokens = _get_tokens(lo)
        l4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
        l4_words = l4.get("words", [])
        l8b_tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
        l8b_profiles = {
            str(p.get("token_id")): p
            for p in l8b_tr.get("verb_governance_profiles", [])
            if p.get("token_id") is not None
        }
        l5_tr = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
        l5_words = l5_tr.get("words", [])
        l10b_tr = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
        l10b_nodes = l10b_tr.get("dependency_nodes", [])

        # Step 1: Find shart_particle (COND operator)
        shart_idx = None
        for i, w in enumerate(l4_words):
            if _is_conditional_trigger(w):
                shart_idx = i
                break

        if shart_idx is None:
            out = _single_main_clause(len(tokens))
            links = _dependency_links(lo)
            out["verbal_clause_regions"] = _verbal_tail_clause_regions(tokens, lo, links)
            _apply_clause_engine_pass2(lo, out, tokens)
            return out

        # Step 2: Find jawab_particle (JAZM operator after shart)
        jawab_idx = None
        for i in range(shart_idx + 1, len(l4_words)):
            w = l4_words[i] if isinstance(l4_words[i], dict) else {}
            if _is_jawab_trigger(w):
                jawab_idx = i
                break
        if jawab_idx is None:
            for node in l10b_nodes:
                if not isinstance(node, dict):
                    continue
                tid = node.get("token_id")
                if tid is None:
                    continue
                idx = int(tid) if isinstance(tid, str) else tid
                if idx > shart_idx and (node.get("connective_group") or "").strip().lower() == "conditional":
                    jawab_idx = idx
                    break

        # Step 3: Find feil_shart head
        feil_end_max = (jawab_idx - 1) if jawab_idx is not None else (len(tokens) - 1)
        feil_head = _first_verb(shart_idx + 1, feil_end_max, l8b_profiles, l5_words)
        # Single conditional: limit feil_shart to verb span so rest is jawab_shart
        if jawab_idx is None and feil_head is not None:
            feil_end = feil_head
        else:
            feil_end = feil_end_max

        # Step 4: Find jawab_shart head
        if jawab_idx is not None:
            jaw_head = _first_verb(jawab_idx + 1, len(tokens) - 1, l8b_profiles, l5_words)
        else:
            jaw_head = None

        clauses = []
        clause_count = 0

        # Emit shart_particle
        clauses.append({
            "clause_id": "shart_particle_0",
            "clause_type": "conditional_particle",
            "arabic_label": "أداة الشرط",
            "start_token_id": str(shart_idx),
            "end_token_id": str(shart_idx),
            "head_token_id": str(shart_idx),
            "parent_clause_id": None,
            "confidence": 0.9,
            "rule": "L4_COND_operator",
            "limitation": None,
        })
        clause_count += 1

        # Emit feil_shart
        feil_head_id = str(feil_head) if feil_head is not None else str(shart_idx + 1)
        feil_end_id = str(feil_end)
        clauses.append({
            "clause_id": "feil_shart_0",
            "clause_type": "feil_shart",
            "arabic_label": "فعل الشرط",
            "start_token_id": str(shart_idx + 1),
            "end_token_id": feil_end_id,
            "head_token_id": feil_head_id,
            "parent_clause_id": "shart_particle_0",
            "confidence": 0.85 if feil_head is not None else 0.5,
            "rule": "first_verb_after_shart_particle" if feil_head is not None else "no_verb_found_fallback",
            "limitation": None if feil_head is not None else "feil_shart verb not found within span",
        })
        clause_count += 1

        if jawab_idx is not None:
            clauses.append({
                "clause_id": "jawab_particle_0",
                "clause_type": "conditional_particle",
                "arabic_label": "أداة الجواب",
                "start_token_id": str(jawab_idx),
                "end_token_id": str(jawab_idx),
                "head_token_id": str(jawab_idx),
                "parent_clause_id": "shart_particle_0",
                "confidence": 0.9,
                "rule": "L4_JAZM_operator",
                "limitation": None,
            })
            clause_count += 1

            jaw_head_id = str(jaw_head) if jaw_head is not None else str(jawab_idx + 1)
            clauses.append({
                "clause_id": "jawab_shart_0",
                "clause_type": "jawab_shart",
                "arabic_label": "جواب الشرط",
                "start_token_id": str(jawab_idx + 1),
                "end_token_id": str(len(tokens) - 1),
                "head_token_id": jaw_head_id,
                "parent_clause_id": "jawab_particle_0",
                "confidence": 0.8 if jaw_head is not None else 0.5,
                "rule": "span_after_jawab_particle" if jaw_head is not None else "no_verb_found_fallback",
                "limitation": None if jaw_head is not None else "jawab_shart verb not found within span",
            })
            clause_count += 1
        else:
            jaw_head_id = str(jaw_head) if jaw_head is not None else str(feil_end + 1)
            if feil_end + 1 <= len(tokens) - 1:
                clauses.append({
                    "clause_id": "jawab_shart_0",
                    "clause_type": "jawab_shart",
                    "arabic_label": "جواب الشرط",
                    "start_token_id": str(feil_end + 1),
                    "end_token_id": str(len(tokens) - 1),
                    "head_token_id": jaw_head_id,
                    "parent_clause_id": "shart_particle_0",
                    "confidence": 0.7,
                    "rule": "span_after_feil_shart",
                    "limitation": "no jawab particle found",
                })
                clause_count += 1

        out = {
            "status": "success",
            "clause_analysis": clauses,
            "clauses": clauses,
            "clause_count": clause_count,
            "conditional_structure_detected": True,
            "coverage": "conditional_decomposition",
            "ambiguity_log": [],
            "verbal_clause_regions": [],
        }
        _apply_clause_engine_pass2(lo, out, tokens)
        return out

    except Exception as e:
        return {
            "status": "error",
            "clause_analysis": [],
            "clauses": [],
            "clause_count": 0,
            "conditional_structure_detected": False,
            "coverage": "error",
            "ambiguity_log": [{"issue": str(e)}],
            "verbal_clause_regions": [],
            "hal_detected": False,
            "tamyiz_detected": False,
            "sila_detected": False,
        }


def _get_tokens(lo: dict) -> list:
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    words = tr2.get("tokens", [])
    if words:
        return [w.get("word", "") for w in words] if isinstance(words[0], dict) else words
    l4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    w4 = l4.get("words", [])
    if w4:
        return [w.get("word", w) for w in w4] if w4 and isinstance(w4[0], dict) else w4
    return []


def _first_verb(start: int, end: int, l8b_profiles: dict, l5_words: list):
    for i in range(start, end + 1):
        if str(i) in l8b_profiles:
            return i
        if i < len(l5_words):
            w = l5_words[i] if isinstance(l5_words[i], dict) else {}
            if (w.get("kind") or "").strip().lower() in ("verb", "فعل"):
                return i
    return None


def _single_main_clause(token_count: int) -> dict:
    main = [{
        "clause_id": "main_0",
        "clause_type": "main",
        "arabic_label": "جملة رئيسية",
        "start_token_id": "0",
        "end_token_id": str(max(0, token_count - 1)),
        "head_token_id": "0",
        "parent_clause_id": None,
        "confidence": 0.5,
        "rule": "no_conditional_particle_found",
        "limitation": "no conditional structure detected",
    }]
    return {
        "status": "success",
        "clause_analysis": main,
        "clauses": main,
        "clause_count": 1,
        "conditional_structure_detected": False,
        "coverage": "main_clause_only",
        "ambiguity_log": [],
        "verbal_clause_regions": [],
    }


