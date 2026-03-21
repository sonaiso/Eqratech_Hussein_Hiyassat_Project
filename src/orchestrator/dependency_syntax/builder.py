# -*- coding: utf-8 -*-
"""
Stage 15 DEPENDENCY_SYNTAX_BUILDER — Pass A.
Builds explicit dependency graph from L10B signals. Nominal (mubtada-khabar) and verbal (verb-subject-object) only.
Reads L5, L8, L8B, L10B; does not mutate L10B. ROOT represented only in root_resolution.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from .relation_inventory import (
    AR_ATF,
    AR_ATF_CONJ,
    AR_BADAL,
    AR_FAIL,
    AR_ISM_INNA,
    AR_JAR_MAJRUR,
    AR_KHABAR,
    AR_MAF3UL_BIH,
    AR_MUBTADA,
    AR_MUDAF,
    AR_NA3T,
    AR_NAIB_FAIL,
    AR_PP_ATTACH,
    REL_APPOS,
    REL_COORD,
    REL_COORD_CONJ,
    REL_IDAFA,
    REL_INNA_NAME,
    REL_JAR_MAJRUR,
    REL_NAIB_SUBJ,
    REL_OBJ,
    REL_PRED,
    REL_PP_ATTACH,
    REL_SIFA,
    REL_SUBJ,
)
from ..l14_jamid_mushtaq import has_strong_true_verb_evidence


def _tokens_from_lo(lo: Dict[str, Any]) -> List[str]:
    """Token list from L2 or L5."""
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    if tokens:
        return [t.get("word") or "" for t in tokens if t.get("word")]
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words = tr5.get("words") or []
    return [w.get("word") or "" for w in words if w.get("word")]


def _words5(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    return tr5.get("words") or []


def _op_words(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L4 operator words for conjunction/particle detection."""
    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    return tr4.get("words") or []


# Pass C: conjunction particles (عطف) — normalized surface
_CONJ_NORMALIZED = frozenset({"و", "ف", "ثم", "او", "أو", "ام", "أم"})

# Pass E: tokens that must not be chosen as root (operator, conjunction, preposition, conditional)
_CONDITIONAL_OPERATOR_NORMALIZED = frozenset({"لو", "ان", "إن", "اذا", "إذا", "ان", "أن", "كي", "لن", "لم", "لما", "لا"})

def _excluded_from_root(
    tokens: List[str],
    op_words: List[Dict[str, Any]],
    edges: List[Dict[str, Any]],
) -> set:
    """Indices of operator/conjunction/preposition/conditional — NEVER use as root unless rare rule."""
    excluded: set = set()
    for i, surface in enumerate(tokens):
        norm = _normalize_surface(surface or "")
        if norm in _CONJ_NORMALIZED:
            excluded.add(i)
        if norm in _CONDITIONAL_OPERATOR_NORMALIZED:
            excluded.add(i)
        if any((x.get("word") or "").strip() == (surface or "").strip() and x.get("operator") for x in op_words):
            excluded.add(i)
    for e in edges:
        if (e.get("relation") or "").strip() == "majrur":
            from_id = e.get("from_id")
            try:
                if from_id is not None:
                    excluded.add(int(from_id))
            except (TypeError, ValueError):
                pass
    return excluded


# PP-like token starts (normalized): multi-letter cues only (see _has_pp_prefix).
_PP_PREFIX_SEQUENCES = (
    "كال",
    "كٱل",
    "بال",
    "بٱل",
    "لل",
    "لٱل",
    "في",
    "فٍ",
    "فى",
    "فٱ",
    "من",
    "عن",
    "مع",
    "عند",
    "إلى",
    "الى",
    "الي",
    "على",
    "علي",
    "حتى",
    "خلا",
    "عدا",
)
# Common adverbs / non-apposition dependents (normalized)
_APPOS_EXCLUDED_DEPENDENT_NORM = frozenset({"ابدا", "أبدا", "دائما", "حقا", "الآن", "الان"})


def _has_pp_prefix(surface: str) -> bool:
    """True if normalized token begins with a typical harf+jarr cluster (في، كالـ، بالـ، …)."""
    norm = _normalize_surface(surface or "")
    if not norm:
        return False
    return any(norm.startswith(p) for p in _PP_PREFIX_SEQUENCES)


def _is_excluded_appos_dependent(surface: str) -> bool:
    """True if token is a common adverb or non-apposition form; do not use as APPOS dependent."""
    norm = _normalize_surface(surface or "")
    return norm in _APPOS_EXCLUDED_DEPENDENT_NORM


def _has_attached_coord_prefix(surface: str) -> bool:
    """
    True if token likely carries an attached coordination prefix (e.g. وَالـ / فَالـ).
    Keep this conservative to avoid hijacking ordinary lexical initials.
    """
    raw = (surface or "").strip()
    norm = _normalize_surface(raw)
    if len(norm) < 4:
        return False
    if not norm.startswith(("و", "ف")):
        return False
    return norm.startswith(("وال", "فال"))


def _is_emphatic_inna_operator(surface: str, op_words: List[Dict[str, Any]]) -> bool:
    """High-confidence إنَّ / أنَّ governance only."""
    raw = (surface or "").strip()
    norm = _normalize_surface(raw)
    if norm not in ("إن", "أن"):
        return False
    for w in op_words:
        if (w.get("word") or "").strip() != raw:
            continue
        operator = w.get("operator")
        if isinstance(operator, dict):
            if (operator.get("effect_signature") or "").strip() == "ACC_TAWKID":
                return True
        elif operator:
            return True
    return False


def _token_to_clause(clause_units: List[Dict[str, Any]]) -> Dict[str, str]:
    """Map token_id (str) to clause_id. Tokens not in any unit get 'main' or first unit id."""
    out: Dict[str, str] = {}
    for c in clause_units or []:
        cid = c.get("clause_id") or c.get("type") or "main"
        start = c.get("start_token_id")
        end = c.get("end_token_id")
        try:
            s, e = int(start or 0), int(end or 0)
            for t in range(s, e + 1):
                out[str(t)] = cid
        except (TypeError, ValueError):
            pass
    return out


def _is_conjunction_token(surface: str, op_words: List[Dict[str, Any]]) -> bool:
    """True if token is a coordination conjunction (waw, fa, thumma, aw, am)."""
    norm = _normalize_surface(surface or "")
    if not norm:
        return False
    if norm in _CONJ_NORMALIZED:
        return True
    # L4 operator with conjunction-like surface
    if any((x.get("word") or "").strip() == (surface or "").strip() and x.get("operator") for x in op_words):
        if norm in _CONJ_NORMALIZED or norm in ("و", "ف", "ثم"):
            return True
    return False


def _l8b_profile_by_index(tokens: List[str], lo: Dict[str, Any]) -> Dict[int, Dict[str, Any]]:
    """Token index -> effective L8B verb profile (strong profiles only).

    Stage 15 must not treat every weak/candidate L8B profile as a real verb.
    A profile counts as an effective verb only when at least one of:
    - exact token_id match with resolved status
    - L5 says the token is a verb
    - strong L8B evidence (passive voice, high confidence, or object-governance)
    """
    out: Dict[int, Dict[str, Any]] = {}
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    words5 = _words5(lo)
    for i, surface in enumerate(tokens):
        word = (surface or "").strip()
        l5_kind = ""
        if i < len(words5) and isinstance(words5[i], dict):
            l5_kind = (words5[i].get("kind") or "").strip().lower()
        for p in profiles:
            same_token = str(p.get("token_id")) == str(i)
            same_surface = (p.get("surface") or "").strip() == word
            if not same_token and not same_surface:
                continue
            if (p.get("status") or "").strip().lower() == "not_applicable":
                continue
            confidence = float(p.get("confidence") or 0.0)
            status = (p.get("status") or "").strip().lower()
            voice = (p.get("voice") or "").strip().lower()
            transitivity = (p.get("transitivity") or "").strip().lower()
            objects = int(p.get("objects") or 0)
            l5_is_verb = l5_kind in ("verb", "فعل")
            strong_profile = (
                status == "resolved"
                or voice == "passive"
                or confidence >= 0.75
                or objects > 0
                or "transitive" in transitivity
                or "متعد" in transitivity
            )
            if same_token and (l5_is_verb or strong_profile):
                out[i] = p
                break
            if same_surface and l5_is_verb:
                out[i] = p
                break
    return out


def _is_noun_like(kind: str, pos_hint: str) -> bool:
    k = (kind or "").strip().lower()
    p = (pos_hint or "").strip().lower()
    noun_tags = ("noun", "اسم", "name", "proper_noun", "proper noun", "علم")
    return (
        k in noun_tags
        or p in noun_tags
        or "noun" in p
        or "name" in p
        or "proper" in p
    )


def _is_explicit_waw_coord_conjunct_compatible(
    idx: int,
    tokens: List[str],
    word_to_kind: Dict[str, str],
    node_by_id: Dict[str, Dict],
    l14_map: Dict[int, str],
) -> bool:
    """
    Tokens that may serve as head/dependent in Pass 5b attached وَالـ COORD chains.

    L5 often tags اسم فاعل / صيغة مشبهة as 'verb'; L14 derivational class then keeps the
    token in the nominal coordination series. Without this, the resolver skips the token and
    links وَالْمُتَصَدِّقَاتِ to the previous conjunct (chain hole).
    """
    if idx < 0 or idx >= len(tokens):
        return False
    surf = (tokens[idx] or "").strip()
    kind = word_to_kind.get(surf, "")
    pos = (node_by_id.get(str(idx)) or {}).get("pos_hint") or ""
    if _is_noun_like(kind, pos):
        return True
    if not _has_attached_coord_prefix(surf):
        return False
    dc = (l14_map.get(idx) or "").strip()
    # Participial / sifa mushtaha in long accusative conjunct lists (Batch 1.5).
    if dc in ("ISM_FAIL", "ISM_MAFUUL", "SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH"):
        return True
    return False


def _normalize_surface(s: str) -> str:
    """Strip Arabic diacritics for matching."""
    if not s or not isinstance(s, str):
        return ""
    result = []
    for c in (s or "").strip():
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _normalize_root_value(root: Any) -> str:
    """Normalize root values from L8/L8B for safe same-root comparison."""
    if isinstance(root, dict):
        root = root.get("formatted") or "-".join(root.get("letters") or [])
    if not isinstance(root, str):
        return ""
    result = []
    for c in root:
        if c == "-":
            continue
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _roots8_by_index(lo: Dict[str, Any]) -> Dict[int, str]:
    """Token index -> normalized root: canonical ARABIC_WORD_STATE first, else L8."""
    from ..arabic_word_state import ARABIC_WORD_STATE_KEY, ensure_arabic_word_state

    ensure_arabic_word_state(lo)
    out: Dict[int, str] = {}
    trs = (lo.get(ARABIC_WORD_STATE_KEY) or {}).get("transformation_result") or {}
    by_id = trs.get("by_token_id") or {}
    for tid, ws in by_id.items():
        if not str(tid).isdigit():
            continue
        i = int(tid)
        root = _normalize_root_value(
            (ws.get("canonical_root") or ws.get("root")) if isinstance(ws, dict) else None
        )
        if root:
            out[i] = root
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    words8 = tr8.get("words") or []
    for i, w in enumerate(words8):
        if i in out:
            continue
        if not isinstance(w, dict):
            continue
        root = _normalize_root_value(w.get("root"))
        if root:
            out[i] = root
    return out


def _same_clause(token_to_clause: Dict[str, str], left_idx: int, right_idx: int) -> bool:
    """True if both tokens are in the same clause (or clause info missing)."""
    left_clause = token_to_clause.get(str(left_idx), "")
    right_clause = token_to_clause.get(str(right_idx), "")
    return not left_clause or not right_clause or left_clause == right_clause


def _coord_resume_blocked_head(
    h: int,
    dependency_links: List[Dict[str, Any]],
    l14_map: Dict[int, str],
    tokens: List[str],
) -> bool:
    """
    Token at h cannot serve as the left conjunct for a following وَ+NP when it sits inside a local
    participial object span (OBJ of ISM_FAIL/ISM_MAFUUL) or is a documented accusative intensifier tail.
    """
    surf = (tokens[h] or "").strip()
    n = _normalize_surface(surf)
    if n in ("كثيرا", "قليلا", "شديدا", "تماما"):
        return True
    for link in dependency_links:
        if (link.get("relation") or "").strip() != REL_OBJ:
            continue
        if str(link.get("dependent_id")) != str(h):
            continue
        hid = link.get("head_id")
        try:
            hi = int(hid)
        except (TypeError, ValueError):
            continue
        dc = (l14_map.get(hi) or "").strip()
        if dc in ("ISM_FAIL", "ISM_MAFUUL"):
            return True
    return False


def _resolve_coord_head_attached_waw(
    i: int,
    tokens: List[str],
    word_to_kind: Dict[str, str],
    node_by_id: Dict[str, Dict],
    token_to_clause: Dict[str, str],
    dependency_links: List[Dict[str, Any]],
    l14_map: Dict[int, str],
) -> Optional[int]:
    """
    Leftward search for COORD head for token i (وَ+conjunct): skip object-of-participle and intensifier
    tails so coordination resumes after a local governed-object span (Batch 1.2).
    """
    h = i - 1
    while h >= 0:
        if not _same_clause(token_to_clause, h, i):
            break
        if _coord_resume_blocked_head(h, dependency_links, l14_map, tokens):
            h -= 1
            continue
        if _is_explicit_waw_coord_conjunct_compatible(
            h, tokens, word_to_kind, node_by_id, l14_map
        ) and _is_explicit_waw_coord_conjunct_compatible(
            i, tokens, word_to_kind, node_by_id, l14_map
        ):
            return h
        h -= 1
    return None


def _is_maf3ul_mutlaq_candidate(
    verb_idx: int,
    candidate_idx: int,
    tokens: List[str],
    words5: List[Dict[str, Any]],
    roots8: Dict[int, str],
) -> bool:
    """Conservative guard: same-root masdar-like noun should not be forced into OBJ."""
    verb_root = roots8.get(verb_idx, "")
    cand_root = roots8.get(candidate_idx, "")
    if not verb_root or not cand_root or verb_root != cand_root:
        return False
    kind = ""
    if candidate_idx < len(words5) and isinstance(words5[candidate_idx], dict):
        kind = (words5[candidate_idx].get("kind") or "").strip().lower()
    if kind not in ("noun", "اسم", ""):
        return False
    norm = _normalize_surface(tokens[candidate_idx] or "")
    return norm.endswith("ا") or norm.endswith("اً") or norm.endswith("ا")


def _is_adjective_like(kind: str, pos_hint: str) -> bool:
    k = (kind or "").strip().lower()
    p = (pos_hint or "").strip().lower()
    return k in ("adjective", "صفة", "نعت") or p in ("adjective", "صفة", "نعت") or "adj" in p or "نعت" in p


def _is_verb_like(kind: str, pos_hint: str, l8b_profile: Optional[Dict]) -> bool:
    if l8b_profile:
        return True
    k = (kind or "").strip().lower()
    p = (pos_hint or "").strip().lower()
    return k in ("verb", "فعل") or p in ("verb", "فعل") or "verb" in p


def _first_verb_index(
    tokens: List[str],
    words5: List[Dict],
    nodes: List[Dict],
    l8b_map: Dict[int, Dict[str, Any]],
) -> Optional[int]:
    """First token index that is a verb (L8B or L5/L10B pos_hint). Fallback: index 0 for verbal."""
    word_to_kind: Dict[str, str] = {}
    for w in words5:
        word_to_kind[(w.get("word") or "").strip()] = (w.get("kind") or "").strip()
    node_by_id: Dict[str, Dict] = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    for i, surface in enumerate(tokens):
        if l8b_map.get(i):
            return i
        kind = word_to_kind.get((surface or "").strip(), "")
        pos_hint = (node_by_id.get(str(i)) or {}).get("pos_hint") or ""
        if _is_verb_like(kind, pos_hint, None):
            return i
    return 0 if tokens else None


def _map_l10b_relation(l10b_relation: str) -> Tuple[str, str]:
    """Map L10B edge relation to Stage 15 relation and arabic_role. Returns (relation, arabic_role)."""
    r = (l10b_relation or "").strip().lower()
    if r in ("naib_fa'il", "naib_fail"):
        return (REL_NAIB_SUBJ, AR_NAIB_FAIL)
    if r == "majrur":
        return (REL_JAR_MAJRUR, AR_JAR_MAJRUR)
    if r == "idafa":
        return (REL_IDAFA, AR_MUDAF)
    if r in ("fa'il", "subject"):
        return (REL_SUBJ, AR_FAIL)
    if r in ("maf'ul_bih", "maful_bih", "object"):
        return (REL_OBJ, AR_MAF3UL_BIH)
    if r == "mubtada":
        return (REL_SUBJ, AR_MUBTADA)
    if r == "khabar":
        return (REL_PRED, AR_KHABAR)
    return (REL_SUBJ, AR_FAIL)  # fallback


def _add_link(
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
    head_id: str,
    dependent_id: str,
    **link_rest: Any,
) -> None:
    """Add a dependency link only if head_id != dependent_id and exact duplicate does not already exist."""
    if head_id == dependent_id:
        corrections_log.append({
            "source_l10b_signal": {"type": "self_loop", "id": head_id, "value": head_id},
            "stage15_decision": {"relation": link_rest.get("relation"), "head_id": head_id, "dependent_id": dependent_id},
            "override_reason": "self_loop_forbidden",
            "confidence": link_rest.get("confidence", 0),
            "evidence_signals": ["self_loop_guard"],
        })
        return
    relation = link_rest.get("relation")
    for link in dependency_links:
        if (
            link.get("head_id") == head_id
            and link.get("dependent_id") == dependent_id
            and link.get("relation") == relation
        ):
            return
    dependency_links.append({
        "head_id": head_id,
        "dependent_id": dependent_id,
        **link_rest,
    })


def _has_explicit_coordination_evidence(
    tokens: List[str],
    op_words: List[Dict[str, Any]],
    head_idx: int,
    dep_idx: int,
) -> bool:
    """Explicit conjunction evidence only: standalone conjunction or attached prefix."""
    if head_idx < 0 or dep_idx <= head_idx or dep_idx >= len(tokens):
        return False
    if dep_idx == head_idx + 1 and _has_attached_coord_prefix(tokens[dep_idx] or ""):
        return True
    if dep_idx == head_idx + 2 and _is_conjunction_token((tokens[head_idx + 1] or "").strip(), op_words):
        return True
    return False


def _l14_classification_by_index(tokens: List[str], lo: Dict[str, Any]) -> Dict[int, str]:
    """Token index -> L14 derivational_class where available (prefer token_id match)."""
    out: Dict[int, str] = {}
    tr = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    classes = tr.get("token_classifications") or []
    by_tid: Dict[int, str] = {}
    for row in classes:
        try:
            tid = int(row.get("token_id"))
            by_tid[tid] = (row.get("derivational_class") or "").strip()
        except (TypeError, ValueError):
            continue
    for i in range(len(tokens)):
        if i in by_tid:
            out[i] = by_tid[i]
            continue
        surf = (tokens[i] or "").strip()
        for row in classes:
            if (row.get("surface") or "").strip() == surf:
                out[i] = (row.get("derivational_class") or "").strip()
                break
    return out


def _looks_indefinite_object_cue(surface: str) -> bool:
    """Conservative cue for مفعول مطلق / indefinite objects like أَحَداً when L8B transitivity is missing."""
    n = _normalize_surface(surface or "")
    if not n:
        return False
    for a in ("\u0623", "\u0625", "\u0671", "\u0622"):
        n = n.replace(a, "\u0627")
    return n.startswith("احد") or n.startswith("شيئ")


def _is_skippable_pronoun_clitic_between_verb_args(surface: str) -> bool:
    """Skip bound pronoun / clitic chunks when scanning objects after a finite verb."""
    n = _normalize_surface(surface or "")
    if not n:
        return False
    if n.startswith("ل") and len(n) <= 5:
        return True
    if n in ("به", "بها", "بهم", "كما", "كن", "كم", "ه", "ها", "هم", "هن", "هما"):
        return True
    return False


def _word_to_kind_map(words5: List[Dict[str, Any]]) -> Dict[str, str]:
    m: Dict[str, str] = {}
    for w in words5:
        m[(w.get("word") or "").strip()] = (w.get("kind") or "").strip()
    return m


def _apply_strong_verb_local_subj_obj(
    tokens: List[str],
    words5: List[Dict[str, Any]],
    nodes: List[Dict[str, Any]],
    l8b_map: Dict[int, Dict[str, Any]],
    lo: Dict[str, Any],
    token_to_clause: Dict[str, str],
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
    roots8: Dict[int, str],
    excluded_from_root: set,
) -> None:
    """Finite verbs with strong evidence: SUBJ on first content noun; OBJ on next (skip clitics)."""
    word_to_kind = _word_to_kind_map(words5)
    node_by_id = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    for verb_idx, surface in enumerate(tokens):
        if verb_idx in excluded_from_root:
            continue
        if not has_strong_true_verb_evidence(str(verb_idx), surface or "", lo):
            continue
        has_subj = any(
            l.get("head_id") == str(verb_idx) and l.get("relation") == REL_SUBJ for l in dependency_links
        )
        has_obj = any(
            l.get("head_id") == str(verb_idx) and l.get("relation") == REL_OBJ for l in dependency_links
        )
        content_nouns: List[int] = []
        for j in range(verb_idx + 1, len(tokens)):
            if not _same_clause(token_to_clause, verb_idx, j):
                break
            if j in excluded_from_root:
                continue
            surf_j = (tokens[j] or "").strip()
            if _is_skippable_pronoun_clitic_between_verb_args(surf_j):
                continue
            kind = word_to_kind.get(surf_j, "")
            pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if not _is_noun_like(kind, pos_hint):
                continue
            content_nouns.append(j)
        if not content_nouns:
            continue
        profile = l8b_map.get(verb_idx) or {}
        is_passive = (profile.get("voice") or "").strip().lower() == "passive"
        transitivity = (profile.get("transitivity") or "").strip().lower()
        transitive = (
            "transitive" in transitivity
            or int(profile.get("objects") or 0) > 0
            or int(profile.get("exp_objects") or 0) > 0
        )
        if not transitive and len(content_nouns) >= 2:
            transitive = True
        first_n = content_nouns[0]
        second_n = content_nouns[1] if len(content_nouns) >= 2 else None
        first_surf = (tokens[first_n] or "").strip()
        first_definite = _normalize_surface(first_surf).startswith("ال")
        effective_transitive = transitive
        if (
            not effective_transitive
            and not is_passive
            and len(content_nouns) == 1
            and not first_definite
            and _looks_indefinite_object_cue(first_surf)
        ):
            effective_transitive = True
        lone_indefinite_object = (
            second_n is None
            and not first_definite
            and len(content_nouns) == 1
            and effective_transitive
            and not is_passive
        )
        if not has_subj:
            if is_passive:
                _add_link(
                    dependency_links, corrections_log, str(verb_idx), str(first_n),
                    relation=REL_NAIB_SUBJ, arabic_role=AR_NAIB_FAIL, confidence=0.82,
                    rule="Pass_E2_strong_verb_local_naib_fail", inferred=True,
                )
            elif lone_indefinite_object:
                if not has_obj and not _is_maf3ul_mutlaq_candidate(verb_idx, first_n, tokens, words5, roots8):
                    _add_link(
                        dependency_links, corrections_log, str(verb_idx), str(first_n),
                        relation=REL_OBJ, arabic_role=AR_MAF3UL_BIH, confidence=0.78,
                        rule="Pass_E2_transitive_lone_indefinite_maf3ul", inferred=True,
                    )
                    has_obj = True
            else:
                _add_link(
                    dependency_links, corrections_log, str(verb_idx), str(first_n),
                    relation=REL_SUBJ, arabic_role=AR_FAIL, confidence=0.82,
                    rule="Pass_E2_strong_verb_local_subj", inferred=True,
                )
        if second_n is not None and effective_transitive and not is_passive and not has_obj:
            if _is_maf3ul_mutlaq_candidate(verb_idx, second_n, tokens, words5, roots8):
                continue
            _add_link(
                dependency_links, corrections_log, str(verb_idx), str(second_n),
                relation=REL_OBJ, arabic_role=AR_MAF3UL_BIH, confidence=0.78,
                rule="Pass_E2_strong_verb_local_obj", inferred=True,
            )


def _apply_ism_fail_governed_object(
    tokens: List[str],
    words5: List[Dict[str, Any]],
    nodes: List[Dict[str, Any]],
    l14_map: Dict[int, str],
    token_to_clause: Dict[str, str],
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
    op_words: List[Dict[str, Any]],
    lo: Dict[str, Any],
) -> None:
    """Narrow ISM_FAIL governor → immediately following noun = OBJ (participial object patterns)."""
    word_to_kind = _word_to_kind_map(words5)
    node_by_id = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    existing = {(l.get("head_id"), l.get("dependent_id")) for l in dependency_links}
    for i, surface in enumerate(tokens):
        if (l14_map.get(i) or "") != "ISM_FAIL":
            continue
        j = i + 1
        if j >= len(tokens):
            continue
        if not _same_clause(token_to_clause, i, j):
            continue
        if any((x.get("word") or "").strip() == (tokens[j] or "").strip() and x.get("operator") for x in op_words):
            continue
        surf_j = (tokens[j] or "").strip()
        # ISM_FAIL participle governs a nominal object only. A following strong finite verb opens a new
        # verbal clause — never attach it as OBJ (L5 may mis-tag the verb as noun-like).
        if (l14_map.get(j) or "").strip() == "VERB":
            continue
        if has_strong_true_verb_evidence(str(j), surf_j, lo):
            continue
        if _has_pp_prefix(surf_j):
            continue
        if _has_attached_coord_prefix(surf_j):
            continue
        kind = word_to_kind.get(surf_j, "")
        pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
        if not _is_noun_like(kind, pos_hint):
            continue
        # Nominal shell often adds mubtada→khabar (PRED); ISM_FAIL + governed object supersedes that.
        for _rip in range(len(dependency_links) - 1, -1, -1):
            lk = dependency_links[_rip]
            if (
                str(lk.get("head_id")) == str(i)
                and str(lk.get("dependent_id")) == str(j)
                and (lk.get("relation") or "").strip() == REL_PRED
                and (lk.get("rule") or "").strip() == "nominal_mubtada_to_khabar"
            ):
                corrections_log.append({
                    "source_l10b_signal": {"type": "nominal_pred_overlap", "head_id": str(i), "dependent_id": str(j)},
                    "stage15_decision": {"relation": REL_OBJ, "head_id": str(i), "dependent_id": str(j)},
                    "override_reason": "Pass_E3_ism_fail_supersedes_nominal_mubtada_khabar",
                    "confidence": float(lk.get("confidence") or 0.75),
                    "evidence_signals": ["ISM_FAIL", "immediate_noun_governance"],
                })
                dependency_links.pop(_rip)
                existing.discard((str(i), str(j)))
                break
        if (str(i), str(j)) in existing:
            continue
        _add_link(
            dependency_links, corrections_log, str(i), str(j),
            relation=REL_OBJ, arabic_role=AR_MAF3UL_BIH, confidence=0.72,
            rule="Pass_E3_ism_fail_immediate_object", inferred=True,
        )
        existing.add((str(i), str(j)))


def _has_waw_second_conjunct_prefix(surface: str) -> bool:
    """
    True if token begins with attached و as a second conjunct (وX…), not وَالـ (article chain).
    Used to prefer coordination / NAʿT over APPOS in verbal tails.
    """
    norm = _normalize_surface(surface or "")
    if len(norm) < 4:
        return False
    if not norm.startswith("و"):
        return False
    # وَالرَّجُلُ / وَالْمُسْلِمِينَ — article continuation, not وَأَجْرًا-style second conjunct
    if norm[1] == "ل":
        return False
    return True


def _strip_false_appos_structural_competition(
    tokens: List[str],
    lo: Dict[str, Any],
    l14_map: Dict[int, str],
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
    words5: List[Dict[str, Any]],
    nodes: List[Dict[str, Any]],
) -> None:
    """
    After Pass C APPOS, remove edges that lose to stronger structural analyses:
    - object + coordinated second conjunct (وَمفعولٌ ثانٍ)
    - waw-conjunct + SIFA_MUSHABBAHA adjective (نعت عطف)
    - ISM_FAIL object + following SIFA_MUSHABBAHA (حال/صيغة صفتية على المفعول)

    No token-ID hacks; uses OBJ links, L14 classes, coordination shape, strong-verb OBJ domain.
    """
    if not tokens:
        return
    word_to_kind = _word_to_kind_map(words5)
    node_by_id = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}

    obj_heads_by_dep: Dict[int, int] = {}
    for lk in dependency_links:
        if (lk.get("relation") or "").strip() != REL_OBJ:
            continue
        h = lk.get("head_id")
        d = lk.get("dependent_id")
        try:
            hi = int(h)
            di = int(d)
        except (TypeError, ValueError):
            continue
        obj_heads_by_dep[di] = hi

    strong_verb_obj_heads: set = set()
    for dep_i, gov_i in obj_heads_by_dep.items():
        surf_g = (tokens[gov_i] or "").strip() if 0 <= gov_i < len(tokens) else ""
        if has_strong_true_verb_evidence(str(gov_i), surf_g, lo):
            strong_verb_obj_heads.add(dep_i)

    to_remove: List[int] = []
    to_add_sifa: List[Tuple[str, str]] = []

    for idx, link in enumerate(dependency_links):
        if (link.get("relation") or "").strip() != REL_APPOS:
            continue
        hid_s, did_s = link.get("head_id"), link.get("dependent_id")
        if hid_s is None or did_s is None:
            continue
        try:
            hi = int(hid_s)
            di = int(did_s)
        except (TypeError, ValueError):
            continue
        if hi < 0 or di < 0 or hi >= len(tokens) or di >= len(tokens):
            continue
        if di != hi + 1:
            continue

        gov = obj_heads_by_dep.get(hi)
        l14_hi = (l14_map.get(hi) or "").strip()
        l14_di = (l14_map.get(di) or "").strip()
        surf_h = (tokens[hi] or "").strip()
        surf_d = (tokens[di] or "").strip()

        suppress = False
        reason = ""
        evidence: List[str] = []

        # R1: strong finite verb governs OBJ on head; dependent is a second conjunct (وَX)
        if gov is not None and hi in strong_verb_obj_heads and _has_waw_second_conjunct_prefix(surf_d):
            suppress = True
            reason = "Pass_C_appos_suppressed_strong_verb_obj_chain_second_conjunct"
            evidence = ["OBJ_from_strong_verb", "waw_second_conjunct"]

        # R2: waw-conjunct noun + following SIFA_MUSHABBAHA (NAʿT / agreement path)
        elif _has_waw_second_conjunct_prefix(surf_h) and l14_di == "SIFA_MUSHABBAHA":
            suppress = True
            reason = "Pass_C_appos_suppressed_waw_conjunct_plus_sifa_mushabbaha"
            evidence = ["waw_conjunct_head", "L14_SIFA_MUSHABBAHA_dependent"]
            if (hid_s, did_s) not in {
                (l.get("head_id"), l.get("dependent_id"))
                for l in dependency_links
                if (l.get("relation") or "").strip() == REL_SIFA
            }:
                to_add_sifa.append((hid_s, did_s))

        # R3: ISM_FAIL governor → object; dependent is morphologically SIFA_MUSHABBAHA (not BADAL)
        elif gov is not None and (l14_map.get(gov) or "").strip() == "ISM_FAIL" and l14_di == "SIFA_MUSHABBAHA":
            suppress = True
            reason = "Pass_C_appos_suppressed_ism_fail_obj_plus_sifa_mushabbaha"
            evidence = ["L14_ISM_FAIL_governor", "L14_SIFA_MUSHABBAHA_dependent"]

        if suppress:
            to_remove.append(idx)
            corrections_log.append({
                "source_l10b_signal": {
                    "type": "appos_structural_competition",
                    "head_id": hid_s,
                    "dependent_id": did_s,
                },
                "stage15_decision": {"relation": REL_APPOS, "suppressed": True, "prefer": "COORD_or_SIFA_or_hal"},
                "override_reason": reason,
                "confidence": float(link.get("confidence") or 0.0),
                "evidence_signals": evidence,
            })

    for idx in reversed(to_remove):
        dependency_links.pop(idx)

    for head_id, dep_id in to_add_sifa:
        kind = word_to_kind.get((tokens[int(dep_id)] or "").strip(), "") if int(dep_id) < len(tokens) else ""
        pos_hint = (node_by_id.get(dep_id) or {}).get("pos_hint") or ""
        if not _is_adjective_like(kind, pos_hint) and (l14_map.get(int(dep_id)) or "").strip() != "SIFA_MUSHABBAHA":
            continue
        _add_link(
            dependency_links, corrections_log, head_id, dep_id,
            relation=REL_SIFA, arabic_role=AR_NA3T, confidence=0.72,
            rule="Pass_C_sifa_after_appos_suppression_waw_conjunct", inferred=True,
        )


def _strip_spurious_appos_for_strong_verb_heads(
    tokens: List[str],
    lo: Dict[str, Any],
    l14_map: Dict[int, str],
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
) -> None:
    """
    Remove APPOS/BADAL edges whose head is a strong finite verb (L14 VERB or strong-verb evidence).
    Verbal predicates must not be analyzed as nominal apposition heads for the following noun.
    """
    to_remove: List[int] = []
    for idx, link in enumerate(dependency_links):
        if (link.get("relation") or "").strip() != REL_APPOS:
            continue
        hid = link.get("head_id")
        if hid is None:
            continue
        try:
            hi = int(hid)
        except (TypeError, ValueError):
            continue
        if hi < 0 or hi >= len(tokens):
            continue
        surf = (tokens[hi] or "").strip()
        if has_strong_true_verb_evidence(str(hi), surf, lo):
            to_remove.append(idx)
            continue
        if (l14_map.get(hi) or "").strip() == "VERB":
            to_remove.append(idx)
    for idx in reversed(to_remove):
        link = dependency_links.pop(idx)
        corrections_log.append({
            "source_l10b_signal": {
                "type": "appos_removed_strong_verb_head",
                "head_id": link.get("head_id"),
                "dependent_id": link.get("dependent_id"),
            },
            "stage15_decision": {"relation": "APPOS", "suppressed": True},
            "override_reason": "Pass_C_appos_suppressed_strong_verb_or_L14_VERB_head",
            "confidence": float(link.get("confidence") or 0.0),
            "evidence_signals": ["strong_true_verb_evidence", "L14_VERB"],
        })


def _suppress_conflicting_relations_for_explicit_coordination(
    dependency_links: List[Dict[str, Any]],
    corrections_log: List[Dict[str, Any]],
) -> None:
    """Explicit COORD wins over weaker nominal overlaps on the same pair."""
    explicit_coord_rules = {
        "Pass_C_coordination_conjunction_between",
        "Pass_C_coordination_attached_prefix",
    }
    explicit_coord_pairs = {
        (str(link.get("head_id")), str(link.get("dependent_id")))
        for link in dependency_links
        if (link.get("relation") or "").strip() == REL_COORD
        and (link.get("rule") or "").strip() in explicit_coord_rules
    }
    if not explicit_coord_pairs:
        return

    filtered_links: List[Dict[str, Any]] = []
    for link in dependency_links:
        pair = (str(link.get("head_id")), str(link.get("dependent_id")))
        relation = (link.get("relation") or "").strip()
        if pair in explicit_coord_pairs and relation in (REL_APPOS, REL_PRED):
            corrections_log.append({
                "source_l10b_signal": {"type": "relation_overlap", "head_id": pair[0], "dependent_id": pair[1], "relation": relation},
                "stage15_decision": {"relation": REL_COORD, "head_id": pair[0], "dependent_id": pair[1]},
                "override_reason": "explicit_coordination_suppresses_conflicting_nominal_relation",
                "confidence": float(link.get("confidence") or 0.0),
                "evidence_signals": ["explicit_coordination"],
            })
            continue
        filtered_links.append(link)
    dependency_links[:] = filtered_links


def _first_two_content_indices(
    tokens: List[str],
    words5: List[Dict],
    nodes: List[Dict],
    l8b_map: Dict[int, Dict[str, Any]],
) -> Tuple[Optional[int], Optional[int]]:
    """First two noun-like content token indices (for nominal: mubtada, khabar). Skip verb. Fallback: first two non-verb."""
    word_to_kind: Dict[str, str] = {}
    for w in words5:
        word_to_kind[(w.get("word") or "").strip()] = (w.get("kind") or "").strip()
    node_by_id: Dict[str, Dict] = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    first: Optional[int] = None
    second: Optional[int] = None
    for i, surface in enumerate(tokens):
        if l8b_map.get(i):
            continue
        kind = word_to_kind.get((surface or "").strip(), "")
        pos_hint = (node_by_id.get(str(i)) or {}).get("pos_hint") or ""
        if _is_noun_like(kind, pos_hint):
            if first is None:
                first = i
            elif second is None:
                second = i
                break
    if first is not None and second is not None:
        return first, second
    # Fallback: first two tokens that are not L8B verb (for nominal, no verb at 0)
    for i in range(len(tokens)):
        if l8b_map.get(i):
            continue
        if first is None:
            first = i
        elif second is None:
            second = i
            break
    return first, second


def build_dependency_syntax(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """
    Build Stage 15 dependency graph from L10B (and L5, L8, L8B) signals.
    Pass A: nominal (mubtada-khabar) and verbal (verb-subject-object / passive subject) only.
    Returns dict for lo["DEPENDENCY_SYNTAX_BUILDER"] or None if upstream missing.
    """
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    tr10b = l10b.get("transformation_result") or {}
    nodes = tr10b.get("dependency_nodes") or []
    edges = tr10b.get("dependency_edges") or []
    summary = tr10b.get("syntax_summary") or {}
    main_clause_type = (summary.get("main_clause_type") or "").strip().lower()

    tokens = _tokens_from_lo(lo)
    if not tokens and nodes:
        tokens = [n.get("surface") or "" for n in sorted(nodes, key=lambda n: int(n.get("token_id") or 0))]
    if not tokens:
        return None
    words5 = _words5(lo)
    l8b_map = _l8b_profile_by_index(tokens, lo)
    l14_map = _l14_classification_by_index(tokens, lo)
    roots8 = _roots8_by_index(lo)
    node_by_id = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    op_words = _op_words(lo)
    clause_units = tr10b.get("clause_units") or []
    token_to_clause = _token_to_clause(clause_units)
    excluded_from_root = _excluded_from_root(tokens, op_words, edges)

    dependency_links: List[Dict[str, Any]] = []
    root_id = "0"
    root_form = tokens[0] if tokens else ""
    root_confidence = 0.5
    root_rule = "default_first_token"
    ambiguity_log: List[Dict[str, Any]] = []
    corrections_log: List[Dict[str, Any]] = []

    # ----- Patch A2: Carry-forward L10B resolved edges (before Stage 15 rules) -----
    existing_pairs: set = set()
    for e in edges:
        if (e.get("status") or "").strip().lower() != "resolved":
            continue
        from_id = e.get("from_id")
        to_id = e.get("to_id")
        if from_id is None or to_id is None:
            continue
        h, d = str(from_id), str(to_id)
        if (h, d) in existing_pairs:
            continue
        rel_s15, ar_s15 = _map_l10b_relation(e.get("relation") or "")
        conf = float(e.get("confidence") or 0.75)
        link_entry = {
            "relation": rel_s15,
            "arabic_role": ar_s15,
            "confidence": conf,
            "rule": "carried_forward_from_L10B",
            "inferred": False,
        }
        before_len = len(dependency_links)
        _add_link(dependency_links, corrections_log, h, d, **link_entry)
        if len(dependency_links) > before_len:
            existing_pairs.add((h, d))
            corrections_log.append({
                "source_l10b_signal": {"type": "resolved_edge", "from_id": from_id, "to_id": to_id, "relation": e.get("relation")},
                "stage15_decision": {"relation": rel_s15, "head_id": h, "dependent_id": d},
                "override_reason": "L10B resolved edge preserved",
                "confidence": conf,
                "evidence_signals": ["L10B_resolved"],
            })

    # Pass E: root selection — never operator/conjunction/preposition; priority: resolved verb > clause head verb > predicate > fallback content
    if main_clause_type == "nominal":
        # Nominal: no SUBJ link (mubtada is in root_resolution only). Canonical: mubtada → PRED → khabar.
        first_idx, second_idx = _first_two_content_indices(tokens, words5, nodes, l8b_map)
        if first_idx is not None and first_idx not in excluded_from_root:
            root_id = str(first_idx)
            root_form = (tokens[first_idx] or "").strip()
            root_confidence = 0.75
            root_rule = "nominal_mubtada_first_content"
        elif first_idx is not None and first_idx in excluded_from_root:
            for j in range(first_idx + 1, len(tokens)):
                if j not in excluded_from_root and not l8b_map.get(j):
                    kind = next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), "")
                    pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
                    if _is_noun_like(kind, pos_hint):
                        root_id = str(j)
                        root_form = (tokens[j] or "").strip()
                        root_confidence = 0.6
                        root_rule = "nominal_fallback_content_after_operator"
                        break
        if first_idx is not None and second_idx is not None:
            if not _has_explicit_coordination_evidence(tokens, op_words, first_idx, second_idx):
                _add_link(
                    dependency_links, corrections_log, str(first_idx), str(second_idx),
                    relation=REL_PRED, arabic_role=AR_KHABAR, confidence=0.75,
                    rule="nominal_mubtada_to_khabar", inferred=True,
                )

    elif main_clause_type == "verbal":
        # Verbal: canonical directions — verb/root → SUBJ/OBJ/NAIB_SUBJ (governing verb is always head).
        # Pass E: never choose operator/conjunction/preposition as root; POS bridge: L8B verb counts as verb.
        verb_idx = _first_verb_index(tokens, words5, nodes, l8b_map)
        while verb_idx is not None and verb_idx in excluded_from_root:
            next_verb = None
            for j in range(verb_idx + 1, len(tokens)):
                if l8b_map.get(j) or _is_verb_like(
                    next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), ""),
                    (node_by_id.get(str(j)) or {}).get("pos_hint") or "",
                    l8b_map.get(j),
                ):
                    next_verb = j
                    break
            verb_idx = next_verb
        if verb_idx is None:
            verb_idx = 0
            if 0 in excluded_from_root:
                for j in range(1, len(tokens)):
                    if j not in excluded_from_root and not l8b_map.get(j):
                        verb_idx = j
                        break
            root_rule = "verbal_assume_first_token_verb"
            root_confidence = 0.4
        else:
            root_rule = "verbal_first_verb_L8B_or_pos_hint"
            root_confidence = 0.8
        root_id = str(verb_idx)
        root_form = (tokens[verb_idx] or "").strip()
        profile = l8b_map.get(verb_idx) or {}
        is_passive = (profile.get("voice") or "").strip().lower() == "passive"
        transitivity = (profile.get("transitivity") or "").strip().lower()
        transitive = "transitive" in transitivity or profile.get("objects", 0) or profile.get("exp_objects", 0)
        # Post-verb noun: subject or naib fa'il (head=verb, dependent=noun)
        # Root cause for missing OBJ in simple transitives:
        # weak/candidate L8B profiles on nouns were treated as verbs, so Stage 15 skipped the true subject
        # and never reached a valid second noun object candidate.
        first_after_verb: Optional[int] = None
        second_after_verb: Optional[int] = None
        for j in range(verb_idx + 1, len(tokens)):
            if not _same_clause(token_to_clause, verb_idx, j):
                continue
            if l8b_map.get(j):
                continue
            kind = next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), "")
            pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if _is_noun_like(kind, pos_hint):
                if first_after_verb is None:
                    first_after_verb = j
                elif second_after_verb is None:
                    second_after_verb = j
                    break
        if first_after_verb is None and verb_idx + 1 < len(tokens) and _same_clause(token_to_clause, verb_idx, verb_idx + 1):
            first_after_verb = verb_idx + 1
        if first_after_verb is not None and second_after_verb is None and first_after_verb + 1 < len(tokens):
            for j in range(first_after_verb + 1, len(tokens)):
                if not _same_clause(token_to_clause, verb_idx, j):
                    continue
                if l8b_map.get(j):
                    continue
                kind = next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), "")
                pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
                if _is_noun_like(kind, pos_hint):
                    second_after_verb = j
                    break
        if first_after_verb is not None:
            if is_passive:
                _add_link(
                    dependency_links, corrections_log, str(verb_idx), str(first_after_verb),
                    relation=REL_NAIB_SUBJ, arabic_role=AR_NAIB_FAIL, confidence=0.8,
                    rule="verbal_passive_post_verb_noun_naib_fail_L8B", inferred=True,
                )
            else:
                _add_link(
                    dependency_links, corrections_log, str(verb_idx), str(first_after_verb),
                    relation=REL_SUBJ, arabic_role=AR_FAIL, confidence=0.8,
                    rule="verbal_active_post_verb_noun_fail", inferred=True,
                )
        existing_core_dependents = {
            l.get("dependent_id")
            for l in dependency_links
            if l.get("head_id") == str(verb_idx) and l.get("relation") in (REL_SUBJ, REL_OBJ, REL_NAIB_SUBJ)
        }
        if (
            second_after_verb is not None
            and transitive
            and not is_passive
            and str(second_after_verb) not in existing_core_dependents
            and str(second_after_verb) != str(first_after_verb)
            and not _is_maf3ul_mutlaq_candidate(verb_idx, second_after_verb, tokens, words5, roots8)
        ):
            _add_link(
                dependency_links, corrections_log, str(verb_idx), str(second_after_verb),
                relation=REL_OBJ, arabic_role=AR_MAF3UL_BIH, confidence=0.75,
                rule="verbal_transitive_second_noun_maf3ul_bih_L8B", inferred=True,
            )
        elif (
            second_after_verb is not None
            and transitive
            and not is_passive
            and _is_maf3ul_mutlaq_candidate(verb_idx, second_after_verb, tokens, words5, roots8)
        ):
            candidate_surface = (tokens[second_after_verb] or "").strip()
            candidate_mark_reason = f"same-root masdar-like candidate after verb: {candidate_surface}"
            ambiguity_log.append({
                "token_id": str(second_after_verb),
                "candidates": [
                    {"relation": REL_OBJ, "head_id": str(verb_idx), "score": 0.45, "reason": "transitive verb but same-root masdar candidate"},
                ],
                "selected": "",
                "selection_reason": f"OBJ suppressed; {candidate_mark_reason}",
            })

    else:
        # conditional or unknown: still set root_resolution; NEVER use operator/conjunction/preposition as root
        root_confidence = 0.4
        root_rule = "unknown_clause_type_default_root"
        if 0 in excluded_from_root:
            for j in range(1, len(tokens)):
                if j not in excluded_from_root:
                    root_id = str(j)
                    root_form = (tokens[j] or "").strip()
                    root_rule = "unknown_clause_type_first_content_not_operator"
                    break

    # Pass E2/E3: strong finite verbs (local SUBJ/OBJ) and ISM_FAIL immediate objects
    _apply_strong_verb_local_subj_obj(
        tokens,
        words5,
        nodes,
        l8b_map,
        lo,
        token_to_clause,
        dependency_links,
        corrections_log,
        roots8,
        excluded_from_root,
    )
    _apply_ism_fail_governed_object(
        tokens,
        words5,
        nodes,
        l14_map,
        token_to_clause,
        dependency_links,
        corrections_log,
        op_words,
        lo,
    )

    # High-confidence emphatic governance: إنَّ / أنَّ → اسم إن
    for i, surface in enumerate(tokens[:-1]):
        if not _is_emphatic_inna_operator(surface, op_words):
            continue
        for j in range(i + 1, len(tokens)):
            if not _same_clause(token_to_clause, i, j):
                continue
            kind = next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), "")
            pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if not _is_noun_like(kind, pos_hint):
                continue
            _add_link(
                dependency_links, corrections_log, str(i), str(j),
                relation=REL_INNA_NAME, arabic_role=AR_ISM_INNA, confidence=0.88,
                rule="Pass_A_emphatic_inna_governance", inferred=True,
            )
            break

    # ----- Pass B: PP (jar-majrur), Idafa, SIFA -----
    coverage = "nominal_verbal_pp_idafa_sifa"

    # 1) JAR_MAJRUR: canonical direction harf_al_jarr → JAR_MAJRUR → majrur noun (head=harf, dependent=majrur)
    link_pairs = {(l.get("head_id"), l.get("dependent_id")) for l in dependency_links}
    for e in edges:
        if (e.get("relation") or "").strip() != "majrur":
            continue
        from_id = e.get("from_id")
        to_id = e.get("to_id")
        if from_id is None or to_id is None:
            continue
        if (str(from_id), str(to_id)) in link_pairs:
            continue
        _add_link(
            dependency_links, corrections_log, str(from_id), str(to_id),
            relation=REL_JAR_MAJRUR, arabic_role=AR_JAR_MAJRUR, confidence=0.75,
            rule="Pass_B_L10B_majrur_edge", inferred=True,
        )
        link_pairs.add((str(from_id), str(to_id)))

    # 2) PP_ATTACH: direction always head → PP. Pass E: rank verb/participle fit > same-clause noun > other; no silent weak attach.
    verb_idx_pass_b = _first_verb_index(tokens, words5, nodes, l8b_map)
    for e in edges:
        if (e.get("relation") or "").strip() != "majrur":
            continue
        harf_id = e.get("from_id")
        if harf_id is None:
            continue
        try:
            harf_idx = int(harf_id)
        except (TypeError, ValueError):
            continue
        harf_clause = token_to_clause.get(str(harf_idx), "")
        candidates: List[Dict[str, Any]] = []
        if verb_idx_pass_b is not None and verb_idx_pass_b < harf_idx and verb_idx_pass_b not in excluded_from_root:
            prof = l8b_map.get(verb_idx_pass_b) or {}
            req_pp = prof.get("required_prepositions") or []
            same_clause = token_to_clause.get(str(verb_idx_pass_b), "") == harf_clause
            sc = 0.85 if req_pp else 0.75
            if same_clause:
                sc += 0.05
            candidates.append({"relation": REL_PP_ATTACH, "head_id": str(verb_idx_pass_b), "score": min(0.98, sc), "reason": "L8B required_prepositions" if req_pp else "verb left"})
        for j in range(harf_idx - 1, -1, -1):
            if l8b_map.get(j) or j in excluded_from_root:
                continue
            kind = next((w.get("kind") or "" for w in words5 if (w.get("word") or "").strip() == (tokens[j] or "").strip()), "")
            pos_hint = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if _is_noun_like(kind, pos_hint):
                if not any(c.get("head_id") == str(j) for c in candidates):
                    same_clause_n = token_to_clause.get(str(j), "") == harf_clause
                    candidates.append({"relation": REL_PP_ATTACH, "head_id": str(j), "score": 0.65 if same_clause_n else 0.5, "reason": "nearest noun left (same clause)" if same_clause_n else "nearest noun left"})
                break
        head_id = None
        head_rule = "PP_ATTACH_proximity_noun"
        if candidates:
            best = max(candidates, key=lambda c: float(c.get("score") or 0))
            head_id = best.get("head_id")
            head_rule = "Pass_B_PP_ATTACH_verb_valency" if (best.get("reason") or "").startswith("L8B") else "Pass_B_PP_ATTACH_noun"
        conf = 0.7
        if head_id is not None:
            best_score = max(float(c.get("score") or 0) for c in candidates) if candidates else 0
            if best_score >= 0.80:
                conf = 0.82
            elif best_score >= 0.60:
                conf = 0.68
            else:
                conf = 0.55
            _add_link(
                dependency_links, corrections_log, head_id, str(harf_id),
                relation=REL_PP_ATTACH, arabic_role=AR_PP_ATTACH, confidence=round(conf, 2),
                rule=head_rule, inferred=True,
            )
        if len(candidates) > 1 or (candidates and float(candidates[0].get("score") or 0) < 0.60):
            ambiguity_log.append({
                "token_id": str(harf_id),
                "candidates": candidates,
                "selected": head_id or "",
                "selection_reason": head_rule,
            })

    # 3) IDAFA: canonical direction mudaf → IDAFA → mudaf_ilayhi only (head=mudaf, dependent=mudaf_ilayhi). Apply weak idafa suppression.
    # Skip only if we already have an IDAFA link for this pair (e.g. from carry-forward), not if the pair is used as PRED.
    idafa_pairs = {(l.get("head_id"), l.get("dependent_id")) for l in dependency_links if l.get("relation") == REL_IDAFA}
    for e in edges:
        if (e.get("relation") or "").strip() != "idafa":
            continue
        from_id = e.get("from_id")
        to_id = e.get("to_id")
        if from_id is None or to_id is None:
            continue
        if (str(from_id), str(to_id)) in idafa_pairs:
            continue
        try:
            mudaf_idx = int(from_id)
        except (TypeError, ValueError):
            continue
        # Weak idafa suppression (L10B rule): if mudaf (from_id) immediately follows a passive verb, suppress.
        prev_idx = mudaf_idx - 1
        l10b_suppression = (e.get("idafa_suppression") or "").strip()
        passive_before = prev_idx >= 0 and (l8b_map.get(prev_idx) or {}).get("voice") == "passive"
        if l10b_suppression or passive_before:
            corrections_log.append({
                "source_l10b_signal": {"type": "idafa_edge", "id": from_id, "value": f"{from_id}->{to_id}"},
                "stage15_decision": {"relation": "IDAFA_suppressed", "head_id": from_id, "dependent_id": to_id},
                "override_reason": "weak idafa suppression (mudaf follows passive verb); same logic as L10B",
                "confidence": 0.75,
                "evidence_signals": ["L10B idafa_suppression" if l10b_suppression else "L8B passive at token_index-1"],
            })
            continue
        _add_link(
            dependency_links, corrections_log, str(from_id), str(to_id),
            relation=REL_IDAFA, arabic_role=AR_MUDAF, confidence=0.75,
            rule="Pass_B_L10B_idafa_edge", inferred=True,
        )
        idafa_pairs.add((str(from_id), str(to_id)))

    # 4) SIFA: head = noun (mawsuf), dependent = adjective (sifa). Direction: noun → SIFA → adjective.
    word_to_kind: Dict[str, str] = {}
    for w in words5:
        word_to_kind[(w.get("word") or "").strip()] = (w.get("kind") or "").strip()
    for i in range(1, len(tokens)):
        kind = word_to_kind.get((tokens[i] or "").strip(), "")
        pos_hint = (node_by_id.get(str(i)) or {}).get("pos_hint") or ""
        if not _is_adjective_like(kind, pos_hint):
            continue
        # Previous noun
        for j in range(i - 1, -1, -1):
            if l8b_map.get(j):
                continue
            k = word_to_kind.get((tokens[j] or "").strip(), "")
            ph = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if _is_noun_like(k, ph):
                _add_link(
                    dependency_links, corrections_log, str(j), str(i),
                    relation=REL_SIFA, arabic_role=AR_NA3T, confidence=0.7,
                    rule="Pass_B_sifa_L5_or_pos_hint", inferred=True,
                )
                break

    # ----- Pass C: Coordination, Apposition, Ambiguity discipline, Candidate markers -----
    coverage = "nominal_verbal_pp_idafa_sifa_coord_appos"
    word_to_kind_pass_c: Dict[str, str] = {}
    for w in words5:
        word_to_kind_pass_c[(w.get("word") or "").strip()] = (w.get("kind") or "").strip()
    candidate_markers: List[Dict[str, Any]] = []  # TAMYIZ_CAND / HAL_CAND — Pass E: expand usage, reduce premature linking
    # Pass E: HAL_CAND — post-verbal adjective-like / indefinite not already SUBJ/OBJ/NAIB
    linked_as_core = {l.get("dependent_id") for l in dependency_links if l.get("relation") in (REL_SUBJ, REL_OBJ, REL_NAIB_SUBJ) and l.get("dependent_id") is not None}
    verb_idx_hal = _first_verb_index(tokens, words5, nodes, l8b_map)
    if verb_idx_hal is not None:
        for i in range(verb_idx_hal + 1, len(tokens)):
            if str(i) in linked_as_core or l8b_map.get(i) or i in excluded_from_root:
                continue
            kind = word_to_kind_pass_c.get((tokens[i] or "").strip(), "")
            pos_hint = (node_by_id.get(str(i)) or {}).get("pos_hint") or ""
            if _is_adjective_like(kind, pos_hint):
                candidate_markers.append({"token_id": str(i), "marker": "HAL_CAND", "surface": (tokens[i] or "").strip()})
    # Pass E: TAMYIZ_CAND — token after quantity-like (number or measure)
    quantity_prefixes = ("كيلو", "كغم", "لتر", "متر", "غرام")
    for i in range(len(tokens) - 1):
        surf_prev = _normalize_surface(tokens[i] or "")
        if surf_prev.isdigit() or any(surf_prev.startswith(q) for q in quantity_prefixes):
            dep_id = str(i + 1)
            if not any(m.get("token_id") == dep_id for m in candidate_markers):
                candidate_markers.append({"token_id": dep_id, "marker": "TAMYIZ_CAND", "surface": (tokens[i + 1] or "").strip()})

    # 5) COORD: head_conjunct → COORD → dependent_conjunct; conjunction → COORD_CONJ → head_conjunct
    for i in range(1, len(tokens) - 1):
        surface_i = (tokens[i] or "").strip()
        if not _is_conjunction_token(surface_i, op_words):
            continue
        head_idx = i - 1
        dep_idx = i + 1
        head_id = str(head_idx)
        dep_id = str(dep_idx)
        conj_id = str(i)
        _add_link(
            dependency_links, corrections_log, head_id, dep_id,
            relation=REL_COORD, arabic_role=AR_ATF, confidence=0.75,
            rule="Pass_C_coordination_conjunction_between", inferred=True,
        )
        _add_link(
            dependency_links, corrections_log, head_id, conj_id,
            relation=REL_COORD_CONJ, arabic_role=AR_ATF_CONJ, confidence=0.75,
            rule="Pass_C_conjunction_attaches_to_head_conjunct", inferred=True,
        )
        # If multiple conjunctions could attach: log ambiguity with ranked candidates
        if i > 1 and _is_conjunction_token((tokens[i - 2] or "").strip(), op_words):
            ambiguity_log.append({
                "token_id": conj_id,
                "candidates": [
                    {"relation": REL_COORD, "head_id": head_id, "score": 0.75, "reason": "immediate_left_conjunct"},
                    {"relation": REL_COORD, "head_id": str(i - 2), "score": 0.5, "reason": "previous_conjunct_chain"},
                ],
                "selected": head_id,
                "selection_reason": "Pass_C_immediate_left_head",
            })

    # 5b) COORD with attached prefix (e.g. وَالْمُسْلِمَاتِ)
    for i in range(1, len(tokens)):
        if _is_conjunction_token((tokens[i] or "").strip(), op_words):
            continue
        if not _has_attached_coord_prefix(tokens[i] or ""):
            continue
        head_idx = _resolve_coord_head_attached_waw(
            i, tokens, word_to_kind_pass_c, node_by_id, token_to_clause, dependency_links, l14_map
        )
        if head_idx is None:
            continue
        head_id = str(head_idx)
        dep_id = str(i)
        if not _is_explicit_waw_coord_conjunct_compatible(
            head_idx, tokens, word_to_kind_pass_c, node_by_id, l14_map
        ) or not _is_explicit_waw_coord_conjunct_compatible(
            i, tokens, word_to_kind_pass_c, node_by_id, l14_map
        ):
            continue
        if token_to_clause.get(head_id, "") != token_to_clause.get(dep_id, ""):
            continue
        # Supersede a prior attached-prefix COORD to this dependent (e.g. intensifier as false head).
        dependency_links[:] = [
            lk
            for lk in dependency_links
            if not (
                (lk.get("relation") or "").strip() == REL_COORD
                and str(lk.get("dependent_id")) == dep_id
                and (lk.get("rule") or "").strip() == "Pass_C_coordination_attached_prefix"
            )
        ]
        _add_link(
            dependency_links, corrections_log, head_id, dep_id,
            relation=REL_COORD, arabic_role=AR_ATF, confidence=0.72,
            rule="Pass_C_coordination_attached_prefix", inferred=True,
        )

    # 6) APPOS: main_noun → APPOS → appositive. Pass E: gate — no APPOS if either token is PP-prefixed, PP-governed, HAL/TAMYIZ, SIFA, or other clause.
    existing_head_dep = {(l.get("head_id"), l.get("dependent_id")) for l in dependency_links}
    dep_ids_majrur = {l.get("dependent_id") for l in dependency_links if l.get("relation") == REL_JAR_MAJRUR}
    head_ids_harf = {l.get("head_id") for l in dependency_links if l.get("relation") == REL_JAR_MAJRUR}
    dep_ids_sifa = {l.get("dependent_id") for l in dependency_links if l.get("relation") == REL_SIFA}
    cand_mark_token_ids = {m.get("token_id") for m in candidate_markers}
    for i in range(len(tokens) - 1):
        if _has_pp_prefix(tokens[i] or "") or _has_pp_prefix(tokens[i + 1] or ""):
            continue
        if _has_attached_coord_prefix(tokens[i] or "") or _has_attached_coord_prefix(tokens[i + 1] or ""):
            continue
        if _has_explicit_coordination_evidence(tokens, op_words, i, i + 1):
            continue
        if has_strong_true_verb_evidence(str(i), tokens[i] or "", lo) or has_strong_true_verb_evidence(
            str(i + 1), tokens[i + 1] or "", lo
        ):
            continue
        if str(i) in head_ids_harf or str(i + 1) in head_ids_harf:
            continue
        kind_i = word_to_kind.get((tokens[i] or "").strip(), "")
        kind_j = word_to_kind.get((tokens[i + 1] or "").strip(), "")
        pos_i = (node_by_id.get(str(i)) or {}).get("pos_hint") or ""
        pos_j = (node_by_id.get(str(i + 1)) or {}).get("pos_hint") or ""
        if not _is_noun_like(kind_i, pos_i) or not _is_noun_like(kind_j, pos_j):
            continue
        l14_i = (l14_map.get(i) or "").strip()
        l14_j = (l14_map.get(i + 1) or "").strip()
        if l14_i == "VERB" or l14_j == "VERB":
            continue
        if l8b_map.get(i) or l8b_map.get(i + 1):
            continue
        if (str(i), str(i + 1)) in existing_head_dep:
            continue
        dep_id = str(i + 1)
        if dep_id in dep_ids_majrur or dep_id in cand_mark_token_ids or dep_id in dep_ids_sifa:
            continue
        if _is_excluded_appos_dependent(tokens[i + 1] or ""):
            continue
        nearest_left_verb: Optional[int] = None
        for j in range(i, -1, -1):
            if not _same_clause(token_to_clause, j, i + 1):
                continue
            k_j = word_to_kind.get((tokens[j] or "").strip(), "")
            pos_j = (node_by_id.get(str(j)) or {}).get("pos_hint") or ""
            if l8b_map.get(j) or _is_verb_like(k_j, pos_j, l8b_map.get(j)):
                nearest_left_verb = j
                break
        if nearest_left_verb is not None and _is_maf3ul_mutlaq_candidate(nearest_left_verb, i + 1, tokens, words5, roots8):
            continue
        if token_to_clause.get(str(i), "") != token_to_clause.get(dep_id, ""):
            continue
        _add_link(
            dependency_links, corrections_log, str(i), dep_id,
            relation=REL_APPOS, arabic_role=AR_BADAL, confidence=0.6,
            rule="Pass_C_apposition_adjacent_nouns_gated", inferred=True,
        )

    _strip_spurious_appos_for_strong_verb_heads(
        tokens, lo, l14_map, dependency_links, corrections_log,
    )
    _strip_false_appos_structural_competition(
        tokens, lo, l14_map, dependency_links, corrections_log, words5, nodes,
    )

    _suppress_conflicting_relations_for_explicit_coordination(dependency_links, corrections_log)

    # Ambiguity log discipline: ensure every entry has required shape
    for a in ambiguity_log:
        if "token_id" not in a:
            a["token_id"] = ""
        if "candidates" not in a:
            a["candidates"] = []
        if "selected" not in a:
            a["selected"] = ""
        if "selection_reason" not in a:
            a["selection_reason"] = "unknown"

    return {
        "dependency_links": dependency_links,
        "root_resolution": {
            "root_id": root_id,
            "root_form": root_form,
            "confidence": round(root_confidence, 2),
            "rule": root_rule,
        },
        "ambiguity_log": ambiguity_log,
        "corrections_log": corrections_log,
        "coverage": coverage,
        "candidate_markers": candidate_markers,
    }
