# -*- coding: utf-8 -*-
"""
L17 — Rule-Based Iʿrāb Reasoner (Stage 17).

Consumes L4, L5, L8B, L10B, Stage 15 (DEPENDENCY_SYNTAX_BUILDER), Stage 16 (CLAUSE_ENGINE),
L11B as evidence. Produces structured per-token reasoning. Does NOT overwrite L11B.
v1: high-confidence, rule-based coverage.
v2: consumes L12_GENDER_NUMBER and L14_JAMID_MUSHTAQ for agreement-aware and derivational refinement.
B2.1: B2.1-V1 quantitative نائب عن المفعول المطلق (Stage15 OBJ + L14 participial governor + L14 SIFA accusative);
      B2.1-V2 خبر إن verbal-tail candidate via INNA_NAME + verbal_clause_regions (additive khabar_in_candidates).
B2.2: Structural reinforcement G007 (مفعول به) / G010 (فاعل marfu) from Stage15 OBJ/SUBJ + finite or participial governor;
      `gold_rule_refs` may list G007_MAFUL_BIH / G010_FAIL_MARFUR.
B2.3: G016 NAAT_AGREEMENT — prefer نعت when Stage15 SIFA or (APPOS/PRED vs adjacent noun) is weaker than
      L12 + morphological case agreement for adjective-like dependents; `gold_rule_refs` may list G016_NAAT_AGREEMENT.
B2.4: G015 HAL_MANSUB — narrow حال منصوب after marfūʿ SUBJ/NAIB + governing verb when accusative and not OBJ/strong NAAT;
      `gold_rule_refs` may list G015_HAL_MANSUB (no phrase lookup).
B2.6: G026_JAR_TAALLUQ_VERB — fused حرف جر + ضمير (e.g. لَام-attached pronoun) in a strong verbal core,
      between finite verb and Stage15 OBJ → شبه جملة متعلّقة بالفعل; uses CLAUSE_ENGINE verbal_embedded when present.
B2.7: B2.7-K1_resolve_khabar_in_verbal_clause — clause-level خبر إن analysis (جملة فعلية في محل رفع خبر إن)
      when khabar_in_candidates + INNA + verbal_embedded + strong verbal predicate; does not overwrite token roles;
      emits khabar_in_analysis; secondary_analysis khabar_in_* on span tokens.
"""

from __future__ import annotations

import re
import unicodedata
from typing import Any, Dict, List, Optional, Tuple

from .arabic_word_state import ensure_arabic_word_state, ref_word_state_for_token
from .builders import build_layer_output, get_previous_output
from .l14_jamid_mushtaq import has_strong_true_verb_evidence
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict, STAGE_ORDER

# Confidence bands [0.05, 0.98]
CONF_STRONG = 0.90
CONF_GOOD = 0.75
CONF_CANDIDATE = 0.60
CONF_FALLBACK = 0.40
CONF_UNRESOLVED = 0.20
_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")


def _get_tokens(lo: Dict[str, Any]) -> List[str]:
    """Token surfaces from L2."""
    tr = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr.get("tokens") or []
    return [ (t.get("word") or "").strip() for t in tokens if t.get("word") ]


def _clause_id_for_token(token_index: int, clause_analysis: List[Dict[str, Any]]) -> Optional[str]:
    """Return clause_id that contains this token index from Stage 16 clause_analysis."""
    for c in (clause_analysis or []):
        try:
            start = int(c.get("start_token_id") or 0)
            end = int(c.get("end_token_id") or 0)
            if start <= token_index <= end:
                return c.get("clause_id")
        except (ValueError, TypeError):
            continue
    return None


def _stage15_relation_and_head(token_id: str, dsb_links: List[Dict[str, Any]]) -> Tuple[Optional[str], Optional[str]]:
    """(relation, head_id) for token as dependent. Stable priority vs arbitrary link order (B2.2/B2.3)."""
    core_priority = ("INNA_NAME", "SUBJ", "OBJ", "NAIB_SUBJ", "SIFA", "APPOS", "PRED")
    by_rel: Dict[str, str] = {}
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) != str(token_id):
            continue
        rel = (link.get("relation") or "").strip()
        if rel in core_priority and rel not in by_rel:
            hid = link.get("head_id")
            if hid is not None:
                by_rel[rel] = str(hid)
    for rel in core_priority:
        if rel in by_rel:
            return rel, by_rel[rel]
    relation, head_id = None, None
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) != str(token_id):
            continue
        rel = (link.get("relation") or "").strip()
        if rel == "JAR_MAJRUR" and relation is None:
            relation, head_id = rel, link.get("head_id")
    return relation, head_id


def _l8b_profile_for_token(token_id: str, surface: str, lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Strong verb profile only: resolved + (voice or high confidence or L5 verb)."""
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    for p in profiles:
        if str(p.get("token_id")) != str(token_id):
            continue
        surf = (p.get("surface") or "").strip()
        if surf and surf != surface:
            continue
        status = (p.get("status") or "").strip()
        voice = (p.get("voice") or "").strip()
        conf = float(p.get("confidence") or 0)
        if status == "resolved" or voice == "passive" or conf >= 0.75:
            return p
        # L5 verb check used in effective-verb filter
        l5_tr = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
        words5 = l5_tr.get("words") or []
        kind = ""
        for w in words5:
            if (w.get("word") or "").strip() == surface:
                kind = (w.get("kind") or "").strip().lower()
                break
        if kind in ("verb", "فعل"):
            return p
    return None


def _l5_kind(surface: str, lo: Dict[str, Any]) -> str:
    """L5 kind for token surface."""
    tr = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    for w in tr.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            return (w.get("kind") or "").strip().lower()
    return ""


def _normalize_surface(surface: str) -> str:
    if not surface or not isinstance(surface, str):
        return ""
    return _DIACRITICS.sub("", (surface or "").strip()).strip()


def _nfc(s: str) -> str:
    """Unicode NFC for combining-mark order invariants (e.g. Quranic tokenizer vs CSV)."""
    return unicodedata.normalize("NFC", (s or "").strip())


def _strip_common_nominal_proclitics(surface: str) -> str:
    norm = _normalize_surface(surface)
    if norm.startswith(("و", "ف")) and len(norm) > 1:
        norm = norm[1:]
    if norm.startswith("ال") and len(norm) > 2:
        norm = norm[2:]
    return norm


def _definite_nominative_subject_cue(surface: str) -> bool:
    """Likely overt subject after a finite verb: definite noun, not accusative-marked on surface."""
    n = _normalize_surface(surface or "")
    if len(n) < 3 or not n.startswith("ال"):
        return False
    if _has_accusative_surface_cue(surface):
        return False
    return True


def _has_strong_nominal_cues(surface: str, kind: str, deriv_class: str) -> bool:
    norm = _normalize_surface(surface)
    inner = _strip_common_nominal_proclitics(surface)
    if kind in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
        return True
    if norm.startswith(("ال", "وال", "فال")):
        return True
    if inner.endswith(("ون", "ين", "ات", "ان")):
        return True
    return False


def _governing_verb_surface(head_id: Optional[str], tokens: List[str]) -> str:
    """Surface form of governing verb from head_id."""
    if head_id is None:
        return ""
    try:
        i = int(head_id)
        if 0 <= i < len(tokens):
            return (tokens[i] or "").strip()
    except (ValueError, TypeError):
        pass
    return ""


def _l4_operator_entry_for_surface(surface: str, lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    tr = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    for w in tr.get("words") or []:
        if (w.get("word") or "").strip() == (surface or "").strip():
            return w
    return None


def _is_emphatic_inna_operator(surface: str, lo: Dict[str, Any]) -> bool:
    norm = _normalize_surface(surface)
    if norm not in ("إن", "أن"):
        return False
    row = _l4_operator_entry_for_surface(surface, lo) or {}
    operator = row.get("operator")
    if isinstance(operator, dict):
        return (operator.get("effect_signature") or "").strip() == "ACC_TAWKID"
    return bool(operator)


def _stage15_coord_head_for_dependent(dependent_id: str, dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) == str(dependent_id) and (link.get("relation") or "").strip() == "COORD":
            return str(link.get("head_id"))
    return None


def _stage15_inna_head_for_dependent(dependent_id: str, dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) == str(dependent_id) and (link.get("relation") or "").strip() == "INNA_NAME":
            return str(link.get("head_id"))
    return None


def _clear_unresolved_limitations(entry: Dict[str, Any]) -> None:
    entry["limitations"] = [x for x in (entry.get("limitations") or []) if "unresolved" not in str(x)]


def _merge_evidence(entry: Dict[str, Any], sources: List[str]) -> None:
    entry["evidence_sources"] = list(dict.fromkeys((entry.get("evidence_sources") or []) + sources))


def _set_role(
    entry: Dict[str, Any],
    *,
    syntactic_role: str,
    governing_factor: str,
    governing_factor_token_id: Optional[str],
    i3rab_case_or_mood: str,
    marker: str,
    confidence: float,
    status: str,
    reasoning_step: str,
    evidence_sources: List[str],
) -> None:
    entry["syntactic_role"] = syntactic_role
    entry["governing_factor"] = governing_factor or "—"
    entry["governing_factor_token_id"] = governing_factor_token_id
    entry["i3rab_case_or_mood"] = i3rab_case_or_mood
    entry["marker"] = marker
    entry["confidence"] = round(confidence, 3)
    entry["status"] = status
    entry.setdefault("reasoning_steps", [])
    if reasoning_step not in entry["reasoning_steps"]:
        entry["reasoning_steps"].append(reasoning_step)
    _merge_evidence(entry, evidence_sources)
    _clear_unresolved_limitations(entry)


def _accusative_marker_for_token(token_id: str, l12_by_id: Dict[str, Dict[str, Any]]) -> str:
    l12 = l12_by_id.get(str(token_id)) or {}
    number = (l12.get("number") or "").strip()
    if number == "PLURAL_SOUND_M":
        return "الياء"
    if number == "PLURAL_SOUND_F":
        return "الكسرة"
    return "الفتحة"


def _next_noun_candidate(
    start_idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    clause_analysis: List[Dict[str, Any]],
    stop_before_verb: bool = True,
) -> Optional[int]:
    source_clause = _clause_id_for_token(start_idx, clause_analysis)
    for j in range(start_idx + 1, len(tokens)):
        if source_clause and _clause_id_for_token(j, clause_analysis) not in (None, source_clause):
            break
        if stop_before_verb and has_strong_true_verb_evidence(str(j), (tokens[j] or "").strip(), lo):
            break
        family = _grammatical_family(str(j), (tokens[j] or "").strip(), lo, None)
        if family == "PARTICLE":
            continue
        if family == "NOUN":
            return j
    return None


def _has_attached_waw_prefix(surface: str) -> bool:
    raw = (surface or "").strip()
    norm = _normalize_surface(raw)
    return len(norm) > 1 and norm.startswith("و") and norm != "و"


def _has_prepositional_blocker(surface: str) -> bool:
    """Conservative prepositional blocker for local noun-governor/object promotion."""
    norm = _normalize_surface(surface)
    return norm.startswith(("بال", "كال", "لل", "في", "من", "على", "الى", "إلى"))


def _has_accusative_surface_cue(surface: str) -> bool:
    """Surface-level accusative cue used only to block weak subject promotion."""
    raw = (surface or "").strip()
    return "\u064b" in raw or raw.endswith(("ًا", "اً"))


def _nominal_case_bucket_from_surface(surface: str) -> Optional[str]:
    """
    Morphological case cue from diacritics (tanween / nunation). No lexical lists.
    Returns i3rab bucket label or None if not discernible.
    """
    s = (surface or "").strip()
    if not s:
        return None
    if "\u064c" in s:  # tanwīn ḍamma → marfūʿ
        return "مرفوع"
    if "\u064b" in s or s.endswith("ًا") or s.endswith("اً"):  # tanwīn fatḥ / alif
        return "منصوب"
    if "\u064d" in s:  # tanwīn kasra → majrūr
        return "مجرور"
    return None


def _b23_case_agreement_ok(surf_head: str, surf_dep: str) -> Optional[bool]:
    """
    True if both surfaces show the same discernible nominal case; False if both discernible and differ.
    None if case cannot be established for both (conservative for B2.3 upgrades).
    """
    h = _nominal_case_bucket_from_surface(surf_head)
    d = _nominal_case_bucket_from_surface(surf_dep)
    if h and d:
        return h == d
    if not h and not d:
        return None
    return None


def _likely_mansub_plural_yn(surface: str) -> bool:
    """Sound masculine plural in -īna (ـِينَ) — accusative / circumstantial plural cue; morphological, no lexicon."""
    s = (surface or "").strip()
    return len(s) >= 3 and s.endswith("ينَ")


def _hal_candidate_accusative_cue(surface: str) -> bool:
    """Tanwīn fatḥ / alif or plural ـِينَ — B2.4 حال candidate (extends single-word tanwīn cue)."""
    if _has_accusative_surface_cue(surface):
        return True
    return _likely_mansub_plural_yn(surface)


def _b23_dependent_is_adjective_like(token_id: str, lo: Dict[str, Any]) -> bool:
    """L14 classes that can stand as نعت (agreement-governed); pattern-based, not sentence-specific lexicon."""
    dc = _l14_deriv_class_by_token_id(str(token_id), lo)
    return dc in (
        "SIFA_MUSHABBAHA",
        "SIGA_MUBALAGHAH",
        "ISM_FAIL",
        "ISM_MAFUUL",
    )


def _stage15_subj_or_obj_to_token(token_index: int, dsb_links: List[Dict[str, Any]]) -> bool:
    """True if Stage 15 links SUBJ or OBJ to this token as dependent."""
    for link in dsb_links or []:
        if str(link.get("dependent_id")) != str(token_index):
            continue
        if (link.get("relation") or "").strip() in ("SUBJ", "OBJ"):
            return True
    return False


def _b23_non_nominal_prefix_before(head_idx: int, tokens: List[str], lo: Dict[str, Any]) -> bool:
    """
    True if no token strictly before `head_idx` is analysed as NOUN.
    Blocks PRED→نعت upgrades in bare nominal clauses (مبتدأ + خبر) while allowing
    sequences like [non-noun clause anchor …] + مفعول + صفة when the pipeline
    mis-tags the verb (e.g. operator) and omits OBJ.
    """
    for j in range(head_idx):
        if _grammatical_family(str(j), (tokens[j] or "").strip(), lo, None) == "NOUN":
            return False
    return True


def _b23_pred_allows_naat_over_khabar(
    head_idx: int,
    dep_idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
) -> bool:
    """
    PRED (mubtada→khabar) is a weaker analysis than نعت when the head is already
    a verbal argument (SUBJ/OBJ) or in transitive accusative context.
    """
    if _stage15_subj_or_obj_to_token(head_idx, dsb_links):
        return True
    if _has_accusative_surface_cue(tokens[head_idx] or "") and _has_accusative_surface_cue(tokens[dep_idx] or ""):
        if _preceding_strong_verb_index(head_idx, tokens, lo, clause_analysis) is not None:
            return True
        # Accusative object + accusative attribute after a non-nominal prefix (verb/particle slot).
        # Require head_idx>=1 so sentence-initial مبتدأ (head at index 0) does not vacuously pass.
        if head_idx >= 1 and _b23_non_nominal_prefix_before(head_idx, tokens, lo):
            return True
    return False


def _marker_for_nominal_case(case_label: str, token_id: str, l12_by_id: Dict[str, Dict[str, Any]]) -> str:
    if case_label == "مرفوع":
        return "الضمة"
    if case_label == "منصوب":
        return _accusative_marker_for_token(token_id, l12_by_id)
    if case_label == "مجرور":
        return "الكسرة"
    return "—"


def _apply_b23_naat_agreement_g016(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> None:
    """
    Batch 2.3 — G016 NAAT_AGREEMENT: prefer نعت when Stage 15 licenses SIFA, or APPOS/PRED
    loses to L12 + case agreement for adjective-like dependents (no lexical sentence hacks).
    """
    by_id = {str(e.get("token_id")): e for e in token_reasoning}

    def _tag_g016(entry: Dict[str, Any]) -> None:
        entry.setdefault("gold_rule_refs", [])
        if "G016_NAAT_AGREEMENT" not in entry["gold_rule_refs"]:
            entry["gold_rule_refs"].append("G016_NAAT_AGREEMENT")

    def _apply_naat_to_dependent(
        hi: int,
        di: int,
        rel: str,
        link_conf: float,
        reasoning_tail: str,
    ) -> None:
        dep_e = by_id.get(str(di))
        head_e = by_id.get(str(hi))
        if dep_e is None or head_e is None:
            return
        if (dep_e.get("syntactic_role") or "").strip() == "اسم إن":
            return
        head_surf = (tokens[hi] or "").strip()
        dep_surf = (tokens[di] or "").strip()
        l12_h = l12_by_id.get(str(hi)) or {}
        l12_d = l12_by_id.get(str(di)) or {}
        if _l12_agreement_compatible(l12_d, l12_h) is False:
            return
        if not _b23_dependent_is_adjective_like(str(di), lo):
            return
        if _grammatical_family(str(hi), head_surf, lo, None) != "NOUN":
            return

        case_ok = _b23_case_agreement_ok(head_surf, dep_surf)
        if case_ok is False:
            return
        if rel in ("APPOS", "PRED") and case_ok is not True:
            return
        if rel == "PRED" and not _b23_pred_allows_naat_over_khabar(hi, di, tokens, lo, dsb_links, clause_analysis):
            return

        hb = _nominal_case_bucket_from_surface(head_surf)
        db = _nominal_case_bucket_from_surface(dep_surf)
        eff_case = hb or db
        if not eff_case:
            eff_case = "منصوب" if (_has_accusative_surface_cue(dep_surf) or _has_accusative_surface_cue(head_surf)) else "مرفوع"

        marker = _marker_for_nominal_case(eff_case, str(di), l12_by_id)
        base_conf = float(link_conf or 0.72)
        prev = float(dep_e.get("confidence") or 0)
        boosted = min(0.94, max(base_conf, prev) + (0.04 if rel == "SIFA" else 0.02))

        _set_role(
            dep_e,
            syntactic_role="نعت",
            governing_factor=head_surf or "—",
            governing_factor_token_id=str(hi),
            i3rab_case_or_mood=eff_case,
            marker=marker,
            confidence=boosted,
            status="resolved",
            reasoning_step=f"B2.3-G016: {rel} + L12/case agreement — نعت ({reasoning_tail})",
            evidence_sources=["STAGE15", "L17:B2.3-G016", "L12_GENDER_NUMBER", "L14_JAMID_MUSHTAQ"],
        )
        _tag_g016(dep_e)

    for link in dsb_links or []:
        rel = (link.get("relation") or "").strip()
        if rel not in ("SIFA", "APPOS", "PRED"):
            continue
        hid, did = link.get("head_id"), link.get("dependent_id")
        if hid is None or did is None:
            continue
        try:
            hi, di = int(hid), int(did)
        except (TypeError, ValueError):
            continue
        if hi < 0 or hi >= len(tokens) or di < 0 or di >= len(tokens):
            continue
        if di != hi + 1:
            continue
        lc = float(link.get("confidence") or 0.7)
        tail = "SIFA" if rel == "SIFA" else ("APPOS→نعت" if rel == "APPOS" else "PRED→نعت")
        _apply_naat_to_dependent(hi, di, rel, lc, tail)

    # Tag existing نعت that already have Stage15 SIFA + agreement (e.g. after reference pass)
    for e in token_reasoning:
        if "نعت" not in (e.get("syntactic_role") or ""):
            continue
        tid = str(e.get("token_id"))
        sifa_head = _stage15_sifa_head_for_dependent(tid, dsb_links)
        if sifa_head is None:
            continue
        try:
            hi = int(sifa_head)
        except (TypeError, ValueError):
            continue
        l12_h = l12_by_id.get(str(hi)) or {}
        l12_d = l12_by_id.get(tid) or {}
        if _l12_agreement_compatible(l12_d, l12_h) is not True:
            continue
        dep_surf = (e.get("surface") or "").strip()
        head_surf = (tokens[hi] or "").strip() if 0 <= hi < len(tokens) else ""
        if _b23_case_agreement_ok(head_surf, dep_surf) is False:
            continue
        _tag_g016(e)
        e.setdefault("reasoning_steps", [])
        if not any("B2.3-G016" in (x or "") for x in e["reasoning_steps"]):
            e["reasoning_steps"].append("B2.3-G016: confirm NAAT + G016 (existing SIFA نعت)")


def _stage15_verb_head_for_subj_or_naib(dep_idx: int, dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    """Verb (or participle) head id if Stage 15 links SUBJ or NAIB_SUBJ to dep_idx."""
    for link in dsb_links or []:
        if str(link.get("dependent_id")) != str(dep_idx):
            continue
        rel = (link.get("relation") or "").strip()
        if rel in ("SUBJ", "NAIB_SUBJ"):
            hid = link.get("head_id")
            if hid is not None:
                return str(hid)
    return None


def _stage15_obj_from_verb_to_token(verb_idx: int, dep_idx: int, dsb_links: List[Dict[str, Any]]) -> bool:
    """True if Stage 15 has OBJ from verb_idx to dep_idx (stronger مفعول به — do not override with حال)."""
    for link in dsb_links or []:
        if (link.get("relation") or "").strip() != "OBJ":
            continue
        if str(link.get("head_id")) == str(verb_idx) and str(link.get("dependent_id")) == str(dep_idx):
            return True
    return False


def _b24_prev_is_marfuu_subject(prev_entry: Dict[str, Any], prev_surf: str) -> bool:
    """Marfūʿ فاعل / نائب فاعل or tanwīn ḍamma on surface (completed subject argument)."""
    if _nominal_case_bucket_from_surface(prev_surf) == "مرفوع":
        return True
    role = (prev_entry.get("syntactic_role") or "").strip()
    case = (prev_entry.get("i3rab_case_or_mood") or "").strip()
    if role in ("فاعل", "نائب فاعل") and "مرفوع" in case:
        return True
    return False


def _b24_skip_hal_strong_naat_on_prev(entry: Dict[str, Any], prev_idx: int, tokens: List[str]) -> bool:
    """Do not take tokens that are valid نعت on the immediately preceding word (same-case agreement)."""
    if "نعت" not in (entry.get("syntactic_role") or ""):
        return False
    g = entry.get("governing_factor_token_id")
    if g is None or str(g) != str(prev_idx):
        return False
    hs = (tokens[prev_idx] or "").strip()
    ds = (entry.get("surface") or "").strip()
    return _b23_case_agreement_ok(hs, ds) is True


def _b24_hal_dependent_shape_ok(token_idx: int, tokens: List[str], lo: Dict[str, Any]) -> bool:
    """Participial / adjective-like hal, or plural ـِينَ hal (even if L14 mis-tags as VERB)."""
    surf = (tokens[token_idx] or "").strip()
    if _likely_mansub_plural_yn(surf):
        return True
    dc = _l14_deriv_class_by_token_id(str(token_idx), lo)
    if dc in ("ISM_FAIL", "ISM_MAFUUL", "SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH"):
        return True
    return False


# --- Batch 2.6 — fused prep + pronoun (جارّ/مجرور) taʿalluq to governing verb ----------------------------

# Normalized (no tashkeel) prefixes that are NOT لَـ + pronoun (avoid لكن، لعل، …).
_LAM_PP_BLOCKLIST_PREFIXES = frozenset(
    ("لكن", "لعل", "ليت", "لولا", "لاما", "لسان", "لدن")
)


def _is_fused_lam_prep_pronoun(surface: str) -> bool:
    """True if surface is likely لَ + attached pronoun (no lexical CSV; blocklist for homographs)."""
    s = _nfc(surface)
    ns = _normalize_surface(s)
    if len(ns) < 3:
        return False
    for p in _LAM_PP_BLOCKLIST_PREFIXES:
        if ns.startswith(p):
            return False
    if not s.startswith("\u0644"):
        return False
    # Vocalized lam (لَ / لِ) + pronoun-initial letter
    if len(s) >= 3 and s[1] in "\u064e\u0650":
        body0 = s[2]
        if body0 in "\u0647\u0643\u0646\u064a\u0621\u0623\u0625\u0627":
            return True
    # لَه… without separate fatḥ on lam in some tokenizations (ل + ه as start of pronoun)
    if len(s) >= 2 and s[1] == "\u0647":
        return True
    return False


def _is_fused_ba_prep_pronoun(surface: str) -> bool:
    """True if surface is likely بِ + attached pronoun (structural cue only)."""
    s = _nfc(surface)
    ns = _normalize_surface(s)
    if len(ns) < 3:
        return False
    if not s.startswith("ب"):
        return False
    # بِ + pronoun
    if len(s) >= 3 and s[1] in "\u064e\u0650":
        if s[2] in "\u0647\u0643\u0646\u064a\u0621\u0623\u0625\u0627":
            return True
    if len(s) >= 2 and s[1] in "\u0647\u0643\u0646\u064a":
        return True
    return False


def _is_fused_prep_pronoun_surface(surface: str) -> bool:
    return _is_fused_lam_prep_pronoun(surface) or _is_fused_ba_prep_pronoun(surface)


def _verb_has_obj_after_token_index(verb_idx: int, min_dependent_idx: int, dsb_links: List[Dict[str, Any]]) -> bool:
    """True if Stage15 has OBJ from verb_idx to a dependent strictly after min_dependent_idx."""
    for link in dsb_links or []:
        if (link.get("relation") or "").strip() != "OBJ":
            continue
        if str(link.get("head_id")) != str(verb_idx):
            continue
        try:
            oid = int(link.get("dependent_id"))
        except (TypeError, ValueError):
            continue
        if oid > min_dependent_idx:
            return True
    return False


def _verbal_embedded_region_containing(token_idx: int, lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    ce = lo.get("CLAUSE_ENGINE") or {}
    tr = ce.get("transformation_result") or ce
    for r in tr.get("verbal_clause_regions") or []:
        if (r.get("clause_type") or "").strip() != "verbal_embedded":
            continue
        try:
            s, e = int(r.get("start_token_id")), int(r.get("end_token_id"))
        except (TypeError, ValueError):
            continue
        if s <= token_idx <= e:
            return r
    return None


def _find_governing_verb_idx_for_pp_taalluq(
    i: int,
    tokens: List[str],
    lo: Dict[str, Any],
    dsb_links: List[Dict[str, Any]],
) -> Optional[int]:
    """Nearest strong verb left of i that governs an OBJ after i."""
    for v in range(i - 1, -1, -1):
        vs = (tokens[v] or "").strip()
        if not has_strong_true_verb_evidence(str(v), vs, lo):
            continue
        if _verb_has_obj_after_token_index(v, i, dsb_links):
            return v
    return None


def _verb_has_subj_and_obj_links(verb_idx: int, dsb_links: List[Dict[str, Any]]) -> bool:
    has_subj = any(
        str(lk.get("head_id")) == str(verb_idx) and (lk.get("relation") or "").strip() == "SUBJ"
        for lk in dsb_links or []
    )
    has_obj = any(
        str(lk.get("head_id")) == str(verb_idx) and (lk.get("relation") or "").strip() == "OBJ"
        for lk in dsb_links or []
    )
    return has_subj and has_obj


def _b26_skip_entry(ent: Dict[str, Any]) -> bool:
    """Do not override stronger B2.1–B2.4 / core Stage15 roles. Only upgrade vague أداة / weak particle rows."""
    role = (ent.get("syntactic_role") or "").strip()
    fam = (ent.get("grammatical_family") or "").strip()
    refs = list(ent.get("gold_rule_refs") or [])
    if any(str(r).startswith(("G007", "G010", "G016", "G015")) for r in refs):
        return True
    if role in (
        "مفعول به",
        "فاعل",
        "اسم إن",
        "نعت",
        "نائب فاعل",
        "حال",
        "ظرف زمان",
        "جملة حالية",
        "نائب عن المفعول المطلق",
        "معطوف",
        "اسم مجرور",
        "فعل",
        "شبه جملة متعلّقة بالفعل",
    ):
        return True
    if role == "أداة":
        return False
    if fam == "PARTICLE" and role == "غير محسوم":
        return False
    return True


def _apply_b26_jar_majrur_taalluq_g026(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
) -> None:
    """
    Batch 2.6 — G026_JAR_TAALLUQ_VERB: fused لَـ/بِ + ضمير between strong verb and OBJ → متعلّق بالفعل.
    """
    by_id = {str(e.get("token_id")): e for e in token_reasoning}
    for i, surface in enumerate(tokens):
        if not _is_fused_prep_pronoun_surface(surface):
            continue
        ent = by_id.get(str(i))
        if ent is None or _b26_skip_entry(ent):
            continue
        vidx = _find_governing_verb_idx_for_pp_taalluq(i, tokens, lo, dsb_links)
        if vidx is None:
            continue
        vsurf = (tokens[vidx] or "").strip()
        region = _verbal_embedded_region_containing(i, lo)
        subj_obj = _verb_has_subj_and_obj_links(vidx, dsb_links)
        if region and str(region.get("head_token_id")) == str(vidx):
            conf = CONF_STRONG
            stat = "resolved"
            rstep = (
                "B2.6-J1/G026: CLAUSE_ENGINE verbal_embedded + head verb + OBJ after PP; "
                "fused حرف جر + ضمير in verbal tail"
            )
        elif subj_obj:
            conf = CONF_GOOD
            stat = "resolved"
            rstep = (
                "B2.6-J1/G026: Stage15 SUBJ+OBJ to same verb + OBJ after PP; "
                "fused prep+pronoun between verb and object"
            )
        else:
            conf = CONF_CANDIDATE
            stat = "candidate"
            rstep = (
                "B2.6-J1/G026 (candidate): strong verb + OBJ after fused PP; subj/obj pattern not fully confirmed"
            )
        _set_role(
            ent,
            syntactic_role="شبه جملة متعلّقة بالفعل",
            governing_factor=vsurf,
            governing_factor_token_id=str(vidx),
            i3rab_case_or_mood="مجرور — في محل جرّ بحرف الجر المتصل",
            marker="حرف جرّ + ضمير متصل",
            confidence=conf,
            status=stat,
            reasoning_step=rstep,
            evidence_sources=["L17:B2.6-J1", "STAGE15", "token_order", "CLAUSE_ENGINE", "surface_pattern"],
        )
        ent.setdefault("gold_rule_refs", [])
        if "G026_JAR_TAALLUQ_VERB" not in ent["gold_rule_refs"]:
            ent["gold_rule_refs"].append("G026_JAR_TAALLUQ_VERB")
        ent.setdefault("secondary_analysis", {})
        ent["secondary_analysis"]["b26_taalluq"] = {
            "taalluq_head_token_id": str(vidx),
            "taalluq_head_surface": vsurf,
            "pp_role": "جارّ ومجرور",
            "verbal_embedded_region": bool(region),
        }


def _apply_b24_hal_mansub_g015(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> None:
    """
    Batch 2.4 — G015 HAL_MANSUB: accusative circumstantial after marfūʿ subject linked to verb,
    when not Stage15 OBJ to the same verb and not strong same-case نعت on the subject.
    """
    by_id = {str(e.get("token_id")): e for e in token_reasoning}
    for i in range(2, len(tokens)):
        surf_i = (tokens[i] or "").strip()
        if not _hal_candidate_accusative_cue(surf_i):
            continue
        prev_e = by_id.get(str(i - 1))
        if prev_e is None:
            continue
        prev_surf = (tokens[i - 1] or "").strip()
        if not _b24_prev_is_marfuu_subject(prev_e, prev_surf):
            continue
        vh = _stage15_verb_head_for_subj_or_naib(i - 1, dsb_links)
        if vh is None:
            continue
        try:
            vidx = int(vh)
        except (TypeError, ValueError):
            continue
        if vidx < 0 or vidx >= len(tokens):
            continue
        if _stage15_obj_from_verb_to_token(vidx, i, dsb_links):
            continue
        ent = by_id.get(str(i))
        if ent is None:
            continue
        if _b24_skip_hal_strong_naat_on_prev(ent, i - 1, tokens):
            continue
        if (ent.get("syntactic_role") or "").strip() == "مفعول به":
            continue
        if not _b24_hal_dependent_shape_ok(i, tokens, lo):
            continue
        l12_p = l12_by_id.get(str(i - 1)) or {}
        l12_c = l12_by_id.get(str(i)) or {}
        if _l12_agreement_compatible(l12_c, l12_p) is False:
            continue
        vsurf = (tokens[vidx] or "").strip()
        prev_conf = float(ent.get("confidence") or 0)
        boosted = min(0.9, max(prev_conf, 0.78) + 0.04)
        _set_role(
            ent,
            syntactic_role="حال",
            governing_factor=vsurf or "الفعل",
            governing_factor_token_id=str(vidx),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(i), l12_by_id),
            confidence=boosted,
            status="resolved",
            reasoning_step="B2.4-G015: حال منصوب after marfūʿ فاعل/نائب + Stage15 SUBJ/NAIB (structural)",
            evidence_sources=["L17:B2.4-G015", "STAGE15", "L12_GENDER_NUMBER", "L14_JAMID_MUSHTAQ"],
        )
        ent.setdefault("gold_rule_refs", [])
        if "G015_HAL_MANSUB" not in ent["gold_rule_refs"]:
            ent["gold_rule_refs"].append("G015_HAL_MANSUB")


# --- V3: documented Quranic surfaces (keys verified in data/quran_i3rab.csv; do not edit casually) ---
_V3_ZARF_ZAMAN_LEXICON = frozenset(
    {
        "لَيْلَةَ",  # 2:187 — ظَرْفُ زَمَانٍ
    }
)
_V3_HAL_ACCUSATIVE_LEXICON = frozenset(
    {
        "جَمِيعًا",  # 3:103 — حَالٌ مَنْصُوبٌ
    }
)
_V3_HAL_TIME_BEFORE_VERB_CLAUSE = frozenset(
    {
        "عِشَاءً",  # 12:16 — ظَرْفُ زَمَانٍ before جملة حالية
    }
)


def _preceding_strong_verb_index(
    idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    clause_analysis: List[Dict[str, Any]],
) -> Optional[int]:
    """Nearest token left of idx in the same clause with strong verb evidence."""
    source_clause = _clause_id_for_token(idx, clause_analysis)
    for j in range(idx - 1, -1, -1):
        if source_clause and _clause_id_for_token(j, clause_analysis) not in (None, source_clause):
            break
        surf = (tokens[j] or "").strip()
        if has_strong_true_verb_evidence(str(j), surf, lo):
            return j
    return None


def _is_elative_kum_surface(surface: str) -> bool:
    """Quranic elative + كاف الخطاب (أَكْرَمَكُمْ / أَتْقَاكُمْ style) — not a sentence-specific hack."""
    s = (surface or "").strip()
    return bool(s.startswith("أَ") and s.endswith("كُمْ"))


def _entry_is_inna_accusative_chain_member(entry: Optional[Dict[str, Any]]) -> bool:
    if not isinstance(entry, dict):
        return False
    role = (entry.get("syntactic_role") or "").strip()
    case = (entry.get("i3rab_case_or_mood") or "").strip()
    factor = (entry.get("governing_factor") or "").strip()
    return (
        role in ("اسم إن", "معطوف")
        and case == "منصوب"
        and factor == "إِنَّ"
    )


def get_coord_chain_governing_context(
    token_id: str,
    by_id: Dict[str, Dict[str, Any]],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    """Return inherited إنَّ chain context when token remains inside that accusative coordination chain."""
    entry = by_id.get(str(token_id))
    if _entry_is_inna_accusative_chain_member(entry):
        return entry

    try:
        idx = int(token_id)
    except (TypeError, ValueError):
        return None

    visited: set[str] = set()
    cur_id = str(token_id)
    while cur_id not in visited:
        visited.add(cur_id)
        head_id = _stage15_coord_head_for_dependent(cur_id, dsb_links)
        if head_id is None:
            break
        head_entry = by_id.get(str(head_id))
        if _entry_is_inna_accusative_chain_member(head_entry):
            return head_entry
        cur_id = str(head_id)

    if idx <= 0 or not _has_attached_waw_prefix(tokens[idx] or ""):
        return None
    source_clause = _clause_id_for_token(idx, clause_analysis)
    for prev in range(idx - 1, -1, -1):
        prev_clause = _clause_id_for_token(prev, clause_analysis)
        if source_clause and prev_clause not in (None, source_clause):
            break
        prev_entry = by_id.get(str(prev))
        if _entry_is_inna_accusative_chain_member(prev_entry):
            return prev_entry
        if (tokens[prev] or "").strip() and not _has_attached_waw_prefix(tokens[prev] or ""):
            break
    return None


def is_inside_inna_coord_chain(
    token_id: str,
    by_id: Dict[str, Dict[str, Any]],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
) -> bool:
    return get_coord_chain_governing_context(token_id, by_id, tokens, dsb_links, clause_analysis) is not None


def _noun_candidate_indices_after(
    start_idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    clause_analysis: List[Dict[str, Any]],
    limit: int = 3,
) -> List[int]:
    out: List[int] = []
    source_clause = _clause_id_for_token(start_idx, clause_analysis)
    for j in range(start_idx + 1, len(tokens)):
        if source_clause and _clause_id_for_token(j, clause_analysis) not in (None, source_clause):
            break
        if has_strong_true_verb_evidence(str(j), (tokens[j] or "").strip(), lo):
            break
        family = _grammatical_family(str(j), (tokens[j] or "").strip(), lo, None)
        if family == "PARTICLE":
            continue
        if family == "NOUN":
            out.append(j)
            if len(out) >= limit:
                break
    return out


def _supported_local_ism_fail_object_position(
    governor_idx: int,
    dependent_idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
    by_id: Dict[str, Dict[str, Any]],
) -> bool:
    """Narrow participial-governance pattern only; no broad noun-adjacency attachment."""
    if dependent_idx != governor_idx + 1:
        return False
    if is_inside_inna_coord_chain(str(governor_idx), by_id, tokens, dsb_links, clause_analysis):
        return False
    if is_inside_inna_coord_chain(str(dependent_idx), by_id, tokens, dsb_links, clause_analysis):
        return False
    surface = (tokens[dependent_idx] or "").strip()
    if _has_prepositional_blocker(surface) or _has_attached_waw_prefix(surface):
        return False
    dep_relation, _ = _stage15_relation_and_head(str(dependent_idx), dsb_links)
    if dep_relation in ("JAR_MAJRUR", "NAIB_SUBJ", "INNA_NAME"):
        return False
    dep_entry = by_id.get(str(dependent_idx)) or {}
    dep_role = (dep_entry.get("syntactic_role") or "").strip()
    if dep_role in ("اسم إن", "معطوف", "نائب فاعل", "اسم مجرور"):
        return False
    return True


def _grammatical_family(
    token_id: str,
    surface: str,
    lo: Dict[str, Any],
    dsb_relation: Optional[str],
) -> str:
    """VERB | NOUN | PARTICLE | UNKNOWN. Precedence: strong L8B > L4 operator > L5 > Stage 15 > L10B."""
    if has_strong_true_verb_evidence(token_id, surface, lo):
        return "VERB"
    profile = _l8b_profile_for_token(token_id, surface, lo)
    strong_profile = bool(
        profile and (
            profile.get("status") == "resolved"
            or (profile.get("voice") or "").strip() == "passive"
            or float(profile.get("confidence") or 0) >= 0.75
        )
    )
    if strong_profile:
        return "VERB"
    l4_tr = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    for w in l4_tr.get("words") or []:
        if (w.get("word") or "").strip() == surface and w.get("operator"):
            return "PARTICLE"
    deriv_class, _ = _l14_classification_for_token(surface, lo)
    kind = _l5_kind(surface, lo)
    if deriv_class == "VERB":
        return "VERB"
    if deriv_class in (
        "JAMID",
        "ISM_FAIL",
        "ISM_MAFUUL",
        "SIFA_MUSHABBAHA",
        "SIGA_MUBALAGHAH",
        "MASDAR",
        "MUSHTAQ_LEXICAL",
    ) and kind not in ("verb", "فعل"):
        return "NOUN"
    if _has_strong_nominal_cues(surface, kind, deriv_class) and kind not in ("verb", "فعل"):
        return "NOUN"
    if deriv_class == "PARTICLE":
        return "PARTICLE"
    if _has_strong_nominal_cues(surface, kind, deriv_class) and not strong_profile:
        return "NOUN"
    if kind in ("verb", "فعل"):
        return "VERB"
    if kind in ("noun", "اسم", "name", "proper_noun"):
        return "NOUN"
    if dsb_relation in ("SUBJ", "OBJ", "NAIB_SUBJ"):
        return "NOUN"
    if dsb_relation == "JAR_MAJRUR":
        return "NOUN"
    if kind:
        return "NOUN" if kind not in ("particle", "حرف") else "PARTICLE"
    return "UNKNOWN"


def _build_one_token_reasoning(
    token_id: str,
    surface: str,
    idx: int,
    tokens: List[str],
    lo: Dict[str, Any],
    clause_id: Optional[str],
    dsb_relation: Optional[str],
    dsb_head_id: Optional[str],
    l11b_entry: Optional[Dict],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> Dict[str, Any]:
    """Build one token_reasoning entry. Rules 1–8, safe fallbacks."""
    reasoning_steps: List[str] = []
    evidence_sources: List[str] = []
    family = _grammatical_family(token_id, surface, lo, dsb_relation)
    profile = _l8b_profile_for_token(token_id, surface, lo)
    voice = (profile.get("voice") or "").strip() if profile else ""
    governing_verb = _governing_verb_surface(dsb_head_id, tokens)

    syntactic_role: Optional[str] = None
    governing_factor: Optional[str] = None
    governing_factor_token_id: Optional[str] = dsb_head_id
    i3rab_case_or_mood: Optional[str] = None
    marker: Optional[str] = None
    confidence = CONF_UNRESOLVED
    status = "unresolved"
    limitations: List[str] = []

    # Rule 6 — Preposition-governed (JAR_MAJRUR)
    if dsb_relation == "JAR_MAJRUR":
        syntactic_role = "اسم مجرور"
        governing_factor = "حرف الجر"
        i3rab_case_or_mood = "مجرور"
        marker = "الكسرة"
        reasoning_steps.extend(["Stage15:JAR_MAJRUR", "L5:NOUN or noun-like", "No verb role"])
        evidence_sources.extend(["STAGE15", "L5"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 6b — إنَّ governance
    elif family == "NOUN" and dsb_relation == "INNA_NAME":
        syntactic_role = "اسم إن"
        governing_factor = "إِنَّ"
        i3rab_case_or_mood = "منصوب"
        marker = "الفتحة"
        reasoning_steps.extend(["Stage15:INNA_NAME", "L4:ACC_TAWKID emphatic operator", "Rule: اسم إن"])
        evidence_sources.extend(["STAGE15", "L4"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 2 — Passive verb
    elif family == "VERB" and voice == "passive":
        syntactic_role = "فعل"
        governing_factor = ""
        i3rab_case_or_mood = "مبني للمجهول مبني على الفتح"
        marker = "مبني"
        reasoning_steps.extend(["L5/L8B:VERB", "L8B:voice=passive", "Rule: passive past verb"])
        evidence_sources.extend(["L5", "L8B"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 1 — Active verb
    elif family == "VERB" and (not voice or voice == "active"):
        syntactic_role = "فعل"
        governing_factor = ""
        i3rab_case_or_mood = "مبني على الفتح"
        marker = "الفتح"
        reasoning_steps.extend(["L5/L8B:VERB", "L8B:voice=active or none", "Rule: active past verb"])
        evidence_sources.extend(["L5", "L8B"])
        confidence = CONF_GOOD
        status = "resolved"

    # Rule 4 — NAIB_SUBJ (passive subject)
    elif family == "NOUN" and dsb_relation == "NAIB_SUBJ":
        syntactic_role = "نائب فاعل"
        governing_factor = governing_verb or "الفعل المبني للمجهول"
        i3rab_case_or_mood = "مرفوع"
        marker = "الضمة"
        reasoning_steps.extend(["Stage15:NAIB_SUBJ", "L8B:head voice=passive", "Rule: passive subject"])
        evidence_sources.extend(["STAGE15", "L8B"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 3 — SUBJ (subject)
    elif family == "NOUN" and dsb_relation == "SUBJ":
        syntactic_role = "فاعل"
        governing_factor = governing_verb or "الفعل"
        i3rab_case_or_mood = "مرفوع"
        marker = "الضمة"
        reasoning_steps.extend(["Stage15:SUBJ", "L8B:head voice=active", "Rule: subject"])
        evidence_sources.extend(["STAGE15", "L8B"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 5 — OBJ (direct object)
    elif family == "NOUN" and dsb_relation == "OBJ":
        syntactic_role = "مفعول به"
        governing_factor = governing_verb or "الفعل"
        i3rab_case_or_mood = "منصوب"
        marker = "الفتحة"
        reasoning_steps.extend(["Stage15:OBJ", "L8B:head transitive", "Rule: direct object"])
        evidence_sources.extend(["STAGE15", "L8B"])
        confidence = CONF_STRONG
        status = "resolved"

    # Rule 5b — SIFA (نعت); case follows موصوف (morphological cues)
    elif family == "NOUN" and dsb_relation == "SIFA" and dsb_head_id is not None:
        try:
            hi = int(dsb_head_id)
        except (TypeError, ValueError):
            hi = -1
        head_surf = (tokens[hi] or "").strip() if 0 <= hi < len(tokens) else ""
        hb = _nominal_case_bucket_from_surface(head_surf)
        tb = _nominal_case_bucket_from_surface(surface)
        eff_case = hb or tb
        if not eff_case:
            eff_case = "منصوب" if (_has_accusative_surface_cue(surface) or _has_accusative_surface_cue(head_surf)) else "مرفوع"
        marker = _marker_for_nominal_case(eff_case, token_id, l12_by_id)
        syntactic_role = "نعت"
        governing_factor = head_surf or "الموصوف"
        governing_factor_token_id = dsb_head_id
        i3rab_case_or_mood = eff_case
        reasoning_steps.extend(["Stage15:SIFA", "Rule: نعت لموصوف (B2.3)"])
        evidence_sources.extend(["STAGE15", "L14_JAMID_MUSHTAQ"])
        confidence = CONF_GOOD
        status = "resolved"

    # Rule 7 — clause_id already set
    # Rule 8 — present verb mood: skip in v1 (safe fallback only)

    # Safe fallbacks
    if syntactic_role is None:
        if family == "VERB":
            syntactic_role = "فعل"
            i3rab_case_or_mood = "مبني — يحتاج إلى مزيد تحقق"
            marker = "—"
            confidence = CONF_FALLBACK
            status = "candidate"
            limitations.append("verb role unresolved")
        elif family == "NOUN":
            syntactic_role = "غير محسوم"
            i3rab_case_or_mood = "—"
            marker = "—"
            confidence = CONF_UNRESOLVED
            limitations.append("noun role unresolved")
        elif family == "PARTICLE":
            syntactic_role = "أداة"
            i3rab_case_or_mood = "مبني"
            marker = "—"
            confidence = CONF_FALLBACK
            status = "candidate"
        else:
            syntactic_role = "—"
            governing_factor = ""
            i3rab_case_or_mood = "—"
            marker = "—"

    ensure_arabic_word_state(lo)
    ws = ref_word_state_for_token(lo, token_id)
    if ws.get("root_confirmed") or ws.get("wazn_confirmed"):
        reasoning_steps.append("ARABIC_WORD_STATE:confirmed morphology (root/wazn)")
        if "ARABIC_WORD_STATE" not in evidence_sources:
            evidence_sources.append("ARABIC_WORD_STATE")
    cwz = (ws.get("canonical_wazn") or "").strip()
    if cwz:
        reasoning_steps.append(f"ARABIC_WORD_STATE:canonical_wazn={cwz}")
        if "ARABIC_WORD_STATE" not in evidence_sources:
            evidence_sources.append("ARABIC_WORD_STATE")
    cstem = (ws.get("canonical_stem") or "").strip()
    if cstem and cstem != (ws.get("stem") or "").strip():
        reasoning_steps.append(f"ARABIC_WORD_STATE:canonical_stem={cstem}")

    # L11B comparison
    if l11b_entry:
        l11_role = (l11b_entry.get("role") or "").strip()
        if syntactic_role and l11_role and _roles_compatible(syntactic_role, l11_role):
            reasoning_steps.append("L11B agrees")
        elif l11_role:
            reasoning_steps.append("L11B disagrees or partial")
        else:
            reasoning_steps.append("L11B unavailable")

    return {
        "token_id": token_id,
        "surface": surface,
        "grammatical_family": family,
        "syntactic_role": syntactic_role or "—",
        "governing_factor": governing_factor or "—",
        "governing_factor_token_id": governing_factor_token_id,
        "i3rab_case_or_mood": i3rab_case_or_mood or "—",
        "marker": marker or "—",
        "reasoning_steps": reasoning_steps,
        "evidence_sources": list(dict.fromkeys(evidence_sources)),
        "confidence": round(confidence, 3),
        "status": status,
        "clause_id": clause_id,
        "limitations": limitations,
    }


def _roles_compatible(a: str, b: str) -> bool:
    """Rough compatibility for L11B vs Stage 17 role."""
    a, b = a.strip(), b.strip()
    if not a or not b:
        return False
    return (
        ("فاعل" in a and "فاعل" in b)
        or ("نائب" in a and "نائب" in b)
        or ("مفعول" in a and "مفعول" in b)
        or ("مجرور" in a and "مجرور" in b)
        or ("فعل" in a and "فعل" in b)
    )


# --- v2: L12 / L14 evidence ---

def _l12_features_by_token_id(lo: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    """L12 token_features keyed by token_id. Empty dict if L12 missing."""
    tr = (lo.get("L12_GENDER_NUMBER") or {}).get("transformation_result") or {}
    out: Dict[str, Dict[str, Any]] = {}
    for f in tr.get("token_features") or []:
        tid = str(f.get("token_id"))
        if tid:
            out[tid] = f
    return out


def _l14_classification_for_token(surface: str, lo: Dict[str, Any]) -> Tuple[str, str]:
    """(derivational_class, jamid_or_mushtaq) from L14. UNKNOWN if missing."""
    jm = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    for tc in jm.get("token_classifications") or []:
        if (tc.get("surface") or "").strip() == surface:
            return (
                (tc.get("derivational_class") or "UNKNOWN").strip(),
                (tc.get("jamid_or_mushtaq") or "UNKNOWN").strip(),
            )
    return ("UNKNOWN", "UNKNOWN")


def _l14_deriv_class_by_token_id(token_id: str, lo: Dict[str, Any]) -> str:
    """L14 derivational_class for token_id (stable vs duplicate surfaces)."""
    jm = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    for tc in jm.get("token_classifications") or []:
        if str(tc.get("token_id")) == str(token_id):
            return (tc.get("derivational_class") or "UNKNOWN").strip()
    return "UNKNOWN"


def _b22_head_supports_fael_from_subj(head_id: str, tokens: List[str], lo: Dict[str, Any]) -> bool:
    """Stage15 SUBJ → فاعل only when head is a finite active verb (strong evidence)."""
    try:
        hi = int(head_id)
    except (TypeError, ValueError):
        return False
    if hi < 0 or hi >= len(tokens):
        return False
    surf = (tokens[hi] or "").strip()
    if not has_strong_true_verb_evidence(str(hi), surf, lo):
        return False
    profile = _l8b_profile_for_token(str(hi), surf, lo)
    voice = (profile.get("voice") or "").strip().lower() if profile else ""
    return voice != "passive"


def _b22_head_supports_maf3ul_from_obj(head_id: str, tokens: List[str], lo: Dict[str, Any]) -> bool:
    """Stage15 OBJ → مفعول به when head is finite verb or participial ISM_FAIL / ISM_MAFUUL (Stage15-licensed)."""
    try:
        hi = int(head_id)
    except (TypeError, ValueError):
        return False
    if hi < 0 or hi >= len(tokens):
        return False
    surf = (tokens[hi] or "").strip()
    if has_strong_true_verb_evidence(str(hi), surf, lo):
        return True
    dc = _l14_deriv_class_by_token_id(str(hi), lo)
    return dc in ("ISM_FAIL", "ISM_MAFUUL")


def _apply_b22_structural_g007_g010(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> None:
    """
    Batch 2.2 — Reinforce G007 (مفعول به) and G010 (فاعل marfu) from Stage 15 SUBJ/OBJ links.
    Does not alter إن-chain اسم إن; confidence tracks Stage 15 link strength.
    """
    by_id = {str(e.get("token_id")): e for e in token_reasoning}
    for link in dsb_links or []:
        rel = (link.get("relation") or "").strip()
        if rel not in ("SUBJ", "OBJ"):
            continue
        hid, did = link.get("head_id"), link.get("dependent_id")
        if hid is None or did is None:
            continue
        try:
            hi = int(hid)
            di = int(did)
        except (TypeError, ValueError):
            continue
        if hi < 0 or hi >= len(tokens) or di < 0 or di >= len(tokens):
            continue
        entry = by_id.get(str(di))
        if entry is None:
            continue
        head_surf = (tokens[hi] or "").strip()

        if rel == "SUBJ":
            if (entry.get("syntactic_role") or "").strip() == "اسم إن":
                continue
            if not _b22_head_supports_fael_from_subj(str(hi), tokens, lo):
                continue
            link_conf = float(link.get("confidence") or 0.8)
            prev_conf = float(entry.get("confidence") or 0)
            boosted = min(0.95, max(link_conf, prev_conf) + 0.02)
            _set_role(
                entry,
                syntactic_role="فاعل",
                governing_factor=head_surf or "الفعل",
                governing_factor_token_id=str(hi),
                i3rab_case_or_mood="مرفوع",
                marker="الضمة",
                confidence=boosted,
                status="resolved",
                reasoning_step="B2.2-G010: Stage15 SUBJ + finite active verb — فاعل (structural)",
                evidence_sources=["STAGE15", "L17:B2.2-G010", "L8B"],
            )
            entry.setdefault("gold_rule_refs", [])
            if "G010_FAIL_MARFUR" not in entry["gold_rule_refs"]:
                entry["gold_rule_refs"].append("G010_FAIL_MARFUR")
            continue

        # OBJ
        if not _b22_head_supports_maf3ul_from_obj(str(hi), tokens, lo):
            continue
        link_conf = float(link.get("confidence") or 0.78)
        prev_conf = float(entry.get("confidence") or 0)
        boosted = min(0.95, max(link_conf, prev_conf) + 0.02)
        _set_role(
            entry,
            syntactic_role="مفعول به",
            governing_factor=head_surf or "الفعل",
            governing_factor_token_id=str(hi),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(di), l12_by_id),
            confidence=boosted,
            status="resolved",
            reasoning_step="B2.2-G007: Stage15 OBJ + structural verb/participle governor — مفعول به (structural)",
            evidence_sources=["STAGE15", "L17:B2.2-G007", "L14_JAMID_MUSHTAQ"],
        )
        entry.setdefault("gold_rule_refs", [])
        if "G007_MAFUL_BIH" not in entry["gold_rule_refs"]:
            entry["gold_rule_refs"].append("G007_MAFUL_BIH")


def _build_khabar_in_candidates(
    lo: Dict[str, Any],
    dsb_links: List[Dict[str, Any]],
    tokens: List[str],
) -> List[Dict[str, Any]]:
    """
    B2.1-V2: When Stage 15 has INNA_NAME and CLAUSE_ENGINE marks a later verbal_embedded region,
    expose an additive candidate that the span is a جملة خبرية / خبر إن clause (confidence-based).
    """
    has_inna = any((l.get("relation") or "").strip() == "INNA_NAME" for l in (dsb_links or []))
    if not has_inna or not tokens:
        return []
    ce = lo.get("CLAUSE_ENGINE") or {}
    tr = ce.get("transformation_result") or ce
    regions = tr.get("verbal_clause_regions") or []
    out: List[Dict[str, Any]] = []
    for r in regions:
        if (r.get("clause_type") or "").strip() != "verbal_embedded":
            continue
        sid = r.get("start_token_id")
        eid = r.get("end_token_id")
        hid = r.get("head_token_id")
        if sid is None or eid is None or hid is None:
            continue
        try:
            s_i, e_i = int(sid), int(eid)
        except (TypeError, ValueError):
            continue
        if s_i < 0 or e_i >= len(tokens) or s_i > e_i:
            continue
        base_conf = float(r.get("confidence") or 0.75)
        out.append({
            "rule": "B2.1-V2_verbal_khabar_in_candidate",
            "confidence": round(min(0.92, base_conf * 0.96), 3),
            "evidence_sources": ["STAGE15:INNA_NAME", "CLAUSE_ENGINE:verbal_clause_regions"],
            "start_token_id": str(sid),
            "end_token_id": str(eid),
            "head_verb_token_id": str(hid),
            "label_ar": "جملة فعلية مرشحة لخبر إن",
        })
    return out


def _annotate_khabar_in_secondary(token_reasoning: List[Dict[str, Any]], candidates: List[Dict[str, Any]]) -> None:
    """Add secondary_analysis on tokens inside a B2.1-V2 candidate span (additive; does not replace primary role)."""
    for e in token_reasoning:
        try:
            tid = int(str(e.get("token_id")))
        except (TypeError, ValueError):
            continue
        for c in candidates:
            try:
                s, end = int(c.get("start_token_id")), int(c.get("end_token_id"))
            except (TypeError, ValueError):
                continue
            if s <= tid <= end:
                e.setdefault("secondary_analysis", {})
                e["secondary_analysis"]["khabar_in_clause_candidate"] = True
                e["secondary_analysis"]["khabar_in_rule"] = c.get("rule")
                e["secondary_analysis"]["khabar_in_confidence"] = c.get("confidence")
                break


def _stage15_inna_name_max_dependent(dsb_links: List[Dict[str, Any]]) -> Optional[int]:
    mx: Optional[int] = None
    for lk in dsb_links or []:
        if (lk.get("relation") or "").strip() != "INNA_NAME":
            continue
        try:
            d = int(lk.get("dependent_id"))
        except (TypeError, ValueError):
            continue
        mx = d if mx is None else max(mx, d)
    return mx


def _stage15_inna_governing_operator_token_id(dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    """Head of INNA_NAME link(s) — emphatic particle (e.g. إنَّ)."""
    for lk in dsb_links or []:
        if (lk.get("relation") or "").strip() != "INNA_NAME":
            continue
        hid = lk.get("head_id")
        if hid is not None:
            return str(hid)
    return None


def _has_resolved_ism_inn(token_reasoning: List[Dict[str, Any]]) -> bool:
    for e in token_reasoning:
        if (e.get("syntactic_role") or "").strip() != "اسم إن":
            continue
        if (e.get("status") or "").strip() == "resolved":
            return True
    return False


def _first_ism_inn_token_id(token_reasoning: List[Dict[str, Any]]) -> Optional[str]:
    for e in token_reasoning:
        if (e.get("syntactic_role") or "").strip() == "اسم إن":
            return str(e.get("token_id"))
    return None


def _b27_competing_resolved_nominal_khabar(
    token_reasoning: List[Dict[str, Any]],
    inna_ub: int,
    verbal_start: int,
) -> bool:
    """True if a resolved nominal-type khabar appears strictly between اسم إن domain and the verbal tail."""
    for e in token_reasoning:
        try:
            tid = int(str(e.get("token_id")))
        except (TypeError, ValueError):
            continue
        if tid <= inna_ub or tid >= verbal_start:
            continue
        role = (e.get("syntactic_role") or "").strip()
        st = (e.get("status") or "").strip()
        if st != "resolved":
            continue
        if "خبر" in role and "اسم" not in role and "مرشح" not in role and "فعل" not in role:
            return True
        if role in ("جملة اسمية", "خبر مرفوع"):
            return True
    return False


def _b27_has_subject_from_head(hidx: int, by_id: Dict[str, Dict[str, Any]], dsb_links: List[Dict[str, Any]]) -> bool:
    for lk in dsb_links or []:
        if str(lk.get("head_id")) != str(hidx):
            continue
        if (lk.get("relation") or "").strip() != "SUBJ":
            continue
        dep = str(lk.get("dependent_id"))
        ent = by_id.get(dep)
        if not ent:
            continue
        role = (ent.get("syntactic_role") or "").strip()
        if role in ("فاعل", "نائب فاعل") and (ent.get("status") or "").strip() == "resolved":
            return True
    return False


def _b27_region_has_completing_dependent(
    s_i: int,
    e_i: int,
    h_i: int,
    by_id: Dict[str, Dict[str, Any]],
    dsb_links: List[Dict[str, Any]],
) -> bool:
    """OBJ / B2.6 PP / حال / معطوف as tail completion inside span."""
    for lk in dsb_links or []:
        if str(lk.get("head_id")) != str(h_i):
            continue
        if (lk.get("relation") or "").strip() != "OBJ":
            continue
        try:
            di = int(lk.get("dependent_id"))
        except (TypeError, ValueError):
            continue
        if s_i <= di <= e_i:
            ent = by_id.get(str(di))
            if ent and "مفعول به" in (ent.get("syntactic_role") or "") and (ent.get("status") or "").strip() == "resolved":
                return True
    for tid in range(s_i, e_i + 1):
        ent = by_id.get(str(tid))
        if not ent:
            continue
        sec = ent.get("secondary_analysis") or {}
        if sec.get("b26_taalluq"):
            return True
        if "شبه جملة متعلّقة" in (ent.get("syntactic_role") or ""):
            return True
        if "حال" in (ent.get("syntactic_role") or "") and (ent.get("status") or "").strip() == "resolved":
            return True
        if "معطوف" in (ent.get("syntactic_role") or "") and (ent.get("status") or "").strip() in ("resolved", "candidate"):
            return True
        if "نعت" in (ent.get("syntactic_role") or "") and (ent.get("status") or "").strip() == "resolved":
            return True
    return False


def _b27_annotate_span_tokens(
    token_reasoning: List[Dict[str, Any]],
    s_i: int,
    e_i: int,
    h_i: int,
    status: str,
    confidence: float,
    rule: str,
) -> None:
    by_id = {str(e.get("token_id")): e for e in token_reasoning}
    for tid in range(s_i, e_i + 1):
        e = by_id.get(str(tid))
        if e is None:
            continue
        e.setdefault("secondary_analysis", {})
        e["secondary_analysis"]["khabar_in_clause"] = True
        e["secondary_analysis"]["khabar_in_status"] = status
        # B2.1-V2 keeps khabar_in_rule for verbal_khabar_in_candidate; B2.7 uses distinct keys.
        e["secondary_analysis"]["khabar_in_clause_resolution_rule"] = rule
        e["secondary_analysis"]["khabar_in_clause_confidence"] = round(confidence, 3)
        e["secondary_analysis"]["khabar_in_span_start"] = str(s_i)
        e["secondary_analysis"]["khabar_in_span_end"] = str(e_i)
        e["secondary_analysis"]["khabar_in_head_verb_token_id"] = str(h_i)


def _apply_b27_khabar_in_clause_resolution(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    khabar_in_candidates: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """
    Batch 2.7 — clause-level خبر إن for verbal_embedded tails matching B2.1-V2 candidates.
    Does not change token syntactic_role; adds khabar_in_analysis + secondary_analysis.
    """
    has_inna = any((l.get("relation") or "").strip() == "INNA_NAME" for l in (dsb_links or []))
    if not has_inna or not khabar_in_candidates:
        return []

    by_id = {str(e.get("token_id")): e for e in token_reasoning}
    inna_ub = _stage15_inna_name_max_dependent(dsb_links)
    op_tid = _stage15_inna_governing_operator_token_id(dsb_links)
    op_surf = (tokens[int(op_tid)] or "").strip() if op_tid is not None else ""
    ism_tid = _first_ism_inn_token_id(token_reasoning)

    out: List[Dict[str, Any]] = []

    for cand in khabar_in_candidates:
        try:
            s_i = int(str(cand.get("start_token_id")))
            e_i = int(str(cand.get("end_token_id")))
            h_i = int(str(cand.get("head_verb_token_id")))
        except (TypeError, ValueError):
            continue
        if s_i < 0 or e_i >= len(tokens) or s_i > e_i:
            continue
        if (cand.get("rule") or "").strip() != "B2.1-V2_verbal_khabar_in_candidate":
            continue

        ce = lo.get("CLAUSE_ENGINE") or {}
        tr = ce.get("transformation_result") or ce
        regions = tr.get("verbal_clause_regions") or []
        region_match = None
        for r in regions:
            if (r.get("clause_type") or "").strip() != "verbal_embedded":
                continue
            try:
                rs, re_ = int(r.get("start_token_id")), int(r.get("end_token_id"))
                rh = int(r.get("head_token_id"))
            except (TypeError, ValueError):
                continue
            if rs == s_i and re_ == e_i and rh == h_i:
                region_match = r
                break
        if region_match is None:
            continue

        if inna_ub is not None and s_i <= inna_ub:
            continue

        hv = by_id.get(str(h_i))
        if hv is None or (hv.get("syntactic_role") or "").strip() != "فعل":
            continue
        if (hv.get("status") or "").strip() != "resolved":
            continue

        if not _has_resolved_ism_inn(token_reasoning):
            row = {
                "rule": "B2.7-K1_resolve_khabar_in_verbal_clause",
                "status": "candidate",
                "confidence": 0.70,
                "label_ar": "جملة فعلية مرشّحة في محل رفع خبر إن",
                "clause_type": "verbal_embedded_khabar_in",
                "clause_function_ar": "جملة فعلية في محل رفع خبر إن",
                "start_token_id": str(s_i),
                "end_token_id": str(e_i),
                "head_verb_token_id": str(h_i),
                "governing_particle_token_id": op_tid,
                "governing_particle_surface": op_surf,
                "inna_name_token_id": ism_tid,
                "evidence_sources": ["L17:B2.7-K1", "STAGE15:INNA_NAME", "CLAUSE_ENGINE"],
                "limitations": ["no resolved اسم إن token in L17"],
            }
            out.append(row)
            _b27_annotate_span_tokens(
                token_reasoning, s_i, e_i, h_i, "candidate", 0.70, row["rule"]
            )
            continue

        if _b27_competing_resolved_nominal_khabar(token_reasoning, inna_ub if inna_ub is not None else -1, s_i):
            out.append({
                "rule": "B2.7-K1_resolve_khabar_in_verbal_clause",
                "status": "candidate",
                "confidence": 0.68,
                "label_ar": "مرشّح خبر إن — يوجد خبر اسمي منافس محتمل",
                "clause_type": "verbal_embedded_khabar_in",
                "clause_function_ar": "جملة فعلية في محل رفع خبر إن (مرشّح)",
                "start_token_id": str(s_i),
                "end_token_id": str(e_i),
                "head_verb_token_id": str(h_i),
                "governing_particle_token_id": op_tid,
                "governing_particle_surface": op_surf,
                "inna_name_token_id": ism_tid,
                "evidence_sources": ["L17:B2.7-K1"],
                "limitations": ["competing nominal khabar span before verbal tail"],
            })
            _b27_annotate_span_tokens(
                token_reasoning, s_i, e_i, h_i, "candidate", 0.68, "B2.7-K1_resolve_khabar_in_verbal_clause"
            )
            continue

        has_subj = _b27_has_subject_from_head(h_i, by_id, dsb_links)
        has_comp = _b27_region_has_completing_dependent(s_i, e_i, h_i, by_id, dsb_links)

        if has_subj and has_comp:
            conf = 0.88 if region_match and float(region_match.get("confidence") or 0) >= 0.72 else 0.82
            row = {
                "rule": "B2.7-K1_resolve_khabar_in_verbal_clause",
                "status": "resolved",
                "confidence": round(conf, 3),
                "label_ar": "جملة فعلية في محل رفع خبر إن",
                "clause_type": "verbal_embedded_khabar_in",
                "clause_function_ar": "جملة فعلية في محل رفع خبر إن",
                "start_token_id": str(s_i),
                "end_token_id": str(e_i),
                "head_verb_token_id": str(h_i),
                "governing_particle_token_id": op_tid,
                "governing_particle_surface": op_surf,
                "inna_name_token_id": ism_tid,
                "evidence_sources": [
                    "L17:B2.7-K1",
                    "STAGE15:INNA_NAME",
                    "CLAUSE_ENGINE:verbal_clause_regions",
                    "L17:token_reasoning",
                ],
                "limitations": [],
            }
            out.append(row)
            _b27_annotate_span_tokens(
                token_reasoning, s_i, e_i, h_i, "resolved", conf, row["rule"]
            )
        elif has_subj or has_comp:
            row = {
                "rule": "B2.7-K1_resolve_khabar_in_verbal_clause",
                "status": "candidate",
                "confidence": 0.74,
                "label_ar": "جملة فعلية مرشّحة في محل رفع خبر إن",
                "clause_type": "verbal_embedded_khabar_in",
                "clause_function_ar": "جملة فعلية في محل رفع خبر إن (مرشّح)",
                "start_token_id": str(s_i),
                "end_token_id": str(e_i),
                "head_verb_token_id": str(h_i),
                "governing_particle_token_id": op_tid,
                "governing_particle_surface": op_surf,
                "inna_name_token_id": ism_tid,
                "evidence_sources": ["L17:B2.7-K1", "STAGE15", "CLAUSE_ENGINE"],
                "limitations": ["incomplete verbal predicate evidence (SUBJ or complement weak)"],
            }
            out.append(row)
            _b27_annotate_span_tokens(
                token_reasoning, s_i, e_i, h_i, "candidate", 0.74, row["rule"]
            )
        else:
            row = {
                "rule": "B2.7-K1_resolve_khabar_in_verbal_clause",
                "status": "candidate",
                "confidence": 0.69,
                "label_ar": "جملة فعلية مرشّحة في محل رفع خبر إن",
                "clause_type": "verbal_embedded_khabar_in",
                "clause_function_ar": "جملة فعلية في محل رفع خبر إن (مرشّح)",
                "start_token_id": str(s_i),
                "end_token_id": str(e_i),
                "head_verb_token_id": str(h_i),
                "governing_particle_token_id": op_tid,
                "governing_particle_surface": op_surf,
                "inna_name_token_id": ism_tid,
                "evidence_sources": ["L17:B2.7-K1"],
                "limitations": ["missing resolved subject and/or complement inside span"],
            }
            out.append(row)
            _b27_annotate_span_tokens(
                token_reasoning, s_i, e_i, h_i, "candidate", 0.69, row["rule"]
            )

    return out


def _stage15_sifa_head_for_dependent(dependent_id: str, dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    """If token is SIFA dependent, return head_id (mawsuf)."""
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) == str(dependent_id) and (link.get("relation") or "").strip() == "SIFA":
            return link.get("head_id")
    return None


def _stage15_relation(dependent_id: str, dsb_links: List[Dict[str, Any]]) -> Optional[str]:
    """Relation for token as dependent. Prefer SUBJ/OBJ/NAIB_SUBJ then SIFA."""
    for link in (dsb_links or []):
        if str(link.get("dependent_id")) != str(dependent_id):
            continue
        rel = (link.get("relation") or "").strip()
        if rel in ("SUBJ", "OBJ", "NAIB_SUBJ", "SIFA"):
            return rel
    return None


def _l12_agreement_compatible(f1: Dict[str, Any], f2: Dict[str, Any]) -> Optional[bool]:
    """True if agreed, False if conflict, None if unresolved."""
    if not f1 or not f2:
        return None
    g1, g2 = (f1.get("gender") or "").strip(), (f2.get("gender") or "").strip()
    n1, n2 = (f1.get("number") or "").strip(), (f2.get("number") or "").strip()
    if g1 == "UNKNOWN" or g2 == "UNKNOWN":
        return None
    if g1 and g2 and g1 != g2:
        return False
    if n1 and n2 and n1 != "UNKNOWN" and n2 != "UNKNOWN" and n1 != n2:
        return False
    return True


def _apply_v2_refinement(
    entry: Dict[str, Any],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> List[str]:
    """
    Apply v2 refinement rules using L12 and L14. Modifies entry in place.
    Returns list of ambiguity_log lines to append.
    """
    ambiguity_notes: List[str] = []
    token_id = str(entry.get("token_id"))
    surface = (entry.get("surface") or "").strip()
    l12 = l12_by_id.get(token_id)
    deriv_class, jamid_mushtaq = _l14_classification_for_token(surface, lo)

    # Add derivational evidence (V2-3, V2-5)
    if deriv_class != "UNKNOWN" or jamid_mushtaq != "UNKNOWN":
        entry.setdefault("evidence_sources", [])
        if "L14_JAMID_MUSHTAQ" not in entry["evidence_sources"]:
            entry["evidence_sources"].append("L14_JAMID_MUSHTAQ")
        deriv_ev: List[str] = []
        if deriv_class != "UNKNOWN":
            deriv_ev.append(f"derivational_class={deriv_class}")
        if jamid_mushtaq != "UNKNOWN":
            deriv_ev.append(f"jamid_or_mushtaq={jamid_mushtaq}")
        if deriv_ev:
            entry["derivational_evidence"] = "; ".join(deriv_ev)
        entry.setdefault("reasoning_steps", [])
        if deriv_class == "JAMID":
            entry["reasoning_steps"].append("L14:JAMID — syntax/dependency first (V2-5)")
        elif deriv_class == "ISM_FAIL":
            entry["reasoning_steps"].append("L14:ISM_FAIL supports noun-agent interpretation (V2-3)")
        elif deriv_class == "ISM_MAFUUL":
            entry["reasoning_steps"].append("L14:ISM_MAFUUL supports patient/object-like (V2-3)")
        elif deriv_class == "MASDAR":
            entry["reasoning_steps"].append("L14:MASDAR — caution vs blind OBJ (V2-4)")
        elif deriv_class == "MUSHTAQ_LEXICAL":
            entry["reasoning_steps"].append("L14:MUSHTAQ_LEXICAL — derived noun (JAMID blocked by confirmed root/wazn)")

    # V2-4 MASDAR vs OBJ: lower confidence if OBJ and MASDAR
    if entry.get("syntactic_role") and "مفعول به" in (entry.get("syntactic_role") or ""):
        if deriv_class == "MASDAR":
            conf = entry.get("confidence", 0)
            if conf > CONF_CANDIDATE:
                entry["confidence"] = round(min(conf, CONF_CANDIDATE), 3)
            entry.setdefault("reasoning_steps", [])
            if "L14:MASDAR — caution vs blind OBJ (V2-4)" not in entry["reasoning_steps"]:
                entry["reasoning_steps"].append("L14:MASDAR — caution vs blind OBJ (V2-4)")
            ambiguity_notes.append(f"token_id={token_id} surface={surface!r}: OBJ + MASDAR — confidence reduced (V2-4)")

    # V2-6 Tamyiz relation
    if l12 and l12.get("tamyiz_relation") is not None:
        entry.setdefault("evidence_sources", [])
        if "L12_GENDER_NUMBER" not in entry["evidence_sources"]:
            entry["evidence_sources"].append("L12_GENDER_NUMBER")
        entry.setdefault("reasoning_steps", [])
        entry["reasoning_steps"].append("L12:tamyiz_relation — counted/quantity relation (V2-6)")

    # V2-1 / V2-2 SIFA agreement
    sifa_head_id = _stage15_sifa_head_for_dependent(token_id, dsb_links)
    if sifa_head_id is not None:
        head_l12 = l12_by_id.get(str(sifa_head_id))
        entry.setdefault("reasoning_steps", [])
        entry.setdefault("evidence_sources", [])
        if "L12_GENDER_NUMBER" not in entry["evidence_sources"]:
            entry["evidence_sources"].append("L12_GENDER_NUMBER")
        if "STAGE15" not in entry["evidence_sources"]:
            entry["evidence_sources"].append("STAGE15")
        compat = _l12_agreement_compatible(l12 or {}, head_l12 or {}) if (l12 or head_l12) else None
        if compat is True:
            entry["reasoning_steps"].append("Stage15:SIFA + L12:agreement (V2-1)")
            entry["agreement_evidence"] = "SIFA_agreed"
            conf = entry.get("confidence", 0)
            if conf < CONF_GOOD and conf >= CONF_UNRESOLVED:
                entry["confidence"] = round(min(CONF_GOOD, conf + 0.12), 3)
            entry["refinement_applied"] = True
        elif compat is False:
            entry["reasoning_steps"].append("Stage15:SIFA + L12:conflict — confidence reduced (V2-2)")
            entry["agreement_evidence"] = "SIFA_conflict"
            conf = entry.get("confidence", 0)
            entry["confidence"] = round(max(CONF_UNRESOLVED, conf - 0.15), 3)
            ambiguity_notes.append(f"token_id={token_id} surface={surface!r}: SIFA + L12 conflict (V2-2)")

    # V2-7 SUBJ agreement
    rel = _stage15_relation(token_id, dsb_links)
    if rel == "SUBJ" and entry.get("syntactic_role") and "فاعل" in (entry.get("syntactic_role") or ""):
        if l12 and (l12.get("agreement_status") or "").strip() == "agreed":
            entry.setdefault("reasoning_steps", [])
            entry["reasoning_steps"].append("L12:agreement supports فاعل (V2-7)")
            entry.setdefault("evidence_sources", [])
            if "L12_GENDER_NUMBER" not in entry["evidence_sources"]:
                entry["evidence_sources"].append("L12_GENDER_NUMBER")
            conf = entry.get("confidence", 0)
            if conf < CONF_STRONG:
                entry["confidence"] = round(min(CONF_STRONG, conf + 0.05), 3)
            entry["refinement_applied"] = True
        elif l12 and (l12.get("agreement_status") or "").strip() == "conflict":
            entry.setdefault("reasoning_steps", [])
            entry["reasoning_steps"].append("L12:agreement conflict — confidence reduced (V2-7)")
            conf = entry.get("confidence", 0)
            entry["confidence"] = round(max(CONF_CANDIDATE, conf - 0.1), 3)
            ambiguity_notes.append(f"token_id={token_id} surface={surface!r}: SUBJ + L12 conflict (V2-7)")

    # V2-8 NAIB_SUBJ agreement
    if rel == "NAIB_SUBJ" and entry.get("syntactic_role") and "نائب" in (entry.get("syntactic_role") or ""):
        if l12 and (l12.get("agreement_status") or "").strip() == "agreed":
            entry.setdefault("reasoning_steps", [])
            entry["reasoning_steps"].append("L12:agreement supports نائب فاعل (V2-8)")
            entry.setdefault("evidence_sources", [])
            if "L12_GENDER_NUMBER" not in entry["evidence_sources"]:
                entry["evidence_sources"].append("L12_GENDER_NUMBER")
            conf = entry.get("confidence", 0)
            if conf < CONF_STRONG:
                entry["confidence"] = round(min(CONF_STRONG, conf + 0.05), 3)
            entry["refinement_applied"] = True

    # V2-9 Plural/dual awareness
    if l12:
        num_type = (l12.get("number_type") or "").strip()
        number = (l12.get("number") or "").strip()
        if number in ("DUAL", "PLURAL_SOUND_M", "PLURAL_SOUND_F", "PLURAL_BROKEN") or num_type in ("dual", "sound_plural", "broken_plural"):
            entry.setdefault("reasoning_steps", [])
            entry["reasoning_steps"].append("L12:number_type — plural/dual aware (V2-9)")

    return ambiguity_notes


def _apply_reference_governance_post_pass(
    token_reasoning: List[Dict[str, Any]],
    lo: Dict[str, Any],
    tokens: List[str],
    dsb_links: List[Dict[str, Any]],
    clause_analysis: List[Dict[str, Any]],
    l12_by_id: Dict[str, Dict[str, Any]],
) -> List[str]:
    """Targeted restoration pass: إنَّ governance, coordination inheritance, ism-fa'il governance, final local verb clause."""
    ambiguity_notes: List[str] = []
    by_id = {str(e.get("token_id")): e for e in token_reasoning}

    # 1) إنَّ / أنَّ governance
    for idx, surface in enumerate(tokens):
        if not _is_emphatic_inna_operator(surface, lo):
            continue
        op_entry = by_id.get(str(idx))
        if op_entry is not None:
            _set_role(
                op_entry,
                syntactic_role="حرف توكيد ونصب",
                governing_factor="—",
                governing_factor_token_id=None,
                i3rab_case_or_mood="مبني",
                marker="—",
                confidence=CONF_STRONG,
                status="resolved",
                reasoning_step="L4:ACC_TAWKID + Stage15/sequence — emphatic governance",
                evidence_sources=["L4", "STAGE15"],
            )
        dep_idx: Optional[int] = None
        dep_from_stage15 = _stage15_inna_head_for_dependent(str(idx + 1), dsb_links)
        if dep_from_stage15 is not None:
            dep_idx = idx + 1
        else:
            dep_idx = _next_noun_candidate(idx, tokens, lo, clause_analysis, stop_before_verb=True)
        if dep_idx is None:
            continue
        dep_entry = by_id.get(str(dep_idx))
        if dep_entry is None or (dep_entry.get("grammatical_family") or "") != "NOUN":
            continue
        _set_role(
            dep_entry,
            syntactic_role="اسم إن",
            governing_factor="إِنَّ",
            governing_factor_token_id=str(idx),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(dep_idx), l12_by_id),
            confidence=CONF_STRONG,
            status="resolved",
            reasoning_step="Stage15/sequence: إنَّ governs following noun-family token",
            evidence_sources=["L4", "STAGE15", "L12_GENDER_NUMBER"],
        )

    # 2) Local strong-verb clause restoration (e.g. أَعَدَّ اللَّهُ ... مَّغْفِرَةً)
    for idx, surface in enumerate(tokens):
        if not has_strong_true_verb_evidence(str(idx), surface, lo):
            continue
        verb_entry = by_id.get(str(idx))
        if verb_entry is None:
            continue
        profile = _l8b_profile_for_token(str(idx), surface, lo)
        voice = (profile.get("voice") or "").strip().lower() if profile else ""
        if voice == "passive":
            _set_role(
                verb_entry,
                syntactic_role="فعل",
                governing_factor="",
                governing_factor_token_id=None,
                i3rab_case_or_mood="مبني للمجهول مبني على الفتح",
                marker="مبني",
                confidence=CONF_STRONG,
                status="resolved",
                reasoning_step="Strong true-verb restoration (passive)",
                evidence_sources=["L8B", "L14_JAMID_MUSHTAQ"],
            )
        else:
            _set_role(
                verb_entry,
                syntactic_role="فعل",
                governing_factor="",
                governing_factor_token_id=None,
                i3rab_case_or_mood="مبني على الفتح",
                marker="الفتح",
                confidence=CONF_GOOD,
                status="resolved",
                reasoning_step="Strong true-verb restoration (active)",
                evidence_sources=["L8B", "L14_JAMID_MUSHTAQ"],
            )

        noun_candidates = _noun_candidate_indices_after(idx, tokens, lo, clause_analysis, limit=3)
        subj_idx = noun_candidates[0] if noun_candidates else None
        if subj_idx is None:
            continue
        subj_entry = by_id.get(str(subj_idx))
        if subj_entry is None:
            continue
        subj_rel, _ = _stage15_relation_and_head(str(subj_idx), dsb_links)
        if voice == "passive":
            if subj_rel == "JAR_MAJRUR" or _has_prepositional_blocker(tokens[subj_idx] or ""):
                continue
            _set_role(
                subj_entry,
                syntactic_role="نائب فاعل",
                governing_factor=surface,
                governing_factor_token_id=str(idx),
                i3rab_case_or_mood="مرفوع",
                marker="الضمة",
                confidence=CONF_STRONG,
                status="resolved",
                reasoning_step="Local strong-verb clause restoration: passive subject",
                evidence_sources=["L8B", "token_order"],
            )
        else:
            if subj_rel == "JAR_MAJRUR" or _has_prepositional_blocker(tokens[subj_idx] or ""):
                continue
            if subj_rel not in ("SUBJ", None):
                continue
            if subj_rel != "SUBJ" and _has_accusative_surface_cue(tokens[subj_idx] or ""):
                continue
            if subj_rel != "SUBJ" and len(noun_candidates) < 2:
                # Single overt subject (e.g. أَعَدَّ اللَّهُ) when Stage 15 omitted SUBJ
                if not (
                    len(noun_candidates) == 1
                    and _definite_nominative_subject_cue(tokens[subj_idx] or "")
                ):
                    continue
            _set_role(
                subj_entry,
                syntactic_role="فاعل",
                governing_factor=surface,
                governing_factor_token_id=str(idx),
                i3rab_case_or_mood="مرفوع",
                marker="الضمة",
                confidence=CONF_STRONG,
                status="resolved",
                reasoning_step="Local strong-verb clause restoration: subject",
                evidence_sources=["L8B", "token_order"],
            )

        if voice == "passive":
            continue
        obj_idx = noun_candidates[1] if len(noun_candidates) >= 2 else None
        if obj_idx is None:
            continue
        obj_entry = by_id.get(str(obj_idx))
        if obj_entry is None:
            continue
        obj_rel, _ = _stage15_relation_and_head(str(obj_idx), dsb_links)
        if obj_rel in ("JAR_MAJRUR", "INNA_NAME", "SUBJ", "NAIB_SUBJ"):
            continue
        if _has_prepositional_blocker(tokens[obj_idx] or ""):
            continue
        _set_role(
            obj_entry,
            syntactic_role="مفعول به",
            governing_factor=surface,
            governing_factor_token_id=str(idx),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(obj_idx), l12_by_id),
            confidence=CONF_GOOD,
            status="resolved",
            reasoning_step="Local strong-verb clause restoration: direct object",
            evidence_sources=["L14_JAMID_MUSHTAQ", "token_order"],
        )

    # 3) Coordinated accusative propagation
    for link in dsb_links:
        if (link.get("relation") or "").strip() != "COORD":
            continue
        head_entry = by_id.get(str(link.get("head_id")))
        dep_entry = by_id.get(str(link.get("dependent_id")))
        if head_entry is None or dep_entry is None:
            continue
        if (head_entry.get("i3rab_case_or_mood") or "").strip() != "منصوب":
            continue
        if (head_entry.get("syntactic_role") or "").strip() not in ("اسم إن", "معطوف", "مفعول به"):
            continue
        _set_role(
            dep_entry,
            syntactic_role="معطوف",
            governing_factor=(head_entry.get("governing_factor") or "—"),
            governing_factor_token_id=head_entry.get("governing_factor_token_id"),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(dep_entry.get("token_id")), l12_by_id),
            confidence=max(CONF_GOOD, float(head_entry.get("confidence") or CONF_GOOD) - 0.05),
            status="resolved",
            reasoning_step="Stage15:COORD + inherited accusative governance",
            evidence_sources=["STAGE15", "L12_GENDER_NUMBER"],
        )

    # 3b) Local attached-waw coordination when Stage15 has no explicit COORD link (e.g. وَأَجْرًا)
    for idx in range(1, len(tokens)):
        entry = by_id.get(str(idx))
        prev_entry = by_id.get(str(idx - 1))
        if entry is None or prev_entry is None:
            continue
        if entry.get("status") == "resolved":
            continue
        if not _has_attached_waw_prefix(tokens[idx] or ""):
            continue
        if (prev_entry.get("syntactic_role") or "").strip() not in ("اسم إن", "معطوف", "مفعول به"):
            continue
        if (prev_entry.get("i3rab_case_or_mood") or "").strip() != "منصوب":
            continue
        _set_role(
            entry,
            syntactic_role="معطوف",
            governing_factor=(prev_entry.get("governing_factor") or "—"),
            governing_factor_token_id=prev_entry.get("governing_factor_token_id"),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(entry.get("token_id")), l12_by_id),
            confidence=CONF_GOOD,
            status="resolved",
            reasoning_step="Local attached-waw coordination inherits accusative governance",
            evidence_sources=["token_order", "L12_GENDER_NUMBER"],
        )

    # 4) ISM_FAIL participial governance
    for idx, surface in enumerate(tokens):
        deriv_class, _ = _l14_classification_for_token(surface, lo)
        if deriv_class != "ISM_FAIL" or has_strong_true_verb_evidence(str(idx), surface, lo):
            continue
        head_entry = by_id.get(str(idx))
        if head_entry is None:
            continue
        obj_idx = _next_noun_candidate(idx, tokens, lo, clause_analysis, stop_before_verb=True)
        if obj_idx is None:
            continue
        if not _supported_local_ism_fail_object_position(
            idx, obj_idx, tokens, lo, dsb_links, clause_analysis, by_id
        ):
            continue
        obj_entry = by_id.get(str(obj_idx))
        if obj_entry is None:
            continue
        _set_role(
            obj_entry,
            syntactic_role="مفعول به",
            governing_factor=surface,
            governing_factor_token_id=str(idx),
            i3rab_case_or_mood="منصوب",
            marker=_accusative_marker_for_token(str(obj_idx), l12_by_id),
            confidence=0.82,
            status="resolved",
            reasoning_step="L14:ISM_FAIL + immediate local governed object candidate",
            evidence_sources=["L14_JAMID_MUSHTAQ", "token_order"],
        )
        head_entry.setdefault("reasoning_steps", [])
        if "L14:ISM_FAIL local governance supports governed object" not in head_entry["reasoning_steps"]:
            head_entry["reasoning_steps"].append("L14:ISM_FAIL local governance supports governed object")
        _merge_evidence(head_entry, ["L14_JAMID_MUSHTAQ", "token_order"])

        if obj_idx + 1 < len(tokens):
            intensifier_entry = by_id.get(str(obj_idx + 1))
            norm = _normalize_surface(tokens[obj_idx + 1] or "")
            if intensifier_entry is not None and norm in ("كثيرا", "قليلا") and intensifier_entry.get("status") != "resolved":
                _set_role(
                    intensifier_entry,
                    syntactic_role="نائب عن المفعول المطلق",
                    governing_factor=surface,
                    governing_factor_token_id=str(idx),
                    i3rab_case_or_mood="منصوب",
                    marker="الفتحة",
                    confidence=CONF_CANDIDATE,
                    status="candidate",
                    reasoning_step="ISM_FAIL + governed object + intensifier pattern",
                    evidence_sources=["L14_JAMID_MUSHTAQ", "token_order"],
                )

    # 4c) B2.1-V1 — نائب عن المفعول المطلق after participial object (Stage15 OBJ + L14), including long إن chains
    # where section (4) ISM_FAIL span is blocked by inna_coord_chain: prefer naib over generic NAʿT (section 5).
    for idx in range(1, len(tokens)):
        entry = by_id.get(str(idx))
        prev_entry = by_id.get(str(idx - 1))
        if entry is None or prev_entry is None:
            continue
        if not _has_accusative_surface_cue(tokens[idx] or ""):
            continue
        deriv_e = _l14_deriv_class_by_token_id(str(idx), lo)
        if deriv_e not in ("SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH"):
            continue
        prev_rel, prev_head = _stage15_relation_and_head(str(idx - 1), dsb_links)
        if prev_rel != "OBJ" or prev_head is None:
            continue
        try:
            gov = int(prev_head)
        except (TypeError, ValueError):
            continue
        if gov < 0 or gov >= len(tokens):
            continue
        gov_class = _l14_deriv_class_by_token_id(str(gov), lo)
        if gov_class not in ("ISM_FAIL", "ISM_MAFUUL"):
            continue
        if (entry.get("syntactic_role") or "").strip() == "نائب عن المفعول المطلق":
            continue
        gov_surf = (tokens[gov] or "").strip()
        _set_role(
            entry,
            syntactic_role="نائب عن المفعول المطلق",
            governing_factor=gov_surf,
            governing_factor_token_id=str(gov),
            i3rab_case_or_mood="منصوب",
            marker="الفتحة",
            confidence=CONF_GOOD,
            status="candidate",
            reasoning_step="B2.1-V1: participial governor (L14 ISM_FAIL/ISM_MAFUUL) + Stage15 OBJ + quantitative SIFA accusative",
            evidence_sources=["L17:B2.1-V1", "STAGE15", "L14_JAMID_MUSHTAQ"],
        )

    # 5) Local na't-compatible restoration after accusative noun / coordinated object
    for idx in range(1, len(tokens)):
        entry = by_id.get(str(idx))
        prev_entry = by_id.get(str(idx - 1))
        if entry is None or prev_entry is None:
            continue
        if entry.get("status") == "resolved" or (entry.get("syntactic_role") or "").strip() != "غير محسوم":
            continue
        deriv_class, _ = _l14_classification_for_token((entry.get("surface") or "").strip(), lo)
        if deriv_class not in ("SIFA_MUSHABBAHA", "ISM_FAIL", "ISM_MAFUUL", "MUSHTAQ_LEXICAL"):
            continue
        if (prev_entry.get("syntactic_role") or "").strip() not in ("مفعول به", "معطوف"):
            continue
        if (prev_entry.get("i3rab_case_or_mood") or "").strip() != "منصوب":
            continue
        _set_role(
            entry,
            syntactic_role="نعت",
            governing_factor=(prev_entry.get("surface") or "—"),
            governing_factor_token_id=str(idx - 1),
            i3rab_case_or_mood="منصوب",
            marker="الفتحة",
            confidence=CONF_CANDIDATE,
            status="candidate",
            reasoning_step="Local accusative noun + adjective-like follower",
            evidence_sources=["L14_JAMID_MUSHTAQ", "token_order"],
        )

    # 6) V3 — Quranic patterns aligned with data/quran_i3rab.csv references (lexicon / structural, not sentence IDs)
    # 6a) حال منصوب (documented accusative hal lexicon + governing verb)
    for idx, surface in enumerate(tokens):
        if surface not in _V3_HAL_ACCUSATIVE_LEXICON:
            continue
        if not _has_accusative_surface_cue(surface):
            continue
        vidx = _preceding_strong_verb_index(idx, tokens, lo, clause_analysis)
        if vidx is None:
            continue
        entry = by_id.get(str(idx))
        if entry is None:
            continue
        vsurf = (tokens[vidx] or "").strip()
        _set_role(
            entry,
            syntactic_role="حال",
            governing_factor=vsurf,
            governing_factor_token_id=str(vidx),
            i3rab_case_or_mood="منصوب",
            marker="الفتحة",
            confidence=CONF_STRONG,
            status="resolved",
            reasoning_step="V3-1: documented hal lexicon + preceding strong verb (quran_i3rab-aligned)",
            evidence_sources=["L17:V3-1", "token_order", "L8B"],
        )

    # 6b) إنَّ + two elative كُمْ tokens — اسم إن (أول) و خبر إن (آخر) — 49:13-style
    for idx, surface in enumerate(tokens):
        if not _is_emphatic_inna_operator(surface, lo):
            continue
        kum_idxs = [j for j in range(idx + 1, len(tokens)) if _is_elative_kum_surface(tokens[j])]
        if len(kum_idxs) < 2:
            continue
        ism_idx, khabr_idx = kum_idxs[0], kum_idxs[-1]
        ism_e = by_id.get(str(ism_idx))
        khabr_e = by_id.get(str(khabr_idx))
        if ism_e is None or khabr_e is None:
            continue
        _set_role(
            ism_e,
            syntactic_role="اسم إن",
            governing_factor="إِنَّ",
            governing_factor_token_id=str(idx),
            i3rab_case_or_mood="منصوب",
            marker="الفتحة",
            confidence=CONF_STRONG,
            status="resolved",
            reasoning_step="V3-2: إنَّ + elative كُمْ pair — اسم إن (first)",
            evidence_sources=["L17:V3-2", "L4", "token_order"],
        )
        _set_role(
            khabr_e,
            syntactic_role="خبر إن",
            governing_factor="إِنَّ",
            governing_factor_token_id=str(idx),
            i3rab_case_or_mood="مرفوع",
            marker="الضمة",
            confidence=CONF_STRONG,
            status="resolved",
            reasoning_step="V3-3a: إنَّ + elative كُمْ pair — خبر إن (last)",
            evidence_sources=["L17:V3-2", "L4", "token_order"],
        )

    # 6c) ظرف زمان (documented lexicon) after strong verb — 2:187 لَيْلَةَ
    for idx, surface in enumerate(tokens):
        if surface not in _V3_ZARF_ZAMAN_LEXICON:
            continue
        vidx = _preceding_strong_verb_index(idx, tokens, lo, clause_analysis)
        if vidx is None:
            continue
        entry = by_id.get(str(idx))
        if entry is None:
            continue
        vsurf = (tokens[vidx] or "").strip()
        _set_role(
            entry,
            syntactic_role="ظرف زمان",
            governing_factor=vsurf,
            governing_factor_token_id=str(vidx),
            i3rab_case_or_mood="منصوب",
            marker="الفتحة",
            confidence=0.82,
            status="resolved",
            reasoning_step="V3-4: documented zarf zaman lexicon + governing verb (quran_i3rab-aligned)",
            evidence_sources=["L17:V3-4", "token_order", "L8B"],
        )

    # 6d) هُوَ اللَّهُ أَحَدٌ — خبر مرشح للاسم الجلالة في الجملة الاسمية المختصرة (112:1)
    for i in range(len(tokens) - 2):
        if _nfc(tokens[i] or "") != _nfc("هُوَ"):
            continue
        if _normalize_surface(tokens[i + 1] or "") != _normalize_surface("اللَّهُ"):
            continue
        if _nfc(tokens[i + 2] or "") != _nfc("أَحَدٌ"):
            continue
        ent = by_id.get(str(i + 1))
        if ent is None:
            continue
        _set_role(
            ent,
            syntactic_role="خبر (مرشح)",
            governing_factor="هُوَ",
            governing_factor_token_id=str(i),
            i3rab_case_or_mood="مرفوع",
            marker="الضمة",
            confidence=CONF_CANDIDATE,
            status="candidate",
            reasoning_step="V3-3: nominal clause هُوَ اللَّهُ أَحَدٌ — خبر candidate (pedagogical)",
            evidence_sources=["L17:V3-3", "token_order"],
        )

    # 6e) جملة فعلية في محل حال بعد ظرف زمان منصوب — 12:16 (full clause hal deferred v4)
    for idx, surface in enumerate(tokens):
        if idx == 0:
            continue
        prev = (tokens[idx - 1] or "").strip()
        if prev not in _V3_HAL_TIME_BEFORE_VERB_CLAUSE:
            continue
        if not has_strong_true_verb_evidence(str(idx), surface, lo):
            continue
        entry = by_id.get(str(idx))
        if entry is None:
            continue
        _set_role(
            entry,
            syntactic_role="جملة حالية",
            governing_factor=prev,
            governing_factor_token_id=str(idx - 1),
            i3rab_case_or_mood="—",
            marker="—",
            confidence=CONF_GOOD,
            status="resolved",
            reasoning_step="V3-5: hal clause verb — clause-level حال deferred to v4; not main-clause فعل",
            evidence_sources=["L17:V3-5", "token_order", "L8B"],
        )
        entry.setdefault("limitations", []).append("clause_level_hal_analysis_deferred_v4")

    # Keep ambiguity notes explicit for targeted unresolved/candidate paths
    for entry in token_reasoning:
        if (entry.get("syntactic_role") or "").strip() == "غير محسوم":
            continue
        if (entry.get("syntactic_role") or "").strip() == "نائب عن المفعول المطلق" and entry.get("status") != "resolved":
            ambiguity_notes.append(
                f"token_id={entry.get('token_id')} surface={entry.get('surface')!r}: نائب عن المفعول المطلق supported narrowly from ISM_FAIL + object pattern"
            )
    return ambiguity_notes


def build_rule_based_i3rab(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """
    Build Stage 17 output from layer_outputs. Returns None if no tokens.
    v1 rules apply first; v2 refinement (L12, L14) applied when evidence present.
    """
    tokens = _get_tokens(lo)
    if not tokens:
        return None

    ensure_arabic_word_state(lo)

    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    dsb_links = dsb.get("dependency_links") or []
    ce = lo.get("CLAUSE_ENGINE") or {}
    clause_analysis = ce.get("clause_analysis") or ce.get("clauses") or []
    l11b_tr = (lo.get("L11B_CAUSAL_I3RAB") or {}).get("transformation_result") or {}
    l11b_reasoning = l11b_tr.get("token_i3rab_reasoning") or []
    l12_by_id = _l12_features_by_token_id(lo)

    token_reasoning: List[Dict[str, Any]] = []
    ambiguity_log: List[str] = []
    for idx in range(len(tokens)):
        surface = (tokens[idx] or "").strip()
        token_id = str(idx)
        clause_id = _clause_id_for_token(idx, clause_analysis)
        dsb_relation, dsb_head_id = _stage15_relation_and_head(token_id, dsb_links)
        l11b_entry = next((e for e in l11b_reasoning if str(e.get("token_id")) == token_id), None)
        entry = _build_one_token_reasoning(
            token_id, surface, idx, tokens, lo, clause_id,
            dsb_relation, dsb_head_id, l11b_entry, l12_by_id,
        )
        notes = _apply_v2_refinement(entry, lo, tokens, dsb_links, l12_by_id)
        ambiguity_log.extend(notes)
        token_reasoning.append(entry)

    ambiguity_log.extend(
        _apply_reference_governance_post_pass(
            token_reasoning,
            lo,
            tokens,
            dsb_links,
            clause_analysis,
            l12_by_id,
        )
    )

    khabar_in_candidates = _build_khabar_in_candidates(lo, dsb_links, tokens)
    _annotate_khabar_in_secondary(token_reasoning, khabar_in_candidates)

    _apply_b22_structural_g007_g010(token_reasoning, lo, tokens, dsb_links, l12_by_id)

    _apply_b23_naat_agreement_g016(
        token_reasoning, lo, tokens, dsb_links, clause_analysis, l12_by_id,
    )

    _apply_b24_hal_mansub_g015(token_reasoning, lo, tokens, dsb_links, l12_by_id)

    _apply_b26_jar_majrur_taalluq_g026(token_reasoning, lo, tokens, dsb_links)

    khabar_in_analysis = _apply_b27_khabar_in_clause_resolution(
        token_reasoning, lo, tokens, dsb_links, khabar_in_candidates
    )

    resolved = sum(1 for e in token_reasoning if e.get("status") == "resolved")
    candidate = sum(1 for e in token_reasoning if e.get("status") == "candidate")
    unresolved = len(token_reasoning) - resolved - candidate

    return {
        "status": "success",
        "token_reasoning": token_reasoning,
        "reasoning_summary": {
            "resolved_tokens": resolved,
            "candidate_tokens": candidate,
            "unresolved_tokens": unresolved,
        },
        "coverage": "high_confidence_rules_only",
        "ambiguity_log": ambiguity_log,
        "khabar_in_candidates": khabar_in_candidates,
        "khabar_in_analysis": khabar_in_analysis,
    }


class RealL17RuleBasedI3rab(BaseStage):
    """L17: Rule-based iʿrāb reasoner — structured reasoning from Stage 15/16, L8B, L5, L4; does not replace L11B."""

    def __init__(self) -> None:
        super().__init__("L17_RULE_BASED_I3RAB", STAGE_NAMES["L17_RULE_BASED_I3RAB"], 19)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        lo = pipeline.get("layer_outputs") or {}
        received = get_previous_output(pipeline, self.stage_index) or {}

        tokens = _get_tokens(lo)
        if not tokens:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "skipped",
                received_input=received,
                transformation_result={
                    "status": "success",
                    "token_reasoning": [],
                    "reasoning_summary": {"resolved_tokens": 0, "candidate_tokens": 0, "unresolved_tokens": 0},
                    "coverage": "high_confidence_rules_only",
                    "ambiguity_log": [],
                    "khabar_in_candidates": [],
                    "khabar_in_analysis": [],
                },
                next_input=received,
                warnings=["No tokens; Stage 17 skipped."],
            )

        try:
            result = build_rule_based_i3rab(lo)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result={
                    "status": "failed",
                    "token_reasoning": [],
                    "reasoning_summary": {"resolved_tokens": 0, "candidate_tokens": 0, "unresolved_tokens": len(tokens)},
                    "coverage": "high_confidence_rules_only",
                    "ambiguity_log": [],
                    "khabar_in_candidates": [],
                    "khabar_in_analysis": [],
                },
                next_input=received,
                errors=[str(e)],
            )

        if result is None:
            result = {
                "status": "success",
                "token_reasoning": [],
                "reasoning_summary": {"resolved_tokens": 0, "candidate_tokens": 0, "unresolved_tokens": len(tokens)},
                "coverage": "high_confidence_rules_only",
                "ambiguity_log": [],
                "khabar_in_candidates": [],
                "khabar_in_analysis": [],
            }

        resolved = (result.get("reasoning_summary") or {}).get("resolved_tokens", 0)
        status = "success" if resolved > 0 else "partial"

        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={"file": "orchestrator/l17_rule_based_i3rab.py", "symbol": "RealL17RuleBasedI3rab", "mode": "direct"},
        )
