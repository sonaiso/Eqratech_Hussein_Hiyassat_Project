# -*- coding: utf-8 -*-
"""
L12 — Gender & Number Engine (Pass 1).

Enriches tokens with gender, number, agreement_candidates, and tamyiz relation.
Consumes L2, L5, L9, L14, L8B. Agreement rules (SIFA, SUBJ) require Stage 15;
in pipeline order L12 runs before L10/Stage 15, so agreement_status is unresolved in Pass 1.
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Tuple

from .builders import build_layer_output, get_previous_output
from .l14_jamid_mushtaq import has_strong_true_verb_evidence
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict

_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")


def _normalize_surface(s: str) -> str:
    """Strip diacritics/shadda for suffix/ending checks."""
    if not s or not isinstance(s, str):
        return ""
    return _DIACRITICS.sub("", (s or "").strip()).replace("\u0651", "").strip()


def _strip_common_nominal_proclitics(surface: str) -> str:
    """Internal nominal form for suffix checks: strip leading و/ف then ال."""
    norm = _normalize_surface(surface)
    if norm.startswith(("و", "ف")) and len(norm) > 1:
        norm = norm[1:]
    if norm.startswith("ال") and len(norm) > 2:
        norm = norm[2:]
    return norm


def _normalize_wazn(w: str) -> str:
    """Strip diacritics for wazn pattern matching."""
    if not w or not isinstance(w, str):
        return ""
    return _DIACRITICS.sub("", w).strip()


def _get_tokens(lo: Dict[str, Any]) -> List[str]:
    """Token surfaces from L2."""
    tr = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr.get("tokens") or []
    return [(t.get("word") or "").strip() for t in tokens if t.get("word")]


def _l5_kind(surface: str, lo: Dict[str, Any]) -> str:
    """L5 kind for token (noun, verb, operator, etc.)."""
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    for w in tr5.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            return (w.get("kind") or "").strip().lower()
    return ""


def _l14_derivational(surface: str, lo: Dict[str, Any]) -> Tuple[str, str]:
    """(derivational_class, jamid_or_mushtaq) from L14."""
    jm = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    for tc in jm.get("token_classifications") or []:
        if (tc.get("surface") or "").strip() == surface:
            return (
                (tc.get("derivational_class") or "UNKNOWN").strip(),
                (tc.get("jamid_or_mushtaq") or "UNKNOWN").strip(),
            )
    return ("UNKNOWN", "UNKNOWN")


def _wazn_for_token(surface: str, lo: Dict[str, Any]) -> Tuple[Optional[str], Optional[str]]:
    """(template, word_wazn) from L9."""
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    for w in tr9.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            tpl = (w.get("template") or "").strip()
            ww = (w.get("word_wazn") or "").strip()
            return (tpl or None, ww or tpl or None)
    return (None, None)


def _has_supported_mushtaq_plural_yn_signal(surface: str, lo: Dict[str, Any]) -> bool:
    """
    Conservative support signal for noun-family ...ين forms that behave like
    sound masculine plural mushtaq nouns/adjectives.
    """
    inner = _strip_common_nominal_proclitics(surface)
    if not inner.endswith("\u064a\u0646") or len(inner) <= 4:
        return False
    deriv, jamid_or_mushtaq = _l14_derivational(surface, lo)
    if deriv in ("ISM_FAIL", "ISM_MAFUUL", "SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH"):
        return True
    if jamid_or_mushtaq == "MUSHTAQ":
        return True
    stem = inner[:-2]
    if len(stem) >= 4 and stem.startswith("م"):
        return True
    if len(stem) >= 4 and stem[1] in ("ا", "أ", "آ", "ؤ", "ئ"):
        return True
    return False


def _l8b_has_verb_profile(surface: str, token_id: str, lo: Dict[str, Any]) -> bool:
    """True only for effective/strong L8B verb profiles for this token."""
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    for p in tr.get("verb_governance_profiles") or []:
        if str(p.get("token_id")) != str(token_id) or (p.get("surface") or "").strip() != surface:
            continue
        confidence = float(p.get("confidence") or 0.0)
        status = (p.get("status") or "").strip().lower()
        voice = (p.get("voice") or "").strip().lower()
        transitivity = (p.get("transitivity") or "").strip().lower()
        objects = int(p.get("objects") or 0)
        if (
            status == "resolved"
            or voice == "passive"
            or confidence >= 0.75
            or objects > 0
            or "transitive" in transitivity
            or "متعد" in transitivity
        ):
            return True
    return False


def _has_nominal_family_cues(surface: str, kind: str, deriv: str) -> bool:
    """Conservative noun-family cues used before gender/number logic."""
    norm = _normalize_surface(surface)
    inner = _strip_common_nominal_proclitics(surface)
    k = (kind or "").strip().lower()
    if k in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
        return True
    if deriv in ("JAMID", "ISM_FAIL", "ISM_MAFUUL", "SIFA_MUSHABBAHA", "SIGA_MUBALAGHAH", "MASDAR", "MUSHTAQ_LEXICAL"):
        return True
    if norm.startswith(("ال", "وال", "فال")):
        return True
    if inner.endswith(("ون", "ين", "ات", "ان")):
        return True
    return False


def _grammatical_family(token_id: str, surface: str, lo: Dict[str, Any]) -> str:
    """NOUN | VERB | PARTICLE."""
    kind = _l5_kind(surface, lo)
    deriv, _ = _l14_derivational(surface, lo)
    if kind in ("operator", "particle", "حرف") or deriv == "PARTICLE":
        return "PARTICLE"
    if has_strong_true_verb_evidence(token_id, surface, lo):
        return "VERB"
    if _has_nominal_family_cues(surface, kind, deriv):
        return "NOUN"
    if deriv == "VERB" or _l8b_has_verb_profile(surface, token_id, lo) or kind in ("verb", "فعل"):
        return "VERB"
    return "NOUN"


# --- Feminine wazn patterns (normalized, no diacritics) ---
_WAZN_FEMININE = frozenset({
    "فعلى", "فعلى", "فعلاء", "مفعلة", "فعيلة", "فعالة", "مفعلة",
})

# --- Broken plural wazn patterns (normalized). Exclude فِعَال (فعال) — ambiguous with singular كِتَاب ---
_WAZN_BROKEN_PLURAL = frozenset({
    "افعال", "فعول", "افعله", "افعلة", "فعلى", "فعلا", "مفاعل", "مفاعيل",
    "فعامل", "فواعل", "فعالل", "فعائل",
})


# --- Number lexemes (tamyiz T1) ---
_NUMBER_LEXEMES = frozenset({
    "واحد", "اثنان", "اثنين", "ثلاثة", "ثلاث", "أربعة", "أربع", "خمسة", "خمس",
    "ستة", "ست", "سبعة", "سبع", "ثمانية", "ثمان", "تسعة", "تسع", "عشرة", "عشر",
    "عشرون", "عشرين", "مئة", "مائة", "ألف", "مئة", "مائة",
})

# --- Quantity lexemes (tamyiz T2) ---
_QUANTITY_LEXEMES = frozenset({
    "كيلو", "كيلوجرام", "لتر", "متر", "غرام", "كغم", "كجم",
})


def _apply_gender_rules(
    token_id: str,
    surface: str,
    family: str,
    lo: Dict[str, Any],
) -> Tuple[str, float, str, List[str]]:
    """Returns (gender, confidence, gender_rule, evidence_sources)."""
    norm = _normalize_surface(surface)
    evidence: List[str] = []

    # G5 — Jamid + taa marbuta
    deriv, _ = _l14_derivational(surface, lo)
    if family == "NOUN" and deriv == "JAMID" and norm.endswith("\u0629"):
        return ("FEMININE", 0.85, "jamid_or_proper_noun_taa_marbuta", ["L14", "surface"])

    # G1 — Explicit taa marbuta (noun-family)
    if family == "NOUN" and norm.endswith("\u0629"):
        return ("FEMININE", 0.9, "taa_marbuta", ["surface"])

    # G2 — Feminine by wazn
    _, wazn = _wazn_for_token(surface, lo)
    wazn_norm = _normalize_wazn(wazn or "")
    if family == "NOUN" and wazn_norm in _WAZN_FEMININE:
        return ("FEMININE", 0.8, "wazn_feminine_pattern", ["L9"])

    # G4 — Verb: from L8B only; no inference from ت
    if family == "VERB":
        if _l8b_has_verb_profile(surface, token_id, lo):
            return ("UNKNOWN", 0.5, "l8b_verb_gender_unknown", ["L8B"])
        return ("UNKNOWN", 0.3, "l8b_verb_gender_unknown", [])

    # G5 — Particle
    if family == "PARTICLE":
        return ("UNKNOWN", 0.3, "particle_no_gender", [])

    # G3 — Masculine default for noun-family
    if family == "NOUN":
        return ("MASCULINE", 0.7, "default_masculine_noun", [])

    return ("UNKNOWN", 0.3, "unknown_fallback", [])


def _apply_number_rules(
    token_id: str,
    surface: str,
    family: str,
    gender: str,
    lo: Dict[str, Any],
) -> Tuple[str, str, float, str, List[str]]:
    """Returns (number, number_type, confidence, number_rule, evidence_sources)."""
    norm = _normalize_surface(surface)
    inner = _strip_common_nominal_proclitics(surface)
    evidence: List[str] = []

    if family == "PARTICLE":
        return ("UNKNOWN", "unknown", 0.3, "particle_no_number", [])

    # N1 — Dual ان (alef + noon; support common alef forms)
    if family == "NOUN" and len(inner) >= 2:
        last_two = inner[-2:]
        if last_two == "\u0627\u0646" or last_two == "\u0623\u0646" or last_two == "ان":
            return ("DUAL", "dual", 0.85, "dual_suffix_an", ["surface"])

    # N2 — Sound masculine plural ون
    if family == "NOUN" and inner.endswith("\u0648\u0646"):  # ون
        return ("PLURAL_SOUND_M", "sound_plural", 0.85, "sound_masculine_plural_suffix_wn", ["surface"])

    # N3 — Sound feminine plural ات
    if family == "NOUN" and inner.endswith("\u0627\u062a"):  # ات
        return ("PLURAL_SOUND_F", "sound_plural", 0.85, "sound_feminine_plural_suffix", ["surface"])

    # N3b — Oblique ين for noun-family: plural/dual-aware, never blind singular fallback
    if family == "NOUN" and inner.endswith("\u064a\u0646"):  # ين
        if _has_supported_mushtaq_plural_yn_signal(surface, lo):
            return ("PLURAL_SOUND_M", "sound_plural", 0.72, "sound_masculine_plural_supported_yn", ["surface", "L14"])
        return ("UNKNOWN", "unknown", 0.45, "yn_ambiguous_noun_oblique", ["surface"])

    # N4 — Broken plural by wazn
    _, wazn = _wazn_for_token(surface, lo)
    wazn_norm = _normalize_wazn(wazn or "")
    if family == "NOUN" and wazn_norm in _WAZN_BROKEN_PLURAL:
        return ("PLURAL_BROKEN", "broken_plural", 0.8, "wazn_broken_plural_pattern", ["L9"])

    # N5 — Singular default
    if family in ("NOUN", "VERB"):
        return ("SINGULAR", "singular", 0.7, "default_singular", [])

    return ("UNKNOWN", "unknown", 0.3, "unknown_fallback", [])


def _tamyiz_relation(
    token_id: str,
    surface: str,
    next_token_id: Optional[str],
    next_surface: str,
    next_family: str,
) -> Optional[str]:
    """If this token is number/quantity and next is noun, return next_token_id."""
    norm = _normalize_surface((surface or "").strip())
    norm_canonical = norm.replace("\u0623", "\u0627").replace("\u0625", "\u0627")
    if norm_canonical.startswith("\u0627\u0644"):
        norm_canonical = norm_canonical[2:]
    if norm_canonical in _NUMBER_LEXEMES and next_family == "NOUN":
        return next_token_id
    if norm_canonical in _QUANTITY_LEXEMES and next_family == "NOUN":
        return next_token_id
    if norm in _NUMBER_LEXEMES and next_family == "NOUN":
        return next_token_id
    if norm in _QUANTITY_LEXEMES and next_family == "NOUN":
        return next_token_id
    return None


def _agreement_from_stage15(
    token_id: str,
    features_by_id: Dict[str, Dict[str, Any]],
    dsb_links: List[Dict[str, Any]],
) -> Tuple[List[str], str, Optional[str]]:
    """
    When Stage 15 is available: set agreement_candidates, agreement_status, agreement_rule.
    Pass 1: L12 runs before Stage 15, so this is not used in pipeline; kept for future Pass 2.
    """
    candidates: List[str] = []
    status = "unresolved"
    rule: Optional[str] = None

    for link in dsb_links:
        rel = (link.get("relation") or "").strip()
        head_id = str(link.get("head_id", ""))
        dep_id = str(link.get("dependent_id", ""))

        if rel == "SIFA":
            if dep_id == token_id:
                candidates.append(head_id)
                head_f = features_by_id.get(head_id) or {}
                dep_f = features_by_id.get(token_id) or {}
                g_h, g_d = head_f.get("gender"), dep_f.get("gender")
                n_h, n_d = head_f.get("number"), dep_f.get("number")
                if g_h and g_d and g_h != "UNKNOWN" and g_d != "UNKNOWN" and g_h != g_d:
                    status = "conflict"
                    rule = "stage15_sifa_agreement_conflict"
                elif n_h and n_d and n_h != "UNKNOWN" and n_d != "UNKNOWN" and n_h != n_d:
                    status = "conflict"
                    rule = "stage15_sifa_agreement_conflict"
                elif (g_h == g_d or g_h == "UNKNOWN" or g_d == "UNKNOWN") and (n_h == n_d or n_h == "UNKNOWN" or n_d == "UNKNOWN"):
                    status = "agreed"
                    rule = "stage15_sifa_agreement"
                else:
                    status = "unresolved"
                    rule = "stage15_sifa_agreement_unresolved"
            elif head_id == token_id:
                candidates.append(dep_id)

        if rel == "SUBJ" and dep_id == token_id:
            candidates.append(head_id)
            if not rule:
                rule = "verb_subject_agreement_unresolved"

    return (candidates, status, rule)


def _build_one_token(
    token_id: str,
    surface: str,
    lo: Dict[str, Any],
    next_token_id: Optional[str],
    next_surface: str,
    next_family: str,
) -> Dict[str, Any]:
    """Build one token_features entry (without agreement from Stage 15)."""
    family = _grammatical_family(token_id, surface, lo)
    gender, g_conf, g_rule, g_evidence = _apply_gender_rules(token_id, surface, family, lo)
    number, num_type, n_conf, n_rule, n_evidence = _apply_number_rules(
        token_id, surface, family, gender, lo
    )
    # N3: sound feminine plural ات implies FEMININE if no stronger contradiction
    if number == "PLURAL_SOUND_F" and gender == "MASCULINE" and g_rule == "default_masculine_noun":
        gender = "FEMININE"
    confidence = min(0.95, (g_conf + n_conf) / 2.0) if (g_conf >= 0.6 or n_conf >= 0.6) else 0.3
    if family == "PARTICLE":
        confidence = 0.3

    evidence_sources = list(dict.fromkeys(g_evidence + n_evidence))

    # Tamyiz
    tamyiz_rel = _tamyiz_relation(token_id, surface, next_token_id, next_surface, next_family)
    if tamyiz_rel is not None:
        evidence_sources.append("NUMBER_LEXEME_LIST" if _normalize_surface(surface).replace("\u0623", "\u0627") in _NUMBER_LEXEMES else "QUANTITY_LEXEME_LIST")

    return {
        "token_id": token_id,
        "surface": surface,
        "gender": gender,
        "number": number,
        "number_type": num_type,
        "gender_rule": g_rule,
        "number_rule": n_rule,
        "agreement_candidates": [],
        "agreement_status": "unresolved",
        "agreement_rule": None,
        "tamyiz_relation": tamyiz_rel,
        "confidence": round(confidence, 3),
        "evidence_sources": evidence_sources,
    }


def build_gender_number(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """
    Build L12_GENDER_NUMBER output from layer_outputs.
    Returns None if no tokens.
    """
    tokens = _get_tokens(lo)
    if not tokens:
        return None

    try:
        from .arabic_word_state import ensure_arabic_word_state
        ensure_arabic_word_state(lo)
    except Exception:
        pass

    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    dsb_links = dsb.get("dependency_links") or []

    token_features: List[Dict[str, Any]] = []
    ambiguity_log: List[str] = []

    for i in range(len(tokens)):
        surface = (tokens[i] or "").strip()
        token_id = str(i)
        next_id = str(i + 1) if i + 1 < len(tokens) else None
        next_surf = (tokens[i + 1] or "").strip() if i + 1 < len(tokens) else ""
        next_family = _grammatical_family(next_id, next_surf, lo) if next_id else "NOUN"

        entry = _build_one_token(
            token_id,
            surface,
            lo,
            next_id,
            next_surf,
            next_family,
        )
        token_features.append(entry)

    # If Stage 15 is available (e.g. post-hoc run), fill agreement
    if dsb_links and token_features:
        features_by_id = {str(f.get("token_id")): f for f in token_features}
        for t in token_features:
            tid = str(t.get("token_id"))
            cand, status, rule = _agreement_from_stage15(tid, features_by_id, dsb_links)
            t["agreement_candidates"] = cand
            t["agreement_status"] = status
            t["agreement_rule"] = rule

        # Ambiguous ين: do not force dual/plural without evidence
        norm = _normalize_surface(surface)
        if norm.endswith("\u064a\u0646"):  # ين
            ambiguity_log.append(f"token_id={token_id} surface={surface!r}: suffix ين left ambiguous (dual vs oblique plural)")

    agreed = sum(1 for t in token_features if t.get("agreement_status") == "agreed")
    conflict = sum(1 for t in token_features if t.get("agreement_status") == "conflict")
    unresolved = sum(1 for t in token_features if t.get("agreement_status") == "unresolved")

    return {
        "status": "success",
        "token_features": token_features,
        "agreement_summary": {
            "total": len(token_features),
            "agreed_count": agreed,
            "conflict_count": conflict,
            "unresolved_count": unresolved,
        },
        "coverage": "gender_number_tamyiz_pass1",
        "ambiguity_log": ambiguity_log,
    }


class RealL12GenderNumber(BaseStage):
    """L12: Gender & Number — token features for agreement and tamyiz; Pass 1."""

    def __init__(self) -> None:
        super().__init__("L12_GENDER_NUMBER", STAGE_NAMES["L12_GENDER_NUMBER"], 13)

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
                    "token_features": [],
                    "agreement_summary": {"total": 0, "agreed_count": 0, "conflict_count": 0, "unresolved_count": 0},
                    "coverage": "gender_number_tamyiz_pass1",
                    "ambiguity_log": [],
                },
                next_input=received,
                warnings=["No tokens; L12 Gender/Number skipped."],
            )
        try:
            result = build_gender_number(lo)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result={
                    "status": "failed",
                    "token_features": [],
                    "agreement_summary": {"total": len(tokens), "agreed_count": 0, "conflict_count": 0, "unresolved_count": len(tokens)},
                    "coverage": "gender_number_tamyiz_pass1",
                    "ambiguity_log": [str(e)],
                },
                next_input=received,
                errors=[str(e)],
            )
        if result is None:
            result = {
                "status": "success",
                "token_features": [],
                "agreement_summary": {"total": 0, "agreed_count": 0, "conflict_count": 0, "unresolved_count": 0},
                "coverage": "gender_number_tamyiz_pass1",
                "ambiguity_log": [],
            }
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            "success",
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={"file": "orchestrator/l12_gender_number.py", "symbol": "RealL12GenderNumber", "mode": "direct"},
        )
