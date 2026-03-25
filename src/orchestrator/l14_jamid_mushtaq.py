# -*- coding: utf-8 -*-
"""
L14 — Jamid vs Mushtaq Engine (Pass 1).
Derivational classification from L8 root, L9 wazn, L5 kind, L8B verb profile.
Output: token_classifications with derivational_class and jamid_or_mushtaq.
"""

from __future__ import annotations

import re
import unicodedata
from typing import Any, Dict, List, Optional, Tuple

from .arabic_word_state import (
    derivational_stem,
    jamid_assignment_forbidden,
    merge_l14_classifications_into_word_state,
    ref_word_state_for_token,
    ensure_arabic_word_state,
)
from .hollow_ism_fail import (
    is_hollow_ism_fail_candidate,
    is_lexicon_listed_hollow_stem,
    resolve_hollow_ism_fail_root,
)
from .hollow_ism_mafuul import (
    is_hollow_ism_mafuul_candidate,
    is_lexicon_listed_hollow_mafuul_stem,
    resolve_hollow_ism_mafuul_root,
)
from .builders import build_layer_output, get_previous_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict
from .l8b_verb_bab_governance import _has_strong_finite_verb_surface, is_fused_yaa_nida_vocative

# Diacritics, shadda, and tatweel to strip for wazn normalization
_DIACRITICS = re.compile(r"[\u064b-\u0652\u0670\u0640]")


def _normalize_wazn(w: str) -> str:
    """Strip diacritics for pattern matching."""
    if not w or not isinstance(w, str):
        return ""
    return _DIACRITICS.sub("", w).strip()


def _normalize_surface(s: str) -> str:
    """Strip diacritics for internal family-safe classification checks."""
    if not s or not isinstance(s, str):
        return ""
    return _DIACRITICS.sub("", (s or "").strip()).strip()


def strip_common_nominal_proclitics(surface: str) -> str:
    """Internal nominal form: strip leading و/ف then ال, preserving original surface externally."""
    norm = _normalize_surface(surface)
    if norm.startswith(("و", "ف")) and len(norm) > 1:
        norm = norm[1:]
    if norm.startswith("ال") and len(norm) > 2:
        norm = norm[2:]
    return norm


def normalize_for_derivational_classification(surface: str) -> str:
    """Conservative internal normalization for derivational-family checks only."""
    return strip_common_nominal_proclitics(surface)


# Wazn patterns (normalized, no diacritics) for each derivational class
_WAZN_ISM_FAIL = frozenset({
    "فاعل", "مفاعل", "مفعل", "متفاعل", "متفعل", "منفعل", "مفتعل", "تفاعل", "مستفعل",
})
_WAZN_ISM_MAFUUL = frozenset({
    "مفعول", "مفعل", "مفاعل", "متفاعل", "منفعل", "مفتعل",
})
_WAZN_SIFA_MUSHABBAHA = frozenset({
    "فعيل", "فعل", "فعل", "افعل", "فعلان", "فعول",
})
_WAZN_MASDAR = frozenset({
    "فعل", "فعال", "فعول", "تفعيل", "افعال", "تفاعل", "انفعال", "افتعال", "استفعال",
    "مفعولة", "فعالة", "فعلة",
})
_WAZN_SIGA_MUBALAGHAH = frozenset({
    "فعّال", "فعيل", "مفعال", "فعول", "فعل",
})

_WAZN_MASDAR_AMBIGUOUS = frozenset({"فعل", "فعال", "فعول", "فعلة"})
_WAZN_MASDAR_CLEAR = _WAZN_MASDAR.difference(_WAZN_MASDAR_AMBIGUOUS)


def _get_tokens(lo: Dict[str, Any]) -> List[str]:
    """Token surfaces from L2."""
    tr = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr.get("tokens") or []
    return [(t.get("word") or "").strip() for t in tokens if t.get("word")]


def _morphology_from_word_state(token_id: str, surface: str, lo: Dict[str, Any]) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """
    Root + wazn for classification using persistent ARABIC_WORD_STATE (stem-aligned L8/L9).
    Falls back to exact-surface scan if state entry is missing (should not happen after ensure).
    """
    ws = ref_word_state_for_token(lo, token_id)
    root = ws.get("canonical_root") if ws.get("canonical_root") is not None else ws.get("root")
    template = ws.get("wazn_template")
    wazn = ws.get("canonical_wazn") or ws.get("word_wazn") or template
    if root is not None or template is not None or wazn is not None:
        return root, template, wazn
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    for w in tr9.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            tpl = (w.get("template") or "").strip()
            ww = (w.get("word_wazn") or "").strip()
            return None, tpl or None, ww or tpl or None
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    for w in tr8.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            r = w.get("root")
            if isinstance(r, dict):
                r = r.get("formatted") or ""
            rs = (str(r).strip() if r else "") or None
            return rs, None, None
    return None, None, None


def _apply_jamid_morphology_gate(
    entry: Dict[str, Any],
    ws: Dict[str, Any],
    ambiguity_entry: Optional[Dict[str, Any]],
) -> Tuple[Dict[str, Any], Optional[Dict[str, Any]]]:
    """
    Hard guard: confirmed root or wazn (per ARABIC_WORD_STATE) ⇒ never JAMID.
    Emits MUSHTAQ_LEXICAL when pattern rules would have chosen JAMID.
    """
    if not jamid_assignment_forbidden(ws):
        return entry, ambiguity_entry
    if (entry.get("jamid_or_mushtaq") or "") != "JAMID":
        return entry, ambiguity_entry
    new_e = dict(entry)
    new_e["derivational_class"] = "MUSHTAQ_LEXICAL"
    new_e["jamid_or_mushtaq"] = "MUSHTAQ"
    new_e["confidence"] = min(float(new_e.get("confidence") or 0.7), 0.85)
    new_e["rule"] = "jamid_blocked_confirmed_root_or_wazn"
    ev = list(new_e.get("evidence_sources") or [])
    for s in ("ARABIC_WORD_STATE", "L8", "L9"):
        if s not in ev:
            ev.append(s)
    new_e["evidence_sources"] = ev
    new_amb: Optional[Dict[str, Any]] = None
    if ambiguity_entry:
        new_amb = dict(ambiguity_entry)
        new_amb["selected"] = "MUSHTAQ_LEXICAL"
        new_amb["selection_reason"] = "jamid_blocked_confirmed_root_or_wazn"
    return new_e, new_amb


def _l5_kind(surface: str, lo: Dict[str, Any]) -> str:
    """L5 kind for token."""
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    for w in tr5.get("words") or []:
        if (w.get("word") or "").strip() == surface:
            return (w.get("kind") or "").strip().lower()
    return ""


def _l8b_has_verb_profile(surface: str, token_id: str, lo: Dict[str, Any]) -> bool:
    """True if L8B has a verb governance profile for this token."""
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    for p in tr.get("verb_governance_profiles") or []:
        if str(p.get("token_id")) == str(token_id) and (p.get("surface") or "").strip() == surface:
            if (p.get("status") or "").strip() == "resolved":
                return True
            if (p.get("voice") or "").strip() == "passive":
                return True
    return False


def _l8b_strong_verb_profile(surface: str, token_id: str, lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Resolved/high-confidence L8B profile only; weak candidates never override noun-family safety."""
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    for p in tr.get("verb_governance_profiles") or []:
        if str(p.get("token_id")) != str(token_id) or (p.get("surface") or "").strip() != surface:
            continue
        status = (p.get("status") or "").strip().lower()
        voice = (p.get("voice") or "").strip().lower()
        confidence = float(p.get("confidence") or 0.0)
        objects = int(p.get("objects") or 0)
        transitivity = (p.get("transitivity") or "").strip().lower()
        if (
            status == "resolved"
            or voice == "passive"
            or confidence >= 0.75
            or objects > 0
            or "transitive" in transitivity
            or "متعد" in transitivity
        ):
            return p
    return None


def _has_explicit_nominal_blocker(surface: str, kind: str) -> bool:
    """Only strong nominal blockers should defeat L5 verb fallback."""
    norm = _normalize_surface(surface)
    k = (kind or "").strip().lower()
    if k in ("name", "proper_noun", "proper noun", "علم"):
        return True
    # Patch 20 — L5 closed-class / deictic: never promote via finite-verb surface skeleton alone.
    if k in ("demonstrative", "mabni", "pronoun", "ضمير"):
        return True
    if norm.startswith(("ال", "وال", "فال")):
        return True
    if norm.endswith(("ة", "ات")):
        return True
    if any(mark in (surface or "") for mark in ("\u064b", "\u064c", "\u064d")):
        return True
    return False


def _l8b_voice_confident_candidate_profile(
    surface: str,
    token_id: str,
    lo: Dict[str, Any],
) -> Optional[Dict[str, Any]]:
    """
    Narrow fallback for genuine finite verbs missed by L5:
    candidate L8B profile + strong voice evidence + finite-verb surface cue.
    """
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    for p in tr.get("verb_governance_profiles") or []:
        if str(p.get("token_id")) != str(token_id) or (p.get("surface") or "").strip() != surface:
            continue
        status = (p.get("status") or "").strip().lower()
        voice_conf = float(((p.get("voice_evidence") or {}).get("confidence")) or 0.0)
        if status != "candidate" or voice_conf < 0.8:
            continue
        if _has_explicit_nominal_blocker(surface, _l5_kind(surface, lo)):
            continue
        if "\u0651" not in (surface or ""):
            continue
        return p
    return None


def _arabic_letters_only(surface: str) -> str:
    """Base Arabic letters U+0621–U+064A only (NFC); omits combining marks and shadda."""
    nfc = unicodedata.normalize("NFC", (surface or "").strip())
    return "".join(ch for ch in nfc if "\u0621" <= ch <= "\u064a")


def is_imperative_amr_surface(surface: str) -> bool:
    """
    Batch 28.17 — Quranic fiʿl amr with همزة على الألف + هاء (اهْدِ، اهْدِنَا، …).
    Excludes mudāriʿ ا+ه false positives handled in L17 Batch 28.16 by treating this as **أمر** only here.
    """
    s = (surface or "").strip()
    if s.startswith(("و", "ف")) and len(s) > 1:
        s = s[1:]
    if len(s) < 3:
        return False
    return s[0] == "\u0627" and s[1] == "\u0647"


def is_qul_family_amr_surface(surface: str) -> bool:
    """
    Batch 28.30 — قُلْ / أَقُلْ / قُلْنَا / قُلُوا / قُلْهُمْ (fiʿl amr of قَالَ).
    Narrow letter-skeleton match so Pass E does not treat these as post-verbal *nominal* SUBJ
    candidates after a matrix verb when L5 tags them noun-like.

    Rejects قَلْب / قَلِيل / أَقْلَم (third letter not ن/و/ه/ا after ``قل``, or ``أقل`` + non-clitic tail).
    """
    s = (surface or "").strip()
    if s.startswith(("و", "ف")) and len(s) > 1:
        s = s[1:]
    core = _arabic_letters_only(s)
    if not core:
        return False
    _QAF = "\u0642"
    _LAM = "\u0644"
    _ALEF_HAM = "\u0623"
    if core.startswith(_ALEF_HAM + _QAF + _LAM):
        if len(core) == 3:
            return True
        if len(core) <= 8:
            tail = core[3:]
            if tail.startswith(
                ("ه", "ها", "هم", "هن", "هما", "ك", "كم", "كن", "كما"),
            ):
                return True
        return False
    # قُولُوا — plural imperative of قَالَ (ق + و + ل + …, not the قُلْ ق+ل stem).
    if core.startswith("قول") and core.endswith("وا") and 5 <= len(core) <= 7:
        return True
    if not (core[0] == _QAF and len(core) >= 2 and core[1] == _LAM):
        return False
    if len(core) == 2:
        return True
    third = core[2]
    if third in ("\u0646", "\u0648", "\u0647", "\u0627"):
        return len(core) <= 6
    return False


def is_qala_root_reporting_surface(surface: str) -> bool:
    """
    Batch 28.31 — finite verb surfaces of root ق-و-ل (قَالَ، قَالُوا، …), narrow skeleton.
    """
    s = (surface or "").strip()
    if s.startswith(("و", "ف")) and len(s) > 1:
        s = s[1:]
    core = _arabic_letters_only(s)
    if not core:
        return False
    return core.startswith("قال") and 3 <= len(core) <= 8


def is_reporting_speech_matrix_verb_surface(surface: str) -> bool:
    """
    Batch 28.31 — matrix verb that can introduce quoted speech (قُلْ family + قَالَ family).
    Not a generic ``any verb`` guard.
    """
    if is_qul_family_amr_surface(surface):
        return True
    return is_qala_root_reporting_surface(surface)


def is_reporting_na_finite_surface(surface: str) -> bool:
    """
    Batch 28.30 (Priority 2) — narrow **نا** plural past forms common in Quranic speech frames.
    Letter skeletons only (no ayah lookup). Excludes short **هنا** / **أنا**-length false shapes.

    Whitelist: آمَنَّا، سَمِعْنَا، أَطَعْنَا (أمنا، سمعنا، أطعنا).
    """
    s = (surface or "").strip()
    if s.startswith(("و", "ف")) and len(s) > 1:
        s = s[1:]
    core = _arabic_letters_only(s)
    if len(core) < 4 or len(core) > 8:
        return False
    # Explicit NFC letter skeletons (U+0621–U+064A). آ (U+0622) vs أ (U+0623) on hamzated forms.
    return core in (
        "\u0623\u0645\u0646\u0627",
        "\u0622\u0645\u0646\u0627",
        "\u0633\u0645\u0639\u0646\u0627",
        "\u0623\u0637\u0639\u0646\u0627",
    )


def is_detached_iyya_pronoun(surface: str) -> bool:
    """
    Batch 28.17 — ضمير منفصل منصوب إِيَّا + ضمير (إِيَّاكَ، إِيَّانَا، …).
    Letter skeleton (NFC, U+0621–U+064A) keeps إ with hamza; إِيَّاكَ → ``إياك``.
    Strips optional و/ف coordination prefix for وَإِيَّاكَ-style surfaces.
    """
    core = _arabic_letters_only(surface)
    if core.startswith("\u0648"):
        core = core[1:]
    if core.startswith("\u0641"):
        core = core[1:]
    return len(core) >= 4 and core.startswith("\u0625\u064a\u0627")


def has_strong_true_verb_evidence(token_id: str, surface: str, lo: Dict[str, Any]) -> bool:
    """
    True only for resolved/high-confidence verbs, very narrow voice-confident finite-verb candidates,
    or L5 verb kinds without a stronger nominal blocker.
    Ambiguous noun-like wazn patterns alone never defeat confirmed verb evidence.
    """
    kind = _l5_kind(surface, lo)
    k = (kind or "").strip().lower()
    if k in ("operator", "particle", "حرف"):
        return False
    # Dual noun surfaces (…ان) match finite-verb vowel heuristics; never count as verbal evidence.
    if k in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
        inner = strip_common_nominal_proclitics(surface)
        if len(inner) >= 2 and inner[-2:] in ("\u0627\u0646", "\u0623\u0646"):
            return False
    if is_imperative_amr_surface(surface):
        return True
    # Batch 28.30 — قُلْ / قُولُوا / قُلْنَا… must win L14 VERB even when L5 tags noun-like.
    if is_qul_family_amr_surface(surface):
        return True
    if is_reporting_na_finite_surface(surface):
        return True
    # Batch 28.30 — fused يَا + munādā (e.g. يَاآدَمُ): L5 may say verb; not finite verbal evidence.
    if is_fused_yaa_nida_vocative(surface):
        return False
    # Detached إِيَّا… can match finite fatha heuristics; never count as verb evidence here (28.17 / 28.30).
    if is_detached_iyya_pronoun(surface):
        return False
    if _l8b_strong_verb_profile(surface, token_id, lo) is not None:
        return True
    if _l8b_voice_confident_candidate_profile(surface, token_id, lo) is not None:
        return True
    # Batch 28.30 — hollow/finite past (قَالَ, شَاءَ) when L5 mis-tags as noun; wazn «فعل» must not force SIFA.
    # Patch 20 — tanween / ال / تاء تأنيث / إشارة / ضمير block false «فَعَلَ» skeleton hits on nouns (e.g. عَذَابٌ, أُولَئِكَ).
    # Hollow اسم فاعل أجوف (صَائِم، قَائِل) matches the same vowel skeleton as hollow past verbs — not verbal evidence when L5 is noun-family.
    if _has_strong_finite_verb_surface(surface) and not _has_explicit_nominal_blocker(surface, kind):
        if k in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
            ws = ref_word_state_for_token(lo, token_id)
            stem_ref = (ws.get("canonical_stem") or ws.get("stem") or "").strip() or derivational_stem(surface)
            if is_hollow_ism_fail_candidate(stem_ref):
                pass
            else:
                return True
        else:
            return True
    if k in ("verb", "فعل") and not _has_explicit_nominal_blocker(surface, kind):
        return True
    return False


def _has_strong_nominal_cues(surface: str, kind: str, wazn_norm: str) -> bool:
    """Conservative noun-family cues that block weak verb overreach."""
    norm = _normalize_surface(surface)
    inner = normalize_for_derivational_classification(surface)
    k = (kind or "").strip().lower()
    if k in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
        return True
    if norm.startswith(("ال", "وال", "فال")):
        return True
    if inner.endswith(("ون", "ين", "ات", "ان")):
        return True
    if wazn_norm in (_WAZN_ISM_FAIL | _WAZN_ISM_MAFUUL | _WAZN_SIFA_MUSHABBAHA | _WAZN_SIGA_MUBALAGHAH):
        return True
    if inner.startswith(("م", "مت", "مست")) and len(inner) >= 4:
        return True
    return False


def get_safe_family_for_derivational_classification(
    token_id: str,
    surface: str,
    lo: Dict[str, Any],
    kind: Optional[str] = None,
    wazn_norm: str = "",
) -> str:
    """
    Family-safe classification guard.
    Priority: particle > strong true-verb evidence > strong noun-family cues > weak L5 hints > pattern logic.
    """
    k = (kind or _l5_kind(surface, lo) or "").strip().lower()
    if k in ("operator", "particle", "حرف"):
        return "PARTICLE"
    if has_strong_true_verb_evidence(token_id, surface, lo):
        return "VERB"
    if _has_strong_nominal_cues(surface, k, wazn_norm):
        return "NOUN"
    if k in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
        return "NOUN"
    return "NOUN" if _has_strong_nominal_cues(surface, k, wazn_norm) else "UNKNOWN"


def _classify_one(
    token_id: str,
    surface: str,
    lo: Dict[str, Any],
) -> Tuple[Dict[str, Any], Optional[Dict[str, Any]]]:
    """
    Classify one token. Returns (classification_entry, ambiguity_entry or None).
    Consumes ARABIC_WORD_STATE (stem-aligned L8/L9) before any JAMID fallback.
    """
    ws = ref_word_state_for_token(lo, token_id)
    root, template, wazn = _morphology_from_word_state(token_id, surface, lo)
    stem_ref = (ws.get("canonical_stem") or ws.get("stem") or "").strip() or derivational_stem(surface)
    root = resolve_hollow_ism_fail_root(stem_ref, root)
    root = resolve_hollow_ism_mafuul_root(stem_ref, root)
    wazn_norm = _normalize_wazn(wazn or template or "")
    kind = _l5_kind(surface, lo)
    strong_verb = _l8b_strong_verb_profile(surface, token_id, lo)
    safe_family = get_safe_family_for_derivational_classification(token_id, surface, lo, kind=kind, wazn_norm=wazn_norm)

    derivational_class = "UNKNOWN"
    jamid_or_mushtaq = "UNKNOWN"
    confidence = 0.3
    rule = "unknown_fallback"
    evidence_sources: List[str] = []
    ambiguity_entry: Optional[Dict[str, Any]] = None
    candidates: List[Dict[str, Any]] = []

    # RULE 0 — Batch 28.30 fused يَا + munādā (proper-name vocative); not a verb token for dependency scans.
    if is_fused_yaa_nida_vocative(surface):
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": "JAMID",
            "jamid_or_mushtaq": "JAMID",
            "confidence": 0.86,
            "rule": "B28_30_fused_yaa_nida_munada",
            "evidence_sources": ["L14", "B28_30"],
        }, None)

    # RULE 7 — VERB (before mushtaq)
    if safe_family == "VERB":
        derivational_class = "VERB"
        jamid_or_mushtaq = "VERB"
        confidence = 0.95 if strong_verb is not None else 0.85
        rule = "family_safe_resolved_verb" if strong_verb is not None else "family_safe_l5_verb"
        evidence_sources = ["L8B", "L5"] if strong_verb is not None else ["L5"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 8 — PARTICLE
    if safe_family == "PARTICLE":
        derivational_class = "PARTICLE"
        jamid_or_mushtaq = "PARTICLE"
        confidence = 0.95
        rule = "l5_particle_operator"
        evidence_sources = ["L5"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 1 — ISM_FAIL
    if safe_family == "NOUN" and wazn_norm in _WAZN_ISM_FAIL:
        derivational_class = "ISM_FAIL"
        jamid_or_mushtaq = "MUSHTAQ"
        confidence = 0.9
        rule = "wazn_ism_fail_pattern"
        evidence_sources = ["L9", "L8"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 1H — ISM_FAIL from hollow verb (فَائِل written shape; root from origin not surface hamza)
    if safe_family == "NOUN" and is_hollow_ism_fail_candidate(stem_ref):
        root = resolve_hollow_ism_fail_root(stem_ref, root)
        listed = is_lexicon_listed_hollow_stem(stem_ref)
        derivational_class = "ISM_FAIL"
        jamid_or_mushtaq = "MUSHTAQ"
        confidence = 0.9 if listed else 0.78
        rule = "hollow_ism_fail_lexicon" if listed else "hollow_ism_fail_shape"
        evidence_sources = ["HOLLOW_ISM_FAIL", "ARABIC_WORD_STATE", "L8"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 2 — ISM_MAFUUL
    if safe_family == "NOUN" and wazn_norm in _WAZN_ISM_MAFUUL:
        root = resolve_hollow_ism_mafuul_root(stem_ref, root)
        derivational_class = "ISM_MAFUUL"
        jamid_or_mushtaq = "MUSHTAQ"
        confidence = 0.9
        rule = "wazn_ism_mafuul_pattern"
        evidence_sources = ["L9", "L8"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 2H — ISM_MAFUUL from hollow passive participle (مَفْعُول / مَفْعِيل surface after affix strip)
    if safe_family == "NOUN" and is_hollow_ism_mafuul_candidate(stem_ref):
        root = resolve_hollow_ism_mafuul_root(stem_ref, root)
        listed = is_lexicon_listed_hollow_mafuul_stem(stem_ref)
        derivational_class = "ISM_MAFUUL"
        jamid_or_mushtaq = "MUSHTAQ"
        confidence = 0.9 if listed else 0.78
        rule = "hollow_ism_mafuul_lexicon" if listed else "hollow_ism_mafuul_shape"
        evidence_sources = ["HOLLOW_ISM_MAFUUL", "ARABIC_WORD_STATE", "L8"]
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, None)

    # RULE 4 — MASDAR (prefer over SIFA when trilateral root and clear masdar wazn)
    if safe_family == "NOUN" and wazn_norm in _WAZN_MASDAR_CLEAR:
        candidates.append({"class": "MASDAR", "confidence": 0.82, "rule": "wazn_masdar_pattern_clear"})
    # RULE 3 — SIFA_MUSHABBAHA
    if safe_family == "NOUN" and wazn_norm in _WAZN_SIFA_MUSHABBAHA:
        candidates.append({"class": "SIFA_MUSHABBAHA", "confidence": 0.75, "rule": "wazn_sifa_mushabbaha_pattern"})
    # RULE 5 — SIGA_MUBALAGHAH
    if safe_family == "NOUN" and wazn_norm in _WAZN_SIGA_MUBALAGHAH:
        candidates.append({"class": "SIGA_MUBALAGHAH", "confidence": 0.75, "rule": "wazn_siga_mubalaghah_pattern"})

    if candidates:
        best = max(candidates, key=lambda c: c["confidence"])
        derivational_class = best["class"]
        jamid_or_mushtaq = "MUSHTAQ"
        confidence = best["confidence"]
        rule = best["rule"]
        evidence_sources = ["L9", "L8"]
        if len(candidates) > 1:
            ambiguity_entry = {
                "token_id": token_id,
                "surface": surface,
                "candidates": candidates,
                "selected": derivational_class,
                "selection_reason": "highest_confidence_with_masdar_preference",
            }
        return ({
            "token_id": token_id,
            "surface": surface,
            "root": root,
            "wazn": wazn or template,
            "derivational_class": derivational_class,
            "jamid_or_mushtaq": jamid_or_mushtaq,
            "confidence": confidence,
            "rule": rule,
            "evidence_sources": evidence_sources,
        }, ambiguity_entry)

    if safe_family == "NOUN" and wazn_norm in _WAZN_MASDAR_AMBIGUOUS:
        ambiguity_entry = {
            "token_id": token_id,
            "surface": surface,
            "candidates": [
                {"class": "MASDAR", "confidence": 0.45, "rule": "ambiguous_masdar_pattern_only"},
                {"class": "JAMID", "confidence": 0.55, "rule": "family_safe_nominal_fallback"},
            ],
            "selected": "JAMID",
            "selection_reason": "family_safe_ambiguous_masdar_block",
        }

    # RULE 6 — JAMID
    if safe_family == "NOUN":
        if not wazn_norm or wazn_norm in ("", "—"):
            derivational_class = "JAMID"
            jamid_or_mushtaq = "JAMID"
            confidence = 0.7
            rule = "no_mushtaq_wazn_jamid_fallback"
            evidence_sources = ["L5", "L9"]
        else:
            # proper noun / name -> JAMID with higher confidence
            if kind in ("name", "proper_noun", "proper noun"):
                derivational_class = "JAMID"
                jamid_or_mushtaq = "JAMID"
                confidence = 0.85
                rule = "proper_noun_jamid"
                evidence_sources = ["L5"]
            else:
                derivational_class = "JAMID"
                jamid_or_mushtaq = "JAMID"
                confidence = 0.6 if wazn_norm in _WAZN_MASDAR_AMBIGUOUS else 0.7
                rule = "family_safe_ambiguous_masdar_block" if wazn_norm in _WAZN_MASDAR_AMBIGUOUS else "no_mushtaq_wazn_jamid_fallback"
                evidence_sources = ["L5", "L9"]
        entry, ambiguity_entry = _apply_jamid_morphology_gate(
            {
                "token_id": token_id,
                "surface": surface,
                "root": root,
                "wazn": wazn or template,
                "derivational_class": derivational_class,
                "jamid_or_mushtaq": jamid_or_mushtaq,
                "confidence": confidence,
                "rule": rule,
                "evidence_sources": evidence_sources,
            },
            ws,
            ambiguity_entry,
        )
        return (entry, ambiguity_entry)

    # RULE 9 — UNKNOWN
    return ({
        "token_id": token_id,
        "surface": surface,
        "root": root,
        "wazn": wazn or template,
        "derivational_class": "UNKNOWN",
        "jamid_or_mushtaq": "UNKNOWN",
        "confidence": 0.3,
        "rule": "unknown_fallback",
        "evidence_sources": [],
    }, None)


def build_jamid_mushtaq(lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Build L14_JAMID_MUSHTAQ output from layer_outputs. Returns None if no tokens."""
    tokens = _get_tokens(lo)
    if not tokens:
        return None

    ensure_arabic_word_state(lo)

    token_classifications: List[Dict[str, Any]] = []
    ambiguity_log: List[Dict[str, Any]] = []

    for idx in range(len(tokens)):
        surface = (tokens[idx] or "").strip()
        token_id = str(idx)
        entry, amb = _classify_one(token_id, surface, lo)
        token_classifications.append(entry)
        if amb:
            ambiguity_log.append(amb)

    summary: Dict[str, int] = {
        "total": len(token_classifications),
        "ism_fail_count": 0,
        "ism_mafuul_count": 0,
        "sifa_mushabbaha_count": 0,
        "masdar_count": 0,
        "siga_mubalaghah_count": 0,
        "mushtaq_lexical_count": 0,
        "jamid_count": 0,
        "verb_count": 0,
        "particle_count": 0,
        "unknown_count": 0,
    }
    for t in token_classifications:
        dc = t.get("derivational_class") or ""
        if dc == "ISM_FAIL":
            summary["ism_fail_count"] += 1
        elif dc == "ISM_MAFUUL":
            summary["ism_mafuul_count"] += 1
        elif dc == "SIFA_MUSHABBAHA":
            summary["sifa_mushabbaha_count"] += 1
        elif dc == "MASDAR":
            summary["masdar_count"] += 1
        elif dc == "SIGA_MUBALAGHAH":
            summary["siga_mubalaghah_count"] += 1
        elif dc == "MUSHTAQ_LEXICAL":
            summary["mushtaq_lexical_count"] += 1
        elif dc == "JAMID":
            summary["jamid_count"] += 1
        elif dc == "VERB":
            summary["verb_count"] += 1
        elif dc == "PARTICLE":
            summary["particle_count"] += 1
        else:
            summary["unknown_count"] += 1

    return {
        "status": "success",
        "token_classifications": token_classifications,
        "classification_summary": summary,
        "coverage": "wazn_based_pass1",
        "ambiguity_log": ambiguity_log,
    }


class RealL14JamidMushtaq(BaseStage):
    """L14: Jamid vs Mushtaq — derivational classification from L8/L9/L5/L8B."""

    def __init__(self) -> None:
        super().__init__("L14_JAMID_MUSHTAQ", STAGE_NAMES["L14_JAMID_MUSHTAQ"], 11)

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
                    "token_classifications": [],
                    "classification_summary": {"total": 0, "ism_fail_count": 0, "ism_mafuul_count": 0, "sifa_mushabbaha_count": 0, "masdar_count": 0, "siga_mubalaghah_count": 0, "mushtaq_lexical_count": 0, "jamid_count": 0, "verb_count": 0, "particle_count": 0, "unknown_count": 0},
                    "coverage": "wazn_based_pass1",
                    "ambiguity_log": [],
                },
                next_input=received,
                warnings=["No tokens; Jamid/Mushtaq skipped."],
            )

        try:
            result = build_jamid_mushtaq(lo)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result={
                    "status": "failed",
                    "token_classifications": [],
                    "classification_summary": {"total": len(tokens), "ism_fail_count": 0, "ism_mafuul_count": 0, "sifa_mushabbaha_count": 0, "masdar_count": 0, "siga_mubalaghah_count": 0, "mushtaq_lexical_count": 0, "jamid_count": 0, "verb_count": 0, "particle_count": 0, "unknown_count": len(tokens)},
                    "coverage": "wazn_based_pass1",
                    "ambiguity_log": [],
                },
                next_input=received,
                errors=[str(e)],
            )

        if result is None:
            result = {
                "status": "success",
                "token_classifications": [],
                "classification_summary": {"total": 0, "ism_fail_count": 0, "ism_mafuul_count": 0, "sifa_mushabbaha_count": 0, "masdar_count": 0, "siga_mubalaghah_count": 0, "mushtaq_lexical_count": 0, "jamid_count": 0, "verb_count": 0, "particle_count": 0, "unknown_count": 0},
                "coverage": "wazn_based_pass1",
                "ambiguity_log": [],
            }

        merge_l14_classifications_into_word_state(lo, result)

        mushtaq_count = (
            result.get("classification_summary", {}).get("ism_fail_count", 0)
            + result.get("classification_summary", {}).get("ism_mafuul_count", 0)
            + result.get("classification_summary", {}).get("sifa_mushabbaha_count", 0)
            + result.get("classification_summary", {}).get("masdar_count", 0)
            + result.get("classification_summary", {}).get("siga_mubalaghah_count", 0)
            + result.get("classification_summary", {}).get("mushtaq_lexical_count", 0)
        )
        status = "success" if mushtaq_count > 0 or result.get("classification_summary", {}).get("jamid_count", 0) > 0 else "partial"

        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={"file": "orchestrator/l14_jamid_mushtaq.py", "symbol": "RealL14JamidMushtaq", "mode": "direct"},
        )
