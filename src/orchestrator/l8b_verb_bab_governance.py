# -*- coding: utf-8 -*-
"""
L8B — Verb Bab / Governance Profile.

Enriches pipeline with structured verb governance profiles (root type, bab, transitivity,
objects, required prepositions, special class). Runs after L8_ROOT_EXTRACTION, before L9_WAZN_MATCHING.
Deterministic, rule-based; does not replace root extraction or wazn matching.
"""

from __future__ import annotations

import json
import os
import unicodedata
from typing import Any, Dict, List, Optional, Tuple

from .builders import build_layer_output, get_previous_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict

# Confidence bands [0.05, 0.98]
CONF_EXACT_KB = 0.92
CONF_GOOD_MATCH = 0.80
CONF_CANDIDATE = 0.65
CONF_WEAK = 0.40
CONF_UNRESOLVED = 0.20

# Passive voice confidence
CONF_PASSIVE_SOUND = 0.92
CONF_PASSIVE_DERIVED = 0.80
CONF_PASSIVE_HOLLOW_DEFECTIVE = 0.70
CONF_PASSIVE_WEAK = 0.40
CONF_VOICE_UNRESOLVED = 0.20

# Short vowels (combining)
FATHA = "\u064e"
DAMMA = "\u064f"
KASRA = "\u0650"
SUKUN = "\u0652"
SHADDA = "\u0651"

# Root type (triliteral first scope)
ROOT_TYPE_SAHIH_SALIM = "صحيح سالم"
ROOT_TYPE_SAHIH_MAHMOOZ = "صحيح مهموز"
ROOT_TYPE_SAHIH_MUDHAF = "صحيح مضعف"
ROOT_TYPE_MUTAL_MITHAL = "معتل مثال"
ROOT_TYPE_MUTAL_AJWAFF = "معتل أجوف"
ROOT_TYPE_MUTAL_NAQIS = "معتل ناقص"
ROOT_TYPE_MUTAL_LAFIF_MAQROON = "معتل لفيف مقرون"
ROOT_TYPE_MUTAL_LAFIF_MAFROOQ = "معتل لفيف مفروق"
ROOT_TYPE_UNKNOWN = "unknown"

# Weak letters (for root-type classification)
_WEAK_ALEF = "\u0627"
_HAMZA = "\u0621"
_WAW = "\u0648"
_YAH = "\u064a"
_ALEF_MAKSURA = "\u0649"
# Normalize to single code points for comparison
_WEAK_LETTERS = frozenset({_WEAK_ALEF, _HAMZA, _WAW, _YAH, _ALEF_MAKSURA, "\u0623", "\u0625"})

# L5 kinds that indicate non-verb unless overridden by strong verb surface/passive evidence
_L5_NON_VERB_KINDS = frozenset({
    "noun", "اسم", "operator", "particle", "أداة", "حرف", "pronoun", "ضمير",
    "adjective", "adverb", "preposition", "conjunction", "mabni", "demonstrative", "name",
})

# L5 kinds that explicitly indicate verb
_L5_VERB_KINDS = frozenset({
    "verb", "فعل", "فعل ماض", "فعل مضارع", "فعل أمر",
})

# Definite article (alef + lam) — tokens starting with ال are typically nouns
_ALEF = "\u0627"
_LAM = "\u0644"
_TA_MARBUTA = "\u0629"
# Tanwin / accusative nunation
_TANWIN_FATH = "\u064b"
_TANWIN_DAMM = "\u064c"
_TANWIN_KASR = "\u064d"

_VERB_GOVERNANCE_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
    "data",
    "verb_governance.json",
)
_VERB_ABWAB_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
    "data",
    "verb_abwab.json",
)
_KB_CACHE: Optional[Dict[str, Dict[str, Any]]] = None
_ABWAB_CACHE: Optional[Dict[str, str]] = None

# Six canonical triliteral abwab (past-present pattern names)
_CANONICAL_ABWAB = frozenset({
    "فَعَلَ-يَفْعُلُ",
    "فَعَلَ-يَفْعِلُ",
    "فَعَلَ-يَفْعَلُ",
    "فَعِلَ-يَفْعَلُ",
    "فَعُلَ-يَفْعُلُ",
    "فَعِلَ-يَفْعِلُ",
})

# Past → (present_pattern, present_passive_pattern) for صحيح سالم
_ABWAB_TENSE_MAP: Dict[str, Tuple[str, str]] = {
    "فَعَلَ-يَفْعُلُ": ("يَفْعُلُ", "يُفْعَلُ"),
    "فَعَلَ-يَفْعِلُ": ("يَفْعِلُ", "يُفْعَلُ"),
    "فَعَلَ-يَفْعَلُ": ("يَفْعَلُ", "يُفْعَلُ"),
    "فَعِلَ-يَفْعَلُ": ("يَفْعَلُ", "يُفْعَلُ"),
    "فَعُلَ-يَفْعُلُ": ("يَفْعُلُ", "يُفْعَلُ"),
    "فَعِلَ-يَفْعِلُ": ("يَفْعِلُ", "يُفْعَلُ"),
}


def _load_kb(path: Optional[str] = None) -> Dict[str, Dict[str, Any]]:
    global _KB_CACHE
    if _KB_CACHE is not None:
        return _KB_CACHE
    p = path or _VERB_GOVERNANCE_PATH
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = json.load(f)
        _KB_CACHE = {k: v for k, v in data.items() if isinstance(v, dict)}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        _KB_CACHE = {}
    return _KB_CACHE


def _load_abwab_kb(path: Optional[str] = None) -> Dict[str, str]:
    """Load verb abwab KB: root (normalized) -> bab string. Seed only."""
    global _ABWAB_CACHE
    if _ABWAB_CACHE is not None:
        return _ABWAB_CACHE
    p = path or _VERB_ABWAB_PATH
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = json.load(f)
        _ABWAB_CACHE = {k.strip(): str(v).strip() for k, v in data.items() if isinstance(v, str) and k}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        _ABWAB_CACHE = {}
    return _ABWAB_CACHE


# Bab confidence bands [0.05, 0.98]
BAB_CONF_EXACT_KB = 0.90
BAB_CONF_STRONG = 0.75
BAB_CONF_CANDIDATE = 0.55
BAB_CONF_UNKNOWN = 0.20


def _resolve_bab(
    root_norm: str,
    surface_clean: str,
    root_type: str,
    verb_class: str,
    abwab_kb: Dict[str, str],
) -> Tuple[str, str, float]:
    """Return (bab, bab_status, bab_confidence). Uses only abwab KB; no overclaim."""
    if verb_class != "trilateral" or not abwab_kb:
        return "unknown", "unknown", BAB_CONF_UNKNOWN
    bab_val = None
    if root_norm and root_norm in abwab_kb:
        bab_val = abwab_kb[root_norm]
    if not bab_val and surface_clean and surface_clean in abwab_kb:
        bab_val = abwab_kb[surface_clean]
    if not bab_val and root_norm and len(root_norm) >= 3:
        bab_val = abwab_kb.get(root_norm[:3])
        if not bab_val and len(root_norm) == 3 and root_norm[1] == root_norm[2]:
            bab_val = abwab_kb.get(root_norm[0] + root_norm[1])
    if bab_val and bab_val in _CANONICAL_ABWAB:
        return bab_val, "resolved", max(0.05, min(0.98, BAB_CONF_EXACT_KB))
    if bab_val and bab_val in ("derived_form_candidate", "unknown"):
        return bab_val, "candidate", BAB_CONF_CANDIDATE
    return "unknown", "unknown", BAB_CONF_UNKNOWN


def _tense_mapping_for_bab(bab: str, root_type: str) -> Dict[str, str]:
    """Return {past_pattern, present_pattern, present_passive_pattern}. Lightweight; descriptive only."""
    out: Dict[str, str] = {
        "past_pattern": "unknown",
        "present_pattern": "unknown",
        "present_passive_pattern": "unknown",
    }
    if bab not in _CANONICAL_ABWAB:
        if bab == "derived_form_candidate":
            out["past_pattern"] = "derived"
            out["present_pattern"] = "unknown"
            out["present_passive_pattern"] = "يُسْتَعْمَلُ"
        return out
    pair = _ABWAB_TENSE_MAP.get(bab)
    if pair:
        present, present_passive = pair
        past = bab.split("-")[0] if "-" in bab else "فَعَلَ"
        out["past_pattern"] = past
        out["present_pattern"] = present
        if root_type == ROOT_TYPE_MUTAL_AJWAFF:
            out["present_passive_pattern"] = "يُقَالُ"
        elif root_type == ROOT_TYPE_MUTAL_NAQIS or root_type == ROOT_TYPE_MUTAL_MITHAL:
            out["present_passive_pattern"] = "يُدْعَى"
        else:
            out["present_passive_pattern"] = present_passive
    return out


def _normalize_root(r: str) -> str:
    """Normalize root for lookup: strip, collapse dashes, unify alef/hamza."""
    if not r or not isinstance(r, str):
        return ""
    s = (r or "").strip().replace("-", "").replace(" ", "")
    if not s:
        return ""
    return s


def _root_letters(root: str) -> List[str]:
    """Return list of root letters (e.g. ض-ر-ب -> ['ض','ر','ب'])."""
    s = _normalize_root(root)
    if not s:
        return []
    if len(s) == 3:
        return [s[0], s[1], s[2]]
    if len(s) == 4:
        return [s[0], s[1], s[2], s[3]]
    return list(s)[:4]


def _classify_root_type(root: str) -> str:
    """
    Classify triliteral root type. Quadrilateral -> unknown or derived.
    صحيح سالم, صحيح مهموز, صحيح مضعف, معتل مثال, معتل أجوف, معتل ناقص,
    معتل لفيف مقرون, معتل لفيف مفروق, unknown.
    """
    letters = _root_letters(root)
    if len(letters) < 3:
        return ROOT_TYPE_UNKNOWN
    if len(letters) > 3:
        return "quadrilateral_candidate"  # treat as derived/unknown for bab
    a, b, c = letters[0], letters[1], letters[2]
    weak = _WEAK_LETTERS
    a_weak = a in weak
    b_weak = b in weak
    c_weak = c in weak
    # مضعف: second and third same
    if b == c and not (b_weak):
        return ROOT_TYPE_SAHIH_MUDHAF
    # مهموز: hamza in root
    if a == _HAMZA or a == "\u0623" or a == "\u0625" or b == _HAMZA or c == _HAMZA:
        return ROOT_TYPE_SAHIH_MAHMOOZ
    # معتل مثال: first letter weak
    if a_weak and not b_weak and not c_weak:
        return ROOT_TYPE_MUTAL_MITHAL
    # معتل أجوف: middle weak
    if not a_weak and b_weak and not c_weak:
        return ROOT_TYPE_MUTAL_AJWAFF
    # معتل ناقص: last letter weak
    if not a_weak and not b_weak and c_weak:
        return ROOT_TYPE_MUTAL_NAQIS
    # لفيف مقرون: first and last weak
    if a_weak and not b_weak and c_weak:
        return ROOT_TYPE_MUTAL_LAFIF_MAQROON
    # لفيف مفروق: first and middle or middle and last (two non-adjacent weak) — e.g. وَعَد
    if a_weak and c_weak:
        return ROOT_TYPE_MUTAL_LAFIF_MAFROOQ
    if not a_weak and not b_weak and not c_weak:
        return ROOT_TYPE_SAHIH_SALIM
    return ROOT_TYPE_UNKNOWN


def _base_letters(surface: str) -> List[str]:
    """Return list of base (non-diacritic) letters in order. Uses NFD."""
    return [p[0] for p in _get_letter_vowels(surface)]


def _surface_looks_non_verb(surface: str) -> bool:
    """
    True if surface form strongly suggests noun/participle/operator (regardless of L5 kind).
    Used to reject L5 'verb' for participle/noun forms like مُنْتَمِياً, وَمُتَوَكِّلاً.
    """
    letters = _base_letters(surface)
    if not letters:
        return True
    nfd = unicodedata.normalize("NFD", surface)
    if len(letters) >= 2 and letters[0] == _ALEF and letters[1] == _LAM:
        return True
    if _TANWIN_FATH in nfd or _TANWIN_DAMM in nfd or _TANWIN_KASR in nfd:
        return True
    if letters[-1] == _TA_MARBUTA:
        return True
    if len(letters) >= 3 and letters[0] == "\u0643" and letters[1] == _ALEF and letters[2] == _LAM:
        return True
    if len(letters) >= 3 and letters[0] == _LAM and letters[1] in "\u0648\u064a\u0627":
        return True
    if len(letters) >= 2 and letters[0] == _LAM and letters[1] in "\u0648\u0645":
        return True
    if len(letters) >= 2 and letters[0] == "\u0639" and letters[1] == _LAM:
        return True
    if len(letters) >= 4 and letters[-1] == _ALEF:
        return True
    if len(letters) >= 5 and letters[-1] in "\u0649\u064a":
        return True
    return False


def _is_known_non_verb(kind: str, surface: str) -> bool:
    """
    True if token is strongly indicated as non-verb (noun, operator, participle-like, etc.).
    Used to suppress governance profiling unless overridden by strong verb evidence.
    """
    k = (kind or "").strip().lower()
    if k in _L5_VERB_KINDS:
        return _surface_looks_non_verb(surface)
    if k in _L5_NON_VERB_KINDS:
        return True
    letters = _base_letters(surface)
    if not letters:
        return True
    nfd = unicodedata.normalize("NFD", surface)
    # Definite article: ال
    if len(letters) >= 2 and letters[0] == _ALEF and letters[1] == _LAM:
        return True
    # Tanwin (accusative/nominative/genitive nunation)
    if _TANWIN_FATH in nfd or _TANWIN_DAMM in nfd or _TANWIN_KASR in nfd:
        return True
    # Ta marbuta (common noun ending)
    if letters[-1] == _TA_MARBUTA:
        return True
    # كَالْ (كَ + article)
    if len(letters) >= 3 and letters[0] == "\u0643" and letters[1] == _ALEF and letters[2] == _LAM:
        return True
    # لِوَطَنِهِ, لِدِينِهِ: ل + و/ي/ا (preposition + noun)
    if len(letters) >= 3 and letters[0] == _LAM and letters[1] in "\u0648\u064a\u0627":
        return True
    # لَوْ, لَمَا: particle (ل + و or ل + م)
    if len(letters) >= 2 and letters[0] == _LAM and letters[1] in "\u0648\u0645":
        return True
    # عَلَى: preposition
    if len(letters) >= 2 and letters[0] == "\u0639" and letters[1] == _LAM and (len(letters) <= 3 or letters[2] == "\u0649"):
        return True
    # 4+ letters ending in alef: أَحَداً, أَبَداً (noun/participle)
    if len(letters) >= 4 and letters[-1] == _ALEF:
        return True
    # 5+ letters ending in alef maksura (ى): مُنْتَمِياً, مُتَوَكِّلاً (participle)
    if len(letters) >= 5 and letters[-1] in "\u0649\u064a":
        return True
    return False


def _has_strong_finite_verb_surface(surface: str) -> bool:
    """
    True if surface shows strong finite-verb vocalization (past فَعَلَ, فُعِلَ, hollow, defective, derived).
    Does NOT treat فاعل, مفعول, مُتَفَعِّل as verbs.
    """
    pairs = _get_letter_vowels(surface)
    if len(pairs) < 2:
        return False
    letters = [p[0] for p in pairs]
    vowels = [p[1] for p in pairs]
    # Exclude كَالْ (كَ + article): not a verb
    if len(letters) >= 3 and letters[0] == "\u0643" and letters[1] == _ALEF and letters[2] == _LAM:
        return False
    # Exclude noun/participle ending in alef (أَحَداً, أَبَداً, etc.)
    if len(letters) >= 4 and letters[-1] == _ALEF:
        return False
    # Exclude لِ + و/ي/ا (preposition phrase: لِوَطَنِهِ, لِدِينِهِ)
    if len(letters) >= 2 and letters[0] == _LAM and letters[1] in "\u0648\u064a\u0627":
        return False
    # Exclude لَمَا, لَمْ (particle)
    if len(letters) >= 2 and letters[0] == _LAM and letters[1] == "\u0645":
        return False
    # Exclude preposition عَلَى
    if len(letters) >= 2 and letters[0] == "\u0639" and letters[1] == _LAM:
        return False
    # Exclude participle/noun patterns: start with م (ميم) or وَم (waw + mim)
    if letters and letters[0] == "\u0645" and len(letters) >= 4:
        return False
    if len(letters) >= 5 and letters[0] == "\u0648" and letters[1] == "\u0645":
        return False
    # Past active: فَعَلَ — first two consonants fatha, third fatha
    if len(vowels) >= 3 and vowels[0] == "fatha" and vowels[1] == "fatha" and (len(vowels) <= 3 or vowels[2] == "fatha"):
        return True
    # Past passive: فُعِلَ — damma, kasra, fatha
    if len(vowels) >= 3 and vowels[0] == "damma" and vowels[1] == "kasra":
        return True
    # Hollow passive: قِيلَ — first kasra, second letter ي/و, at least 3 root letters
    if len(letters) >= 3 and vowels[0] == "kasra" and letters[1] in "\u064a\u0648":
        return True
    # Hollow active: قَالَ — first fatha, second ا/و/ي, at least 3 root letters
    if len(letters) >= 3 and vowels[0] == "fatha" and letters[1] in "\u0627\u0648\u064a":
        return True
    # Defective: أُتِيَ — damma, kasra, last ي/ى + fatha
    if len(pairs) >= 3 and vowels[0] == "damma" and vowels[1] == "kasra":
        if letters[-1] in "\u064a\u0649" and vowels[-1] == "fatha":
            return True
    # Derived: أُكْرِمَ — 4+ letters, first damma, vowel before last kasra
    if len(vowels) >= 4 and vowels[0] == "damma":
        if len(vowels) >= 2 and vowels[-2] == "kasra":
            return True
    # Derived active: أَكْرَمَ — 4+ letters, first fatha
    if len(vowels) >= 4 and vowels[0] == "fatha":
        return True
    return False


def _has_strong_passive_evidence(surface: str, root: Optional[str]) -> bool:
    """True if passive voice detector returns passive with confidence >= 0.70."""
    root_type = _classify_root_type(_normalize_root(root or ""))
    verb_class = "trilateral" if len(_root_letters(root or "")) == 3 else "quadrilateral" if len(_root_letters(root or "")) == 4 else "unknown"
    evidence = _detect_passive_voice(surface, root_type, verb_class)
    return (evidence.get("voice") == "passive") and (float(evidence.get("confidence") or 0) >= 0.70)


def _has_kb_match(surface: str, root: Optional[str], kb: Dict[str, Dict[str, Any]]) -> bool:
    """True if lexical KB has an entry for this surface/root."""
    if not kb:
        return False
    root_norm = _normalize_root(root or "")
    surface_clean = (surface or "").strip()
    if root_norm and root_norm in kb:
        return True
    if surface_clean and surface_clean in kb:
        return True
    if root_norm and len(root_norm) >= 3 and root_norm[:3] in kb:
        return True
    if root_norm and len(root_norm) == 3 and root_norm[1] == root_norm[2] and (root_norm[0] + root_norm[1]) in kb:
        return True
    return False


def is_strong_verb_candidate(
    surface: str,
    root: Optional[str],
    kind: str,
    kb: Dict[str, Dict[str, Any]],
) -> bool:
    """
    True iff token may receive a verb governance profile.
    Requires at least one of: (A) L5 verb, (B) strong finite-verb surface, (C) strong passive evidence, (D) KB match + verbal compatibility.
    """
    k = (kind or "").strip().lower()
    # (A) L5 explicitly verb — but reject if surface is clearly participle/noun (e.g. ending in اً)
    if k in _L5_VERB_KINDS:
        if not _is_known_non_verb(kind, surface):
            return True
        if _has_strong_finite_verb_surface(surface) or _has_strong_passive_evidence(surface, root):
            return True
        return False
    # Known non-verb: allow only if strong verb override
    if _is_known_non_verb(kind, surface):
        if _has_strong_finite_verb_surface(surface) or _has_strong_passive_evidence(surface, root):
            return True
        return False
    # (B) Strong finite-verb surface
    if _has_strong_finite_verb_surface(surface):
        return True
    # (C) Strong passive evidence
    if _has_strong_passive_evidence(surface, root):
        return True
    # (D) KB match and compatible with verbal morphology (root present, not clearly noun-only)
    if _has_kb_match(surface, root, kb) and (root and len(_normalize_root(root)) >= 2):
        if _has_strong_finite_verb_surface(surface) or _has_strong_passive_evidence(surface, root) or k in _L5_VERB_KINDS:
            return True
        if not _is_known_non_verb(kind, surface):
            return True
    return False


def _is_verb_candidate(kind: str, root: Optional[str], surface: str) -> bool:
    """True if token is a plausible verb candidate for governance profile. Used only after is_strong_verb_candidate for backward compatibility inside _build_profile."""
    kind = (kind or "").strip().lower()
    if kind in _L5_VERB_KINDS:
        return True
    if root and len(_normalize_root(root)) >= 2:
        return True
    return False


def _map_kb_to_transitivity(entry: Dict[str, Any]) -> str:
    trans = (entry.get("transitivity") or "").strip().lower()
    if trans in ("intransitive", "لازم"):
        return "لازم"
    if trans in ("transitive", "متعدي"):
        return "متعدي"
    if trans in ("mental_verb", "transformational"):
        return "متعدي"
    return "unknown"


def _map_kb_to_governance(
    entry: Dict[str, Any],
) -> tuple[str, int, bool, List[str], Optional[str]]:
    """Return (governance_family, objects, prepositional_required, required_prepositions, special_class)."""
    family = (entry.get("governance_family") or "").strip() or "unknown"
    objects = int(entry.get("objects") or 0)
    prep_req = bool(entry.get("prepositional_required"))
    preps = entry.get("required_prepositions")
    if isinstance(preps, list):
        required_prepositions = [str(p).strip() for p in preps if p]
    else:
        single = (entry.get("required_preposition") or "").strip()
        required_prepositions = [single] if single else []
    special = (entry.get("special_class") or "").strip() or None
    return family, objects, prep_req, required_prepositions, special


def _get_letter_vowels(word: str) -> List[Tuple[str, Optional[str]]]:
    """
    Return list of (base_letter, short_vowel) for each base letter.
    short_vowel is "fatha" | "damma" | "kasra" | None.
    Uses NFD; takes the last short vowel after each base (so shadda+fatha gives fatha).
    """
    if not word:
        return []
    nfd = unicodedata.normalize("NFD", word)
    out: List[Tuple[str, Optional[str]]] = []
    i = 0
    while i < len(nfd):
        c = nfd[i]
        if unicodedata.category(c) == "Mn":
            i += 1
            continue
        vowel: Optional[str] = None
        j = i + 1
        while j < len(nfd) and unicodedata.category(nfd[j]) == "Mn":
            m = nfd[j]
            if m == DAMMA:
                vowel = "damma"
            elif m == KASRA:
                vowel = "kasra"
            elif m == FATHA:
                vowel = "fatha"
            j += 1
        out.append((c, vowel))
        i = j if (j > i + 1) else i + 1
    return out


def _detect_passive_voice(
    surface: str,
    root_type: str,
    verb_class: str,
) -> Dict[str, Any]:
    """
    Passive voice morphological detector (past verbs only).
    Returns voice_evidence dict: voice, rule, confidence.
    Rule names: sound_trilateral_passive | hollow_passive | defective_passive | derived_passive | none.
    """
    evidence: Dict[str, Any] = {
        "voice": "unknown",
        "rule": "none",
        "confidence": CONF_VOICE_UNRESOLVED,
    }
    pairs = _get_letter_vowels(surface)
    if len(pairs) < 2:
        return evidence

    letters = [p[0] for p in pairs]
    vowels = [p[1] for p in pairs]

    # Rule A — triliteral sound past passive: فَعَلَ → فُعِلَ (first damma, second kasra)
    if len(pairs) >= 3 and root_type == ROOT_TYPE_SAHIH_SALIM:
        if vowels[0] == "damma" and vowels[1] == "kasra":
            evidence["voice"] = "passive"
            evidence["rule"] = "sound_trilateral_passive"
            evidence["confidence"] = CONF_PASSIVE_SOUND
            return evidence
        if vowels[0] == "fatha" and vowels[1] == "fatha" and (len(vowels) <= 3 or vowels[2] == "fatha"):
            evidence["voice"] = "active"
            evidence["rule"] = "none"
            evidence["confidence"] = 0.85
            return evidence

    # Rule B — triliteral hollow passive: قَالَ → قِيلَ (أجوف: middle weak; passive: كسرة then ي/و then لَ)
    if root_type == ROOT_TYPE_MUTAL_AJWAFF and len(pairs) >= 2:
        # قِيلَ = ق + كسرة + ي + ل + فتحة. So first letter kasra, then ي, then last letter fatha.
        if vowels[0] == "kasra" and len(letters) >= 2 and letters[1] in "\u064a\u0648":  # ي و
            evidence["voice"] = "passive"
            evidence["rule"] = "hollow_passive"
            evidence["confidence"] = CONF_PASSIVE_HOLLOW_DEFECTIVE
            return evidence
        if vowels[0] == "fatha":
            evidence["voice"] = "active"
            evidence["rule"] = "none"
            evidence["confidence"] = 0.75
            return evidence

    # Rule C — triliteral defective passive: أَتَى → أُتِيَ (last radical weak; passive: damma first, kasra second, يَ end)
    # Root may be ناقص (last weak) or مثال (first weak); or use surface pattern when root unknown
    last_letter = letters[-1] if len(letters) >= 1 else ""
    defective_surface_pattern = (
        len(pairs) >= 3
        and vowels[0] == "damma"
        and vowels[1] == "kasra"
        and last_letter in "\u064a\u0649"
        and vowels[-1] == "fatha"
    )
    is_defective_candidate = (
        root_type == ROOT_TYPE_MUTAL_NAQIS
        or (root_type == ROOT_TYPE_MUTAL_MITHAL and len(letters) >= 3 and last_letter in "\u064a\u0649")
        or defective_surface_pattern
    )
    if is_defective_candidate and len(pairs) >= 3:
        if vowels[0] == "damma" and vowels[1] == "kasra" and last_letter in "\u064a\u0649" and vowels[-1] == "fatha":
            evidence["voice"] = "passive"
            evidence["rule"] = "defective_passive"
            evidence["confidence"] = CONF_PASSIVE_HOLLOW_DEFECTIVE
            return evidence
        if vowels[0] == "fatha":
            evidence["voice"] = "active"
            evidence["rule"] = "none"
            evidence["confidence"] = 0.75
            return evidence

    # Rule D — derived passive: أَكْرَمَ → أُكْرِمَ (first vowel damma, vowel before last kasra)
    if verb_class in ("quadrilateral", "derived") or "derived" in (root_type or "") or len(pairs) >= 4:
        if vowels[0] == "damma":
            # Vowel before last base letter = kasra
            if len(vowels) >= 2:
                vowel_before_last = vowels[-2] if len(vowels) >= 2 else None
                if vowel_before_last == "kasra":
                    evidence["voice"] = "passive"
                    evidence["rule"] = "derived_passive"
                    evidence["confidence"] = CONF_PASSIVE_DERIVED
                    return evidence
            evidence["voice"] = "passive"
            evidence["rule"] = "derived_passive"
            evidence["confidence"] = CONF_PASSIVE_WEAK
            return evidence
        if vowels[0] == "fatha":
            evidence["voice"] = "active"
            evidence["rule"] = "none"
            evidence["confidence"] = 0.75
            return evidence

    # Active past: فَعَلَ pattern (fatha on first two)
    if len(vowels) >= 2 and vowels[0] == "fatha" and vowels[1] == "fatha":
        evidence["voice"] = "active"
        evidence["rule"] = "none"
        evidence["confidence"] = 0.80
    elif len(vowels) >= 1 and vowels[0] == "damma" and vowels[1] == "kasra":
        evidence["voice"] = "passive"
        evidence["rule"] = "sound_trilateral_passive"
        evidence["confidence"] = CONF_PASSIVE_WEAK

    evidence["confidence"] = max(0.05, min(0.98, evidence["confidence"]))
    return evidence


def _build_profile(
    token_id: str,
    surface: str,
    root: Optional[str],
    kind: str,
    kb: Dict[str, Dict[str, Any]],
    abwab_kb: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Build one verb governance profile. Non-verbs get status not_applicable or omitted."""
    root_norm = _normalize_root(root or "")
    root_type = _classify_root_type(root or "") if root_norm else ROOT_TYPE_UNKNOWN
    verb_class = "trilateral" if len(_root_letters(root or "")) == 3 else (
        "quadrilateral" if len(_root_letters(root or "")) == 4 else "unknown"
    )
    bab = "unknown"
    bab_status = "unknown"
    bab_confidence = BAB_CONF_UNKNOWN
    tense_mapping: Dict[str, str] = {"past_pattern": "unknown", "present_pattern": "unknown", "present_passive_pattern": "unknown"}
    voice = "unknown"
    tense_family = "unknown"
    transitivity = "unknown"
    objects = 0
    prepositional_required = False
    required_prepositions: List[str] = []
    governance_family = "unknown"
    special_class: Optional[str] = None
    confidence = CONF_UNRESOLVED
    status = "unresolved"

    # Lookup: normalized root, then surface (lemma), then first 3 letters of root (e.g. ظنن -> ظن)
    surface_clean = (surface or "").strip()
    entry = None
    if root_norm:
        entry = kb.get(root_norm)
    if not entry and surface_clean:
        entry = kb.get(surface_clean)
    if not entry and root_norm and len(root_norm) >= 3:
        entry = kb.get(root_norm[:3])
        if not entry and len(root_norm) == 3 and root_norm[1] == root_norm[2]:
            entry = kb.get(root_norm[0] + root_norm[1])  # مضعف: ظنن -> ظن
    if entry:
        transitivity = _map_kb_to_transitivity(entry)
        governance_family, objects, prepositional_required, required_prepositions, special_class = _map_kb_to_governance(entry)
        confidence = CONF_EXACT_KB
        status = "resolved"
    else:
        if root_norm:
            confidence = CONF_WEAK
            status = "candidate"
        else:
            status = "unresolved"

    # Passive voice morphological detector (past verbs only)
    voice_evidence = _detect_passive_voice(surface, root_type, verb_class)
    voice = (voice_evidence.get("voice") or "unknown").strip() or "unknown"
    voice_conf = max(0.05, min(0.98, float(voice_evidence.get("confidence") or CONF_VOICE_UNRESOLVED)))
    voice_evidence["confidence"] = voice_conf

    expected_subject_role: Optional[str] = "فاعل"
    if voice == "passive":
        expected_subject_role = "نائب فاعل"
        if governance_family and governance_family != "unknown":
            if "transitive" in governance_family or governance_family in ("متعدي لفعل", "double_object", "mental_verb", "transformational"):
                governance_family = "passive_transitive_frame"

    # Bab and tense mapping (six canonical abwab + lightweight present/passive-present)
    abwab = abwab_kb or _load_abwab_kb()
    bab, bab_status, bab_confidence = _resolve_bab(
        root_norm, (surface or "").strip(), root_type, verb_class, abwab
    )
    tense_mapping = _tense_mapping_for_bab(bab, root_type)
    bab_confidence = max(0.05, min(0.98, bab_confidence))

    # L8C Valency Matrix Seed: additive semantic governance metadata only (no syntax/iʿrāb change)
    valency_class = "unknown"
    valency_required_roles: List[str] = []
    valency_optional_roles: List[str] = []
    valency_confidence = 0.20
    try:
        from .valency import resolve_valency
        frame = resolve_valency(root_norm if root_norm else root)
        if frame is not None:
            valency_class = frame.valency_class or "unknown"
            valency_required_roles = list(frame.required_roles or [])
            valency_optional_roles = list(frame.optional_roles or [])
            valency_confidence = max(0.05, min(0.98, float(frame.confidence)))
    except Exception:
        pass

    return {
        "token_id": token_id,
        "surface": surface,
        "root": root if root else None,
        "root_type": root_type,
        "verb_class": verb_class,
        "bab": bab,
        "bab_status": bab_status,
        "bab_confidence": bab_confidence,
        "tense_mapping": tense_mapping,
        "voice": voice,
        "tense_family": tense_family,
        "transitivity": transitivity,
        "objects": objects,
        "prepositional_required": prepositional_required,
        "required_prepositions": required_prepositions,
        "governance_family": governance_family,
        "special_class": special_class,
        "voice_evidence": voice_evidence,
        "expected_subject_role": expected_subject_role,
        "confidence": max(0.05, min(0.98, confidence)),
        "status": status,
        "valency_class": valency_class,
        "valency_required_roles": valency_required_roles,
        "valency_optional_roles": valency_optional_roles,
        "valency_confidence": valency_confidence,
    }


class RealL8BVerbBabGovernance(BaseStage):
    """
    L8B: Verb bab / governance profile — enriches with root type, transitivity, objects,
    required prepositions, special class. Reads L2, L5, L8 only.
    """

    def __init__(self) -> None:
        super().__init__("L8B_VERB_BAB_GOVERNANCE", STAGE_NAMES["L8B_VERB_BAB_GOVERNANCE"], 9)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        lo = pipeline.get("layer_outputs") or {}
        received = get_previous_output(pipeline, self.stage_index) or {}

        tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
        tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
        tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}

        tokens = tr2.get("tokens") or []
        words5 = tr5.get("words") or []
        words8 = tr8.get("words") or []

        if not tokens:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "skipped",
                received_input=received,
                transformation_result={
                    "verb_governance_profiles": [],
                    "governance_summary": {
                        "verb_count": 0,
                        "resolved_profiles": 0,
                        "candidate_profiles": 0,
                        "unresolved_profiles": 0,
                        "excluded_non_verbs": 0,
                    },
                },
                next_input=received,
                warnings=["No tokens; verb governance skipped."],
            )

        word_to_kind: Dict[str, str] = {}
        for w in words5:
            wo = (w.get("word") or "").strip()
            if wo:
                word_to_kind[wo] = (w.get("kind") or "").strip()
        word_to_root: Dict[str, Optional[str]] = {}
        for w in words8:
            wo = (w.get("word") or "").strip()
            r = w.get("root")
            if isinstance(r, dict):
                r = r.get("formatted") or (("-".join(r["letters"]) if r.get("letters") else None))
            word_to_root[wo] = (r or "").strip() or None

        kb = _load_kb()
        abwab_kb = _load_abwab_kb()
        profiles: List[Dict[str, Any]] = []
        excluded_non_verbs = 0
        for i, t in enumerate(tokens):
            word = (t.get("word") or "").strip() if isinstance(t, dict) else ""
            if not word:
                continue
            token_id = str(i)
            kind = word_to_kind.get(word, "")
            root = word_to_root.get(word)
            if not is_strong_verb_candidate(word, root, kind, kb):
                excluded_non_verbs += 1
                continue
            profile = _build_profile(token_id, word, root, kind, kb, abwab_kb)
            profiles.append(profile)

        resolved = sum(1 for p in profiles if p.get("status") == "resolved")
        candidate = sum(1 for p in profiles if p.get("status") == "candidate")
        unresolved = sum(1 for p in profiles if p.get("status") == "unresolved")
        verb_count = len(profiles)

        summary = {
            "verb_count": verb_count,
            "resolved_profiles": resolved,
            "candidate_profiles": candidate,
            "unresolved_profiles": unresolved,
            "excluded_non_verbs": excluded_non_verbs,
        }
        result = {
            "verb_governance_profiles": profiles,
            "governance_summary": summary,
        }
        status = "success" if resolved > 0 else ("partial" if candidate > 0 or verb_count > 0 else "partial")
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={"file": "orchestrator/l8b_verb_bab_governance.py", "symbol": "RealL8BVerbBabGovernance", "mode": "direct"},
        )
