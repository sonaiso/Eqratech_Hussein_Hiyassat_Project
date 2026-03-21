# -*- coding: utf-8 -*-
"""
Controlled relation-label inventory for Stage 15 DEPENDENCY_SYNTAX_BUILDER.
Pass A: SUBJ, OBJ, PRED, NAIB_SUBJ only. ROOT is excluded; root_resolution is sole root record.
"""

from __future__ import annotations

from typing import Any, Dict, List

# Relation labels (Pass A)
REL_SUBJ = "SUBJ"
REL_OBJ = "OBJ"
REL_PRED = "PRED"
REL_NAIB_SUBJ = "NAIB_SUBJ"

# Relation labels (Pass B)
REL_JAR_MAJRUR = "JAR_MAJRUR"
REL_PP_ATTACH = "PP_ATTACH"
REL_IDAFA = "IDAFA"
REL_SIFA = "SIFA"
REL_INNA_NAME = "INNA_NAME"

# Relation labels (Pass C)
REL_COORD = "COORD"
REL_COORD_CONJ = "COORD_CONJ"
REL_APPOS = "APPOS"
REL_TAMYIZ_CAND = "TAMYIZ_CAND"
REL_HAL_CAND = "HAL_CAND"

# Arabic role constants (for arabic_role field)
AR_FAIL = "FAIL"
AR_MUBTADA = "MUBTADA"
AR_MAF3UL_BIH = "MAF3UL_BIH"
AR_KHABAR = "KHABAR"
AR_NAIB_FAIL = "NAIB_FAIL"
AR_JAR_MAJRUR = "JAR_MAJRUR"
AR_PP_ATTACH = "PP_ATTACH"
AR_MUDAF = "MUDAF"
AR_NA3T = "NA3T"
AR_ISM_INNA = "ISM_INNA"
AR_ATF = "ATF"
AR_ATF_CONJ = "ATF_CONJ"
AR_BADAL = "BADAL"

PASS_A_RELATIONS: List[str] = [REL_SUBJ, REL_OBJ, REL_PRED, REL_NAIB_SUBJ]
PASS_B_RELATIONS: List[str] = [REL_JAR_MAJRUR, REL_PP_ATTACH, REL_IDAFA, REL_SIFA, REL_INNA_NAME]
PASS_C_RELATIONS: List[str] = [REL_COORD, REL_COORD_CONJ, REL_APPOS]
PASS_C_MARKERS_ONLY: List[str] = [REL_TAMYIZ_CAND, REL_HAL_CAND]  # no link; see candidate_markers in output


def get_relation_spec(relation: str) -> Dict[str, Any]:
    """Return full spec for a relation label. Empty dict if unknown."""
    return _INVENTORY.get(relation, {})


def get_arabic_role_for_relation(relation: str, context: str = "verbal") -> str | None:
    """Map relation to arabic_role. context: 'verbal' | 'nominal'."""
    spec = _INVENTORY.get(relation, {})
    ar = spec.get("arabic_role")
    if isinstance(ar, str):
        return ar
    if relation == REL_SUBJ:
        return AR_FAIL if context == "verbal" else AR_MUBTADA
    return None


# Pass A inventory: label -> spec. Canonical direction = head → dependent (governing head first).
_INVENTORY: Dict[str, Dict[str, Any]] = {
    REL_SUBJ: {
        "label": REL_SUBJ,
        "arabic_name": "فاعل",
        "definition": "Subject in verbal sentence. Canonical direction: governing verb/root → SUBJ → subject noun. Used for verbal sentences only; nominal sentences do not use SUBJ (they use root_resolution for mubtada and PRED for mubtada→khabar).",
        "typical_trigger_signals": ["post-verb noun (active)"],
        "arabic_role": None,  # resolved by context: FAIL (verbal)
        "example": "كَتَبَ → SUBJ → زَيْدٌ (head=verb, dependent=subject noun)",
    },
    REL_OBJ: {
        "label": REL_OBJ,
        "arabic_name": "مفعول به",
        "definition": "Direct object of transitive verb. Canonical direction: governing verb/root → OBJ → object noun.",
        "typical_trigger_signals": [
            "post-subject noun",
            "L8B transitivity confirmed",
        ],
        "arabic_role": AR_MAF3UL_BIH,
        "example": "كَتَبَ → OBJ → الرِّسَالَةَ (head=verb, dependent=object noun)",
    },
    REL_PRED: {
        "label": REL_PRED,
        "arabic_name": "خبر المبتدأ",
        "definition": "Predicate of nominal sentence (khabar). Canonical direction: governing nominal head (mubtada/root nominal center) → PRED → khabar.",
        "typical_trigger_signals": [
            "second noun/adjective after mubtada",
        ],
        "arabic_role": AR_KHABAR,
        "example": "الطَّالِبُ → PRED → مُجْتَهِدٌ (head=mubtada, dependent=khabar)",
    },
    REL_NAIB_SUBJ: {
        "label": REL_NAIB_SUBJ,
        "arabic_name": "نائب فاعل",
        "definition": "Passive subject (naib al-fa'il). Canonical direction: governing passive verb/root → NAIB_SUBJ → naib al-fa'il.",
        "typical_trigger_signals": [
            "L8B passive voice",
            "post-verb noun",
        ],
        "arabic_role": AR_NAIB_FAIL,
        "example": "ضُرِبَ → NAIB_SUBJ → الظَّالِمُ (head=passive verb, dependent=naib al-fa'il)",
    },
    # Pass B
    REL_JAR_MAJRUR: {
        "label": REL_JAR_MAJRUR,
        "arabic_name": "جار ومجرور",
        "definition": "Preposition (harf al-jarr) linked to its governed noun (majrur). Canonical direction: harf_al_jarr → JAR_MAJRUR → majrur noun.",
        "typical_trigger_signals": ["harf jar token from L4/connectives layer"],
        "arabic_role": AR_JAR_MAJRUR,
        "example": "في → JAR_MAJRUR → البيت (head=harf, dependent=majrur noun)",
    },
    REL_PP_ATTACH: {
        "label": REL_PP_ATTACH,
        "arabic_name": "تعلق شبه الجملة",
        "definition": "PP anchor attached to governing head. Canonical direction: governing head (verb or noun) → PP_ATTACH → harf_al_jarr (PP anchor). Do not use reverse; direction is fixed.",
        "typical_trigger_signals": [
            "valency PP expectation (L8B)",
            "proximity to noun head",
        ],
        "arabic_role": AR_PP_ATTACH,
        "example": "سافر → PP_ATTACH → إلى (head=verb, dependent=harf/PP anchor)",
    },
    REL_IDAFA: {
        "label": REL_IDAFA,
        "arabic_name": "إضافة",
        "definition": "Mudaf linked to mudaf ilayhi (construct state). Canonical direction only: mudaf → IDAFA → mudaf_ilayhi (head=mudaf, dependent=mudaf ilayhi). Do not use reverse. Future (Stage 17): consider distinct arabic_role for head (MUDAF) vs dependent (MUDAF_ILAYH).",
        "typical_trigger_signals": [
            "L10B idafa edge confirmed",
            "construct state morphology",
        ],
        "arabic_role": AR_MUDAF,
        "example": "كتاب → IDAFA → الطالب (head=mudaf, dependent=mudaf ilayhi)",
    },
    REL_SIFA: {
        "label": REL_SIFA,
        "arabic_name": "نعت",
        "definition": "Adjective (sifa/naʿt) depending on noun (mawsuf). Direction always: head = noun (mawsuf), dependent = adjective (sifa). Link: noun → SIFA → adjective.",
        "typical_trigger_signals": [
            "L5 adjective typing",
            "agreement signals",
        ],
        "arabic_role": AR_NA3T,
        "example": "الطالب المجتهد — head=الطالب (noun), dependent=المجتهد (adjective); direction: noun → SIFA → adjective",
    },
    REL_INNA_NAME: {
        "label": REL_INNA_NAME,
        "arabic_name": "اسم إن",
        "definition": "High-confidence emphatic governance: إنَّ / أنَّ governing its noun. Canonical direction: emphatic operator → INNA_NAME → governed noun.",
        "typical_trigger_signals": ["ACC_TAWKID operator", "next noun-family token"],
        "arabic_role": AR_ISM_INNA,
        "example": "إِنَّ → INNA_NAME → المسلمين",
    },
    # Pass C
    REL_COORD: {
        "label": REL_COORD,
        "arabic_name": "عطف",
        "definition": "Coordination: head conjunct linked to dependent conjunct. Canonical direction: head_conjunct → COORD → dependent_conjunct.",
        "typical_trigger_signals": ["conjunction particle (waw, fa, thumma, aw, am) from L4/connectives"],
        "arabic_role": AR_ATF,
        "example": "خالد → COORD → محمد (head conjunct → dependent conjunct)",
    },
    REL_COORD_CONJ: {
        "label": REL_COORD_CONJ,
        "arabic_name": "حرف عطف",
        "definition": "Conjunction particle attached to the head of the coordination. Canonical direction: head_conjunct → COORD_CONJ → conjunction.",
        "typical_trigger_signals": ["waw, fa, thumma, aw, am"],
        "arabic_role": AR_ATF_CONJ,
        "example": "خالد → COORD_CONJ → و (head conjunct → conjunction)",
    },
    REL_APPOS: {
        "label": REL_APPOS,
        "arabic_name": "بدل",
        "definition": "Apposition / badal: main noun followed by appositive. Canonical direction: main_noun → APPOS → appositive.",
        "typical_trigger_signals": ["same case, same definiteness, adjacent, no governing particle between"],
        "arabic_role": AR_BADAL,
        "example": "الأستاذ → APPOS → أحمد (main noun → appositive)",
    },
    REL_TAMYIZ_CAND: {
        "label": REL_TAMYIZ_CAND,
        "arabic_name": "تمييز (مرشح)",
        "definition": "Tamyiz candidate — mark only; do not resolve. Signal to Stage 16 for clause-level resolution. No dependency link; use candidate_markers in output.",
        "typical_trigger_signals": [],
        "arabic_role": None,
        "example": "Marker only; no link.",
    },
    REL_HAL_CAND: {
        "label": REL_HAL_CAND,
        "arabic_name": "حال (مرشح)",
        "definition": "Hal candidate — mark only; do not resolve. Signal to Stage 16 for clause-level resolution. No dependency link; use candidate_markers in output.",
        "typical_trigger_signals": [],
        "arabic_role": None,
        "example": "Marker only; no link.",
    },
}
