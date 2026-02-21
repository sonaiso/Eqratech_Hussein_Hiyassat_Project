"""Arabic-English mappings for I3rab terms.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Syntax Foundation
"""

from typing import Dict

# I3rab Type Mappings (Top 5 priority)
I3RAB_TYPE_AR_TO_EN: Dict[str, str] = {
    "مبتدأ": "mubtada",
    "خبر": "khabar",
    "فاعل": "fa'il",
    "مفعول به": "maf'ul_bihi",
    "حرف": "harf",
    # Additional types (lower priority)
    "نعت": "na't",
    "حال": "hal",
    "مضاف إليه": "mudaf_ilayhi",
    "بدل": "badal",
    "عطف": "atf",
}

I3RAB_TYPE_EN_TO_AR: Dict[str, str] = {v: k for k, v in I3RAB_TYPE_AR_TO_EN.items()}

# Case Mappings
CASE_AR_TO_EN: Dict[str, str] = {
    "مرفوع": "nominative",
    "منصوب": "accusative",
    "مجرور": "genitive",
}

CASE_EN_TO_AR: Dict[str, str] = {v: k for k, v in CASE_AR_TO_EN.items()}

# Case Marker Mappings
CASE_MARKER_AR_TO_EN: Dict[str, str] = {
    "الضمة": "damma",
    "الفتحة": "fatha",
    "الكسرة": "kasra",
    "الواو": "waw",
    "الياء": "ya",
    "الألف": "alif",
}

# Syntactic Role Mappings
I3RAB_TO_ROLE: Dict[str, str] = {
    "mubtada": "subject",
    "khabar": "predicate",
    "fa'il": "agent",
    "maf'ul_bihi": "object",
    "harf": "particle",
    "na't": "adjective",
    "hal": "adverb",
    "mudaf_ilayhi": "possessive",
}


def map_i3rab_to_role(i3rab_type_en: str) -> str:
    """Map I3rab type to syntactic role."""
    return I3RAB_TO_ROLE.get(i3rab_type_en, "unknown")


def map_ar_to_en(arabic_term: str, category: str) -> str:
    """Generic mapper for Arabic to English.
    
    Args:
        arabic_term: Arabic term
        category: 'i3rab_type', 'case', or 'case_marker'
    
    Returns:
        English equivalent or 'unknown'
    """
    mappings = {
        "i3rab_type": I3RAB_TYPE_AR_TO_EN,
        "case": CASE_AR_TO_EN,
        "case_marker": CASE_MARKER_AR_TO_EN,
    }
    
    return mappings.get(category, {}).get(arabic_term, "unknown")