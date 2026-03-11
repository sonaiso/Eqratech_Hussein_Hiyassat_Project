# -*- coding: utf-8 -*-
"""
Noun enrichment: derivation, number, gender, case, definite, pattern_type.
Uses c2b features and awzan_merged_final.csv for pattern type.
"""
from __future__ import annotations

import csv
from pathlib import Path
from typing import Any, Dict, Optional

from .models import NounFeatures

# Map وزن (template) to pattern_type for nouns — from Arabic morphology
_WEIGHT_TO_PATTERN_TYPE: Dict[str, str] = {
    "فَعَلَ": "فعل ماضي",
    "فَعْل": "مصدر أو اسم",
    "فَعْلَة": "مصدر أو اسم",
    "فَعْلُ": "مصدر أو اسم",
    "فَعْلِ": "مصدر أو اسم",
    "فَاعِل": "اسم فاعل",
    "فَاعِلَة": "اسم فاعل",
    "فَاعِلُون": "اسم فاعل",
    "فَاعِلَات": "اسم فاعل",
    "مَفْعُول": "اسم مفعول",
    "مَفْعُولَة": "اسم مفعول",
    "مَفْعِل": "اسم مكان/زمان",
    "مَفْعَل": "اسم مكان/زمان",
    "فَعِيل": "صفة مشبهة",
    "فَعِيلَة": "صفة مشبهة",
    "فَعُول": "صفة مشبهة",
    "أَفْعَل": "اسم تفضيل",
    "أَفْعَلَة": "اسم تفضيل",
    "تَفْعِيل": "مصدر",
    "تَفْعِلَة": "مصدر",
    "تَفَعُّل": "مصدر",
    "تَفَاعُل": "مصدر",
    "اسْتِفْعَال": "مصدر",
    "افْتِعَال": "مصدر",
    "انْفِعَال": "مصدر",
    "فَعَّال": "اسم فاعل",
    "فَعَّالَة": "اسم فاعل",
    "مُفَعِّل": "اسم مفعول/صيغة مبالغة",
    "مُفَعَّل": "اسم مفعول",
    "مُفَاعِل": "اسم مفعول",
    "فَعْلان": "صفة مشبهة",
    "فَعْلَى": "صفة مشبهة",
    "فَعْلَاء": "صفة مشبهة",
    "فَعْلَة": "مصدر أو اسم",
    "فَعَالَة": "مصدر",
    "فُعُول": "مصدر أو صفة",
    "فِعَال": "مصدر",
    "فَعَالَى": "جمع",
    "فَعَائِل": "جمع",
    "مَفَاعِل": "جمع",
    "مَفَاعِيل": "جمع",
    "فَوَاعِل": "جمع",
    "فَعْلَان": "صفة مشبهة",
}

_awzan_loaded: Optional[Dict[str, str]] = None


def _load_awzan() -> Dict[str, str]:
    """Load وزن -> example from awzan_merged_final.csv; use for pattern_type lookup."""
    global _awzan_loaded
    if _awzan_loaded is not None:
        return _awzan_loaded
    base = Path(__file__).resolve().parents[2]
    path = base / "data" / "awzan_merged_final.csv"
    out: Dict[str, str] = {}
    try:
        with path.open(encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                w = (row.get("الوزن") or "").strip()
                if w:
                    out[w] = (row.get("مثال") or "").strip()
    except Exception:
        pass
    _awzan_loaded = out
    return out


def _pattern_type_from_template(template: Optional[str]) -> Optional[str]:
    """Resolve pattern_type from c2b template or وزن."""
    if not template:
        return None
    t = template.strip()
    if t in _WEIGHT_TO_PATTERN_TYPE:
        return _WEIGHT_TO_PATTERN_TYPE[t]
    # Normalize: remove optional diacritics for lookup
    for key, val in _WEIGHT_TO_PATTERN_TYPE.items():
        if key.replace("َ", "").replace("ِ", "").replace("ُ", "").replace("ْ", "") == t.replace("َ", "").replace("ِ", "").replace("ُ", "").replace("ْ", ""):
            return val
    return t


def analyze_noun(
    word: str,
    stripped: str,
    root: str,
    c2b_features: Optional[Dict[str, Any]] = None,
    c2b_pattern_template: Optional[str] = None,
) -> NounFeatures:
    """
    Build noun features from c2b (number, gender, case, definite) and add pattern_type.
    """
    c2b_features = c2b_features or {}
    number = c2b_features.get("number")
    if number is None and isinstance(c2b_features.get("number"), str):
        number = c2b_features["number"]
    gender = c2b_features.get("gender")
    case = c2b_features.get("case")
    definite = c2b_features.get("definite")
    if isinstance(definite, str):
        definite = definite.lower() in ("true", "1", "نعم", "معرف")
    pattern_type = _pattern_type_from_template(c2b_pattern_template)
    return NounFeatures(
        number=number,
        gender=gender,
        case=case,
        definite=definite,
        pattern_type=pattern_type,
    )
