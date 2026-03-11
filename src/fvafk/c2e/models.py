# -*- coding: utf-8 -*-
"""Data classes for c2e enrichment output."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional


@dataclass
class VerbFeatures:
    """صرف الفعل: زمن، بناء، شخص، عدد، جنس، قالب."""
    tense: str   # ماضي | مضارع | أمر
    voice: str   # معلوم | مجهول
    person: int  # 1 | 2 | 3
    number: str  # مفرد | مثنى | جمع
    gender: str  # مذكر | مؤنث
    pattern: str  # e.g. فَعَلَ

    def to_dict(self) -> Dict[str, Any]:
        return {
            "tense": self.tense,
            "voice": self.voice,
            "person": self.person,
            "number": self.number,
            "gender": self.gender,
            "pattern": self.pattern,
        }


@dataclass
class NounFeatures:
    """صرف الاسم: عدد، جنس، إعراب، تنكير/تعريف، نوع القالب."""
    number: Optional[str] = None
    gender: Optional[str] = None
    case: Optional[str] = None
    definite: Optional[bool] = None
    pattern_type: Optional[str] = None  # مصدر | اسم فاعل | اسم مفعول | etc.

    def to_dict(self) -> Dict[str, Any]:
        return {
            "number": self.number,
            "gender": self.gender,
            "case": self.case,
            "definite": self.definite,
            "pattern_type": self.pattern_type,
        }


@dataclass
class EnrichmentResult:
    word: str
    derivation: str  # "جامد" | "مشتق"
    verb_features: Optional[VerbFeatures] = None
    noun_features: Optional[NounFeatures] = None
    confidence: float = 0.0
    i3rab_text: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {
            "derivation": self.derivation,
            "confidence": self.confidence,
        }
        if self.verb_features is not None:
            out["verb"] = self.verb_features.to_dict()
        else:
            out["verb"] = None
        if self.noun_features is not None:
            out["noun"] = self.noun_features.to_dict()
        else:
            out["noun"] = None
        out["i3rab_text"] = self.i3rab_text
        return out
