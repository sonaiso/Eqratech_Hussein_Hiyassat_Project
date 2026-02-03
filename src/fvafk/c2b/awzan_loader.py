from __future__ import annotations

import csv
from pathlib import Path
from typing import Dict, List, Optional

from .morpheme import PatternType


class AwzanPatternLoader:
    CSV_PATH = Path(__file__).resolve().parents[3] / "awzan-claude-atwah.csv"

    PATTERN_TYPE_MAP: Dict[str, PatternType] = {
        "فَعَلَ": PatternType.FORM_I,
        "فَعِلَ": PatternType.FORM_I,
        "فَعُلَ": PatternType.FORM_I,
        "فَعَّلَ": PatternType.FORM_II,
        "فَاعَلَ": PatternType.FORM_III,
        "أَفْعَلَ": PatternType.FORM_IV,
        "تَفَعَّلَ": PatternType.FORM_V,
        "تَفَاعَلَ": PatternType.FORM_VI,
        "انْفَعَلَ": PatternType.FORM_VII,
        "افْتَعَلَ": PatternType.FORM_VIII,
        "اسْتَفْعَلَ": PatternType.FORM_X,
        "مَفْعُول": PatternType.PASSIVE_PARTICIPLE,
        "فَاعِل": PatternType.ACTIVE_PARTICIPLE,
        "مَفْعَل": PatternType.PLACE_TIME_NOUN,
        "فِعَال": PatternType.VERBAL_NOUN,
        "فَعِيل": PatternType.INTENSIVE,
        "أَفْعَل": PatternType.ELATIVE,
        "فَاعِلُون": PatternType.SOUND_MASCULINE_PLURAL,
        "فَاعِلِين": PatternType.SOUND_MASCULINE_PLURAL,
        "فَاعِلَات": PatternType.SOUND_FEMININE_PLURAL,
        "فُعُول": PatternType.BROKEN_PLURAL_FUUL,
        "فِعَال": PatternType.BROKEN_PLURAL_FIAAL,
        "أَفْعَال": PatternType.BROKEN_PLURAL_AFAAL,
        "فِعَل": PatternType.BROKEN_PLURAL_FIUL,
        "فَعِيْلَة": PatternType.INTENSIVE,
        "فَعِيل": PatternType.INTENSIVE,
        "مَفْعَلَة": PatternType.PLACE_TIME_NOUN,
        "مِفْعَال": PatternType.PLACE_TIME_NOUN,
    }

    @classmethod
    def load(cls) -> List[PatternTemplate]:
        patterns: List[dict] = []
        if not cls.CSV_PATH.exists():
            return patterns
        with open(cls.CSV_PATH, encoding="utf-8-sig", newline="") as handle:
            reader = csv.DictReader(handle, delimiter="\t")
            seen = set()
            for row in reader:
                template = (row.get("الوزن") or "").strip()
                if not template or template in seen:
                    continue
                seen.add(template)
                pattern_type = cls.PATTERN_TYPE_MAP.get(template, PatternType.UNKNOWN)
                category = cls._infer_category(row, pattern_type)
                patterns.append(
                    {
                        "template": template,
                        "pattern_type": pattern_type,
                        "category": category,
                        "form": row.get("الاسم") or None,
                        "meaning": row.get("الوصف") or None,
                        "cv_simple": row.get("CV") or None,
                        "cv_detailed": row.get("Detailed_CV") or None,
                        "cv_advanced": row.get("Advanced_CV") or None,
                        "notes": row.get("ملاحظات") or None,
                    }
                )
        return patterns

    @staticmethod
    def _infer_category(row: Dict[str, str], pattern_type: PatternType) -> str:
        label = (row.get("الاسم") or "").strip()
        description = (row.get("الوصف") or "").strip()
        if "جمع" in label or "جمع" in description:
            return "plural"
        if description.startswith("اسم") or label.startswith("اسم") or "صفة" in description:
            return "noun"
        if pattern_type in {
            PatternType.SOUND_MASCULINE_PLURAL,
            PatternType.SOUND_FEMININE_PLURAL,
            PatternType.BROKEN_PLURAL_AFAAL,
            PatternType.BROKEN_PLURAL_FIAAL,
            PatternType.BROKEN_PLURAL_FUUL,
            PatternType.BROKEN_PLURAL_FIUL,
        }:
            return "plural"
        if pattern_type != PatternType.UNKNOWN:
            return "verb"
        return "noun"
