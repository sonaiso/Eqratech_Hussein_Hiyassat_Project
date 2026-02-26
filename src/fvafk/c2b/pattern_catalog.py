"""
Pattern Catalog - Arabic Morphological Patterns
Comprehensive collection of verb forms, noun patterns, and broken plurals
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional
from enum import Enum


class PatternType(Enum):
    """Pattern types"""
    VERB_FORM_I = "verb_form_i"
    VERB_FORM_II = "verb_form_ii"
    VERB_FORM_III = "verb_form_iii"
    VERB_FORM_IV = "verb_form_iv"
    VERB_FORM_V = "verb_form_v"
    VERB_FORM_VI = "verb_form_vi"
    VERB_FORM_VII = "verb_form_vii"
    VERB_FORM_VIII = "verb_form_viii"
    VERB_FORM_IX = "verb_form_ix"
    VERB_FORM_X = "verb_form_x"
    
    NOUN_MASDAR = "noun_masdar"
    NOUN_ACTIVE_PARTICIPLE = "noun_active_participle"
    NOUN_PASSIVE_PARTICIPLE = "noun_passive_participle"
    NOUN_INSTRUMENT = "noun_instrument"
    NOUN_PLACE_TIME = "noun_place_time"
    
    BROKEN_PLURAL = "broken_plural"
    ADJECTIVE = "adjective"


@dataclass
class PatternTemplate:
    """Simple pattern template"""
    name: str
    template: str
    description: str
    pattern_type: str = "unknown"
    examples: Optional[List[str]] = None

    @property
    def pattern(self) -> str:
        """Alias for template, for compatibility."""
        return self.template


class PatternCategory(Enum):
    """Category of a pattern."""
    VERB = "VERB"
    NOUN = "NOUN"
    PLURAL = "PLURAL"
    PARTICIPLE = "PARTICIPLE"
    ADJECTIVE = "ADJECTIVE"
    OTHER = "OTHER"


@dataclass
class PatternInfo:
    """Rich information about a single morphological pattern."""
    template: str
    pattern_type: Any  # PatternType from morpheme
    category: PatternCategory
    form: Optional[str] = None
    meaning: Optional[str] = None
    frequency_rank: Optional[int] = None
    examples: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "template": self.template,
            "pattern_type": self.pattern_type.name if hasattr(self.pattern_type, "name") else str(self.pattern_type),
            "category": self.category.name,
            "form": self.form,
            "meaning": self.meaning,
            "frequency_rank": self.frequency_rank,
        }


@dataclass
class PatternMatch:
    """Result of a pattern match."""
    pattern_info: PatternInfo
    confidence: float
    matched_word: str = ""


class PatternCatalog:
    """Catalog of Arabic morphological patterns"""

    def __init__(self) -> None:
        self._pattern_info_cache: List[PatternInfo] = []
        self._build_cache()

    def _build_cache(self) -> None:
        from fvafk.c2b.morpheme import PatternType as MorphPatternType
        from fvafk.c2b.pattern_matcher import PatternDatabase

        db = PatternDatabase()
        _CATEGORY_MAP: Dict[str, PatternCategory] = {
            "verb": PatternCategory.VERB,
            "noun": PatternCategory.NOUN,
            "plural": PatternCategory.PLURAL,
        }
        _PARTICIPLE_TYPES = {
            MorphPatternType.ACTIVE_PARTICIPLE,
            MorphPatternType.PASSIVE_PARTICIPLE,
        }
        rank = 1
        for tpl in db.get_all():
            cat = _CATEGORY_MAP.get(tpl.category, PatternCategory.OTHER)
            if tpl.pattern_type in _PARTICIPLE_TYPES:
                cat = PatternCategory.PARTICIPLE
            info = PatternInfo(
                template=tpl.template,
                pattern_type=tpl.pattern_type,
                category=cat,
                form=tpl.form,
                meaning=tpl.meaning,
                frequency_rank=rank,
            )
            self._pattern_info_cache.append(info)
            rank += 1

    # ------------------------------------------------------------------ #
    # Read API                                                             #
    # ------------------------------------------------------------------ #

    def get_by_category(self, category: PatternCategory) -> List[PatternInfo]:
        return [p for p in self._pattern_info_cache if p.category == category]

    def get_participle_patterns(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.PARTICIPLE)

    def get_verb_forms(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.VERB)

    def get_most_common(self, limit: int = 20) -> List[PatternInfo]:
        ranked = [p for p in self._pattern_info_cache if p.frequency_rank is not None]
        ranked.sort(key=lambda p: p.frequency_rank)  # type: ignore[arg-type]
        return ranked[:limit]

    def search_patterns(
        self,
        category: Optional[PatternCategory] = None,
        form: Optional[str] = None,
        min_frequency_rank: Optional[int] = None,
    ) -> List[PatternInfo]:
        results = self._pattern_info_cache
        if category is not None:
            results = [p for p in results if p.category == category]
        if form is not None:
            results = [p for p in results if p.form == form]
        if min_frequency_rank is not None:
            results = [
                p for p in results
                if p.frequency_rank is not None and p.frequency_rank <= min_frequency_rank
            ]
        return results

    def get_pattern_by_template(self, template: str) -> Optional[PatternInfo]:
        for p in self._pattern_info_cache:
            if p.template == template:
                return p
        return None

    def match_pattern(self, word: str, root: Any) -> Optional[PatternMatch]:
        if not word:
            return None
        from fvafk.c2b.pattern_matcher import PatternMatcher
        from fvafk.c2b.morpheme import PatternType as MorphPatternType

        matcher = PatternMatcher()
        result = matcher.match(word, root)
        if result is None:
            return None

        # Find matching PatternInfo
        for info in self._pattern_info_cache:
            if info.pattern_type == result.pattern_type and info.template == result.template:
                confidence = float(result.features.get("confidence", 0.8))
                return PatternMatch(pattern_info=info, confidence=confidence, matched_word=word)

        # Fallback: create PatternInfo on-the-fly
        _fallback_map: Dict[str, PatternCategory] = {
            "verb": PatternCategory.VERB,
            "noun": PatternCategory.NOUN,
            "plural": PatternCategory.PLURAL,
        }
        cat = _fallback_map.get(result.features.get("category", ""), PatternCategory.OTHER)
        info = PatternInfo(
            template=result.template or "",
            pattern_type=result.pattern_type,
            category=cat,
            form=result.features.get("form"),
            meaning=result.features.get("meaning"),
        )
        confidence = float(result.features.get("confidence", 0.8))
        return PatternMatch(pattern_info=info, confidence=confidence, matched_word=word)

    def get_statistics(self) -> Dict[str, int]:
        stats: Dict[str, int] = {"total_patterns": len(self._pattern_info_cache)}
        stats["category_verb"] = sum(
            1 for p in self._pattern_info_cache if p.category == PatternCategory.VERB
        )
        stats["category_noun"] = sum(
            1 for p in self._pattern_info_cache
            if p.category in {PatternCategory.NOUN, PatternCategory.PARTICIPLE}
        )
        stats["category_plural"] = sum(
            1 for p in self._pattern_info_cache if p.category == PatternCategory.PLURAL
        )
        return stats

    # ------------------------------------------------------------------ #
    # Legacy class-method API (used by test_verse_integration.py)         #
    # ------------------------------------------------------------------ #

    @classmethod
    def load_full_catalog(cls) -> Dict[str, List["PatternTemplate"]]:
        """Load complete pattern catalog"""
        return {
            "verb_forms": cls._load_verb_patterns(),
            "noun_patterns": cls._load_noun_patterns(),
            "broken_plurals": cls._load_broken_plural_patterns(),
            "adjectives": cls._load_adjective_patterns(),
        }
    
    @classmethod
    def _load_verb_patterns(cls) -> List[PatternTemplate]:
        """Load verb form patterns (Forms I-X)"""
        return [
            # Form I (فَعَلَ)
            PatternTemplate(
                name="FORM_I_FATHA",
                template="فَعَلَ",
                description="Form I - فَتَحَ pattern",
                pattern_type="verb_form_i",
                examples=["كَتَبَ", "ذَهَبَ", "فَعَلَ"]
            ),
            PatternTemplate(
                name="FORM_I_KASRA",
                template="فَعِلَ",
                description="Form I - فَهِمَ pattern",
                pattern_type="verb_form_i",
                examples=["شَرِبَ", "عَلِمَ", "فَهِمَ"]
            ),
            PatternTemplate(
                name="FORM_I_DAMMA",
                template="فَعُلَ",
                description="Form I - حَسُنَ pattern",
                pattern_type="verb_form_i",
                examples=["حَسُنَ", "كَرُمَ", "عَظُمَ"]
            ),
            
            # Form II (فَعَّلَ)
            PatternTemplate(
                name="FORM_II",
                template="فَعَّلَ",
                description="Form II - causative/intensive",
                pattern_type="verb_form_ii",
                examples=["عَلَّمَ", "كَسَّرَ", "فَهَّمَ"]
            ),
            
            # Form III (فَاعَلَ)
            PatternTemplate(
                name="FORM_III",
                template="فَاعَلَ",
                description="Form III - mutual action",
                pattern_type="verb_form_iii",
                examples=["قَاتَلَ", "جَاهَدَ", "سَافَرَ"]
            ),
            
            # Form IV (أَفْعَلَ)
            PatternTemplate(
                name="FORM_IV",
                template="أَفْعَلَ",
                description="Form IV - causative",
                pattern_type="verb_form_iv",
                examples=["أَكْرَمَ", "أَخْرَجَ", "أَسْلَمَ"]
            ),
            
            # Form V (تَفَعَّلَ)
            PatternTemplate(
                name="FORM_V",
                template="تَفَعَّلَ",
                description="Form V - reflexive of Form II",
                pattern_type="verb_form_v",
                examples=["تَعَلَّمَ", "تَكَلَّمَ", "تَقَدَّمَ"]
            ),
            
            # Form VI (تَفَاعَلَ)
            PatternTemplate(
                name="FORM_VI",
                template="تَفَاعَلَ",
                description="Form VI - reflexive of Form III",
                pattern_type="verb_form_vi",
                examples=["تَقَاتَلَ", "تَعَاوَنَ", "تَبَادَلَ"]
            ),
            
            # Form VII (اِنْفَعَلَ)
            PatternTemplate(
                name="FORM_VII",
                template="اِنْفَعَلَ",
                description="Form VII - passive/reflexive",
                pattern_type="verb_form_vii",
                examples=["اِنْكَسَرَ", "اِنْفَتَحَ", "اِنْقَطَعَ"]
            ),
            
            # Form VIII (اِفْتَعَلَ)
            PatternTemplate(
                name="FORM_VIII",
                template="اِفْتَعَلَ",
                description="Form VIII - reflexive",
                pattern_type="verb_form_viii",
                examples=["اِجْتَمَعَ", "اِخْتَارَ", "اِشْتَغَلَ"]
            ),
            
            # Form IX (اِفْعَلَّ)
            PatternTemplate(
                name="FORM_IX",
                template="اِفْعَلَّ",
                description="Form IX - colors/defects",
                pattern_type="verb_form_ix",
                examples=["اِحْمَرَّ", "اِخْضَرَّ", "اِصْفَرَّ"]
            ),
            
            # Form X (اِسْتَفْعَلَ)
            PatternTemplate(
                name="FORM_X",
                template="اِسْتَفْعَلَ",
                description="Form X - seeking/requesting",
                pattern_type="verb_form_x",
                examples=["اِسْتَخْرَجَ", "اِسْتَقْبَلَ", "اِسْتَغْفَرَ"]
            ),
        ]
    
    @classmethod
    def _load_noun_patterns(cls) -> List[PatternTemplate]:
        """Load noun patterns"""
        return [
            # Masdar patterns
            PatternTemplate(
                name="MASDAR_FACL",
                template="فَعْل",
                description="Masdar Form I pattern",
                pattern_type="noun_masdar",
                examples=["ضَرْب", "أَكْل", "فَتْح"]
            ),
            PatternTemplate(
                name="MASDAR_FICAAL",
                template="فِعَال",
                description="Masdar Form I pattern",
                pattern_type="noun_masdar",
                examples=["جِهَاد", "قِتَال", "نِزَال"]
            ),
            PatternTemplate(
                name="MASDAR_TAFCEEL",
                template="تَفْعِيل",
                description="Masdar Form II",
                pattern_type="noun_masdar",
                examples=["تَعْلِيم", "تَكْسِير", "تَفْهِيم"]
            ),
            
            # Active participle
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_FAACIL",
                template="فَاعِل",
                description="Active participle Form I",
                pattern_type="noun_active_participle",
                examples=["كَاتِب", "ذَاهِب", "قَارِئ"]
            ),
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_MUFACCIL",
                template="مُفَعِّل",
                description="Active participle Form II",
                pattern_type="noun_active_participle",
                examples=["مُعَلِّم", "مُكَسِّر", "مُفَهِّم"]
            ),
            
            # Passive participle
            PatternTemplate(
                name="PASSIVE_PARTICIPLE_MAFCOOL",
                template="مَفْعُول",
                description="Passive participle Form I",
                pattern_type="noun_passive_participle",
                examples=["مَكْتُوب", "مَقْرُوء", "مَفْهُوم"]
            ),
            
            # Instrument nouns
            PatternTemplate(
                name="INSTRUMENT_MIFCAAL",
                template="مِفْعَال",
                description="Instrument noun",
                pattern_type="noun_instrument",
                examples=["مِفْتَاح", "مِقْيَاس", "مِنْشَار"]
            ),
            
            # Place/Time nouns
            PatternTemplate(
                name="PLACE_MAFCAL",
                template="مَفْعَل",
                description="Place/time noun",
                pattern_type="noun_place_time",
                examples=["مَكْتَب", "مَدْرَسَة", "مَطْبَخ"]
            ),
        ]
    
    @classmethod
    def _load_broken_plural_patterns(cls) -> List[PatternTemplate]:
        """Load broken plural patterns"""
        return [
            PatternTemplate(
                name="PLURAL_AFCAAL",
                template="أَفْعَال",
                description="Broken plural pattern",
                pattern_type="broken_plural",
                examples=["أَقْلَام", "أَبْوَاب", "أَيَّام"]
            ),
            PatternTemplate(
                name="PLURAL_FUCOOL",
                template="فُعُول",
                description="Broken plural pattern",
                pattern_type="broken_plural",
                examples=["بُيُوت", "عُيُون", "قُلُوب"]
            ),
            PatternTemplate(
                name="PLURAL_FACAALIL",
                template="فَعَائِل",
                description="Broken plural pattern",
                pattern_type="broken_plural",
                examples=["رَسَائِل", "مَسَائِل", "وَسَائِل"]
            ),
            PatternTemplate(
                name="PLURAL_FUCALAA",
                template="فُعَلَاء",
                description="Broken plural pattern",
                pattern_type="broken_plural",
                examples=["عُلَمَاء", "شُعَرَاء", "فُقَهَاء"]
            ),
        ]
    
    @classmethod
    def _load_adjective_patterns(cls) -> List[PatternTemplate]:
        """Load adjective patterns"""
        return [
            PatternTemplate(
                name="ADJECTIVE_FACEEL",
                template="فَعِيل",
                description="Intensive adjective",
                pattern_type="adjective",
                examples=["كَرِيم", "رَحِيم", "عَظِيم"]
            ),
            PatternTemplate(
                name="ADJECTIVE_AFCAL",
                template="أَفْعَل",
                description="Comparative/superlative",
                pattern_type="adjective",
                examples=["أَكْبَر", "أَصْغَر", "أَحْسَن"]
            ),
        ]


_CATEGORY_MAP_SIMPLE: Dict[str, PatternCategory] = {
    "verb": PatternCategory.VERB,
    "noun": PatternCategory.NOUN,
    "plural": PatternCategory.PLURAL,
}


def create_default_catalog() -> PatternCatalog:
    """Factory function that creates a default PatternCatalog."""
    return PatternCatalog()
