"""
Pattern Catalog - Arabic Morphological Patterns
Comprehensive collection of verb forms, noun patterns, and broken plurals
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from enum import Enum
import unicodedata

from .morpheme import PatternType, Root
from .pattern_matcher import PatternDatabase, PatternMatcher


class PatternCategory(Enum):
    """High-level pattern categories."""
    VERB = "verb"
    NOUN = "noun"
    PLURAL = "plural"
    PARTICIPLE = "participle"


_PARTICIPLE_TYPES = {PatternType.ACTIVE_PARTICIPLE, PatternType.PASSIVE_PARTICIPLE}


def _category_from_template(template) -> PatternCategory:
    """Map a PatternTemplate (from pattern_matcher) to PatternCategory."""
    if template.pattern_type in _PARTICIPLE_TYPES:
        return PatternCategory.PARTICIPLE
    cat = template.category
    if cat == "verb":
        return PatternCategory.VERB
    if cat == "plural":
        return PatternCategory.PLURAL
    return PatternCategory.NOUN


@dataclass
class PatternInfo:
    """Rich information about a single Arabic morphological pattern."""
    template: str
    pattern_type: PatternType
    category: PatternCategory
    form: Optional[str] = None
    meaning: Optional[str] = None
    frequency_rank: Optional[int] = None
    # Legacy fields kept for backward compatibility with load_full_catalog() callers
    name: Optional[str] = None
    description: Optional[str] = None
    examples: Optional[List[str]] = None

    @property
    def pattern(self) -> str:
        """Alias for template (legacy compatibility)."""
        return self.template

    def to_dict(self) -> Dict[str, Any]:
        return {
            "template": self.template,
            "pattern_type": self.pattern_type.name,
            "category": self.category.name,
            "form": self.form,
            "meaning": self.meaning,
            "frequency_rank": self.frequency_rank,
        }


@dataclass
class PatternMatch:
    """Result of matching a word against the pattern catalog."""
    confidence: float
    pattern_info: PatternInfo


def _build_pattern_info_cache() -> List[PatternInfo]:
    """Build PatternInfo list from PatternDatabase."""
    db = PatternDatabase()
    seen_templates: set = set()
    result: List[PatternInfo] = []
    # Assign frequency ranks to the first occurrence of each unique template
    rank = 1
    for tmpl in db.get_all():
        if tmpl.template in seen_templates:
            continue
        seen_templates.add(tmpl.template)
        result.append(PatternInfo(
            template=tmpl.template,
            pattern_type=tmpl.pattern_type,
            category=_category_from_template(tmpl),
            form=tmpl.form,
            meaning=tmpl.meaning,
            frequency_rank=rank,
            name=tmpl.pattern_type.name,
            description=tmpl.meaning or tmpl.pattern_type.value.replace("_", " ").title(),
        ))
        rank += 1
    return result


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _morpheme_pattern_type_to_category(pt: Any) -> PatternCategory:
    """Map fvafk.c2b.morpheme.PatternType → PatternCategory."""
    name = pt.name if hasattr(pt, "name") else str(pt)
    if name.startswith("FORM_"):
        return PatternCategory.VERB
    if name in ("ACTIVE_PARTICIPLE", "PASSIVE_PARTICIPLE"):
        return PatternCategory.PARTICIPLE
    if name.startswith("BROKEN_PLURAL") or name.startswith("SOUND_"):
        return PatternCategory.PLURAL
    if name in ("INTENSIVE", "ELATIVE", "COLOUR"):
        return PatternCategory.ADJECTIVE
    return PatternCategory.NOUN


_FORM_ROMAN: Dict[str, str] = {
    "FORM_I": "I", "FORM_II": "II", "FORM_III": "III",
    "FORM_IV": "IV", "FORM_V": "V", "FORM_VI": "VI",
    "FORM_VII": "VII", "FORM_VIII": "VIII", "FORM_IX": "IX",
    "FORM_X": "X",
}

_CATEGORY_STR_MAP: Dict[str, PatternCategory] = {
    "verb": PatternCategory.VERB,
    "noun": PatternCategory.NOUN,
    "broken_plural": PatternCategory.PLURAL,
    "adjective": PatternCategory.ADJECTIVE,
    "participle": PatternCategory.PARTICIPLE,
}

# Frequency rank: most common forms first (lower = more frequent)
_FREQUENCY_RANK: Dict[str, int] = {
    "I": 1, "II": 2, "III": 3, "IV": 4, "V": 5,
    "VI": 6, "VII": 7, "VIII": 8, "IX": 9, "X": 10,
}
# Non-verb patterns start their ranks after the 10 verb forms
_NON_VERB_RANK_START = len(_FREQUENCY_RANK) + 1  # 11


# Arabic diacritics to strip for pattern matching
_DIACRITICS = set('\u064b\u064c\u064d\u064e\u064f\u0650\u0651\u0652\u0653\u0654\u0655')


def _strip_diacritics(text: str) -> str:
    return ''.join(c for c in text if c not in _DIACRITICS)


class PatternCategory(Enum):
    """High-level category for patterns."""
    VERB = "VERB"
    NOUN = "NOUN"
    PLURAL = "PLURAL"
    PARTICIPLE = "PARTICIPLE"
    MASDAR = "MASDAR"
    ADJECTIVE = "ADJECTIVE"


@dataclass
class PatternInfo:
    """Rich pattern info entry for the extended PatternCatalog."""
    template: str
    pattern_type: object  # morpheme.PatternType or None
    category: PatternCategory
    form: Optional[str] = None
    meaning: Optional[str] = None
    frequency_rank: Optional[int] = None
    examples: Optional[List[str]] = None

    def to_dict(self) -> Dict:
        return {
            "template": self.template,
            "pattern_type": self.pattern_type.value if self.pattern_type else None,
            "category": self.category.name,
            "form": self.form,
            "meaning": self.meaning,
            "frequency_rank": self.frequency_rank,
        }


@dataclass
class PatternMatch:
    """Result of matching a word against pattern catalog."""
    pattern_info: PatternInfo
    confidence: float
    matched_template: str = ""


# Mapping from existing PatternTemplate name to PatternInfo fields
# Keys are full name prefixes followed by _ or exact match
# (form, category, pattern_type_value, frequency_rank)
_TEMPLATE_NAME_MAP: Dict[str, Tuple] = {
    "FORM_I": ("I", PatternCategory.VERB, "form_i", 1),
    "FORM_II": ("II", PatternCategory.VERB, "form_ii", 2),
    "FORM_III": ("III", PatternCategory.VERB, "form_iii", 3),
    "FORM_IV": ("IV", PatternCategory.VERB, "form_iv", 4),
    "FORM_V": ("V", PatternCategory.VERB, "form_v", 5),
    "FORM_VI": ("VI", PatternCategory.VERB, "form_vi", 6),
    "FORM_VII": ("VII", PatternCategory.VERB, "form_vii", 7),
    "FORM_VIII": ("VIII", PatternCategory.VERB, "form_viii", 8),
    "FORM_IX": ("IX", PatternCategory.VERB, "form_ix", 9),
    "FORM_X": ("X", PatternCategory.VERB, "form_x", 10),
    "ACTIVE_PARTICIPLE": (None, PatternCategory.PARTICIPLE, "active_participle", 11),
    "PASSIVE_PARTICIPLE": (None, PatternCategory.PARTICIPLE, "passive_participle", 12),
    "MASDAR": (None, PatternCategory.MASDAR, "verbal_noun", 13),
    "NOUN_ACTIVE": (None, PatternCategory.PARTICIPLE, "active_participle", 15),
    "NOUN_PASSIVE": (None, PatternCategory.PARTICIPLE, "passive_participle", 16),
    "NOUN_INSTRUMENT": (None, PatternCategory.NOUN, "instrument", 17),
    "NOUN_PLACE": (None, PatternCategory.NOUN, "place_time_noun", 18),
    "NOUN_MASDAR": (None, PatternCategory.MASDAR, "verbal_noun", 14),
    "NOUN": (None, PatternCategory.NOUN, "abstract_noun", 19),
    "BROKEN_PLURAL": (None, PatternCategory.PLURAL, "broken_plural_fuul", 20),
    "PLURAL": (None, PatternCategory.PLURAL, "broken_plural_fuul", 21),
    "INSTRUMENT": (None, PatternCategory.NOUN, "instrument", 22),
    "ADJECTIVE": (None, PatternCategory.ADJECTIVE, "unknown", 23),
}


def _template_to_pattern_info(tmpl: PatternTemplate) -> PatternInfo:
    """Convert a PatternTemplate to PatternInfo."""
    from fvafk.c2b.morpheme import PatternType as MorphemePatternType
    form = None
    category = PatternCategory.NOUN
    pt_value = "unknown"
    freq = None

    name_upper = tmpl.name.upper()
    # Sort keys by length descending to match most specific key first
    for key in sorted(_TEMPLATE_NAME_MAP.keys(), key=len, reverse=True):
        # Match if name == key or name starts with key + "_"
        if name_upper == key or name_upper.startswith(key + "_"):
            f, cat, ptv, rank = _TEMPLATE_NAME_MAP[key]
            form = f
            category = cat
            pt_value = ptv
            freq = rank
            break
    else:
        # Fallback based on pattern_type string
        ptype = (tmpl.pattern_type or "").lower()
        if "verb" in ptype:
            category = PatternCategory.VERB
        elif "plural" in ptype:
            category = PatternCategory.PLURAL
        elif "adjective" in ptype:
            category = PatternCategory.ADJECTIVE

    try:
        morpheme_pt = MorphemePatternType(pt_value)
    except ValueError:
        morpheme_pt = MorphemePatternType.UNKNOWN

    return PatternInfo(
        template=tmpl.template,
        pattern_type=morpheme_pt,
        category=category,
        form=form,
        meaning=tmpl.description,
        frequency_rank=freq,
        examples=tmpl.examples,
    )


class PatternCatalog:
    """Catalog of Arabic morphological patterns"""

    def __init__(self) -> None:
        self._pattern_info_cache: List[PatternInfo] = self._build_cache()

    def _build_cache(self) -> List[PatternInfo]:
        full = self.load_full_catalog()
        result = []
        for _cat_name, templates in full.items():
            for tmpl in templates:
                result.append(_template_to_pattern_info(tmpl))
        return result

    def get_by_category(self, category: PatternCategory) -> List[PatternInfo]:
        return [p for p in self._pattern_info_cache if p.category == category]

    def get_participle_patterns(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.PARTICIPLE)

    def get_verb_forms(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.VERB)

    def get_most_common(self, limit: int = 20) -> List[PatternInfo]:
        ranked = [p for p in self._pattern_info_cache if p.frequency_rank is not None]
        ranked.sort(key=lambda p: p.frequency_rank)
        return ranked[:limit]

    def get_statistics(self) -> Dict[str, int]:
        stats: Dict[str, int] = {"total_patterns": len(self._pattern_info_cache)}
        for cat in PatternCategory:
            count = sum(1 for p in self._pattern_info_cache if p.category == cat)
            stats[f"category_{cat.name.lower()}"] = count
        return stats

    def get_pattern_by_template(self, template: str) -> Optional[PatternInfo]:
        for p in self._pattern_info_cache:
            if p.template == template:
                return p
        return None

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

    def match_pattern(self, word: str, root) -> Optional[PatternMatch]:
        """Match a word against the pattern catalog given its root."""
        if not word:
            return None
        root_letters = getattr(root, 'letters', ())
        if len(root_letters) < 3:
            return None

        r1, r2, r3 = root_letters[0], root_letters[1], root_letters[2]

        # Use placeholder-based substitution to avoid root-letter interference.
        # Placeholders are from the Unicode Private Use Area (U+E000–U+F8FF) which
        # are guaranteed never to appear in Arabic text, preventing any conflict when
        # a root letter happens to equal a pattern letter (e.g. ف, ع, ل themselves).
        _PF = '\uE001'  # placeholder for ف
        _PA = '\uE002'  # placeholder for ع
        _PL = '\uE003'  # placeholder for ل

        def _apply_substitution(template: str) -> str:
            candidate = (template
                         .replace('\u0641', _PF)   # ف → placeholder
                         .replace('\u0639', _PA)   # ع → placeholder
                         .replace('\u0644', _PL))  # ل → placeholder
            return (candidate
                    .replace(_PF, r1)
                    .replace(_PA, r2)
                    .replace(_PL, r3))

        # Tanwin marks to strip for the intermediate pass
        _TANWIN = {'\u064b', '\u064c', '\u064d'}  # ً ٌ ٍ

        def _strip_tanwin(text: str) -> str:
            return ''.join(c for c in text if c not in _TANWIN)

        # Pass 1: exact match with full diacritics
        for info in self._pattern_info_cache:
            candidate = _apply_substitution(info.template)
            if candidate == word:
                return PatternMatch(pattern_info=info, confidence=1.0,
                                    matched_template=info.template)

        # Pass 2: strip tanwin only (handles indefinite forms like كَاتِبٌ → كَاتِب)
        word_no_tanwin = _strip_tanwin(word)
        for info in self._pattern_info_cache:
            candidate = _apply_substitution(info.template)
            if candidate == word_no_tanwin:
                return PatternMatch(pattern_info=info, confidence=0.95,
                                    matched_template=info.template)

        # Pass 3: strip all diacritics (fuzzy match)
        word_bare = _strip_diacritics(word)
        for info in self._pattern_info_cache:
            tmpl_bare = _strip_diacritics(info.template)
            candidate = _apply_substitution(tmpl_bare)
            if candidate == word_bare:
                return PatternMatch(pattern_info=info, confidence=0.8,
                                    matched_template=info.template)

        return None

    @classmethod
    def load_full_catalog(cls) -> Dict[str, List[PatternTemplate]]:
        """Load complete pattern catalog"""
        return {
            "total_patterns": len(self._pattern_info_cache),
            "category_verb": len(self.get_by_category(PatternCategory.VERB)),
            "category_noun": len(self.get_by_category(PatternCategory.NOUN)),
            "category_plural": len(self.get_by_category(PatternCategory.PLURAL)),
            "category_participle": len(self.get_by_category(PatternCategory.PARTICIPLE)),
        }

    # ------------------------------------------------------------------
    # Legacy class-method API (kept for backward compatibility)
    # ------------------------------------------------------------------

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
            PatternTemplate(
                name="PLACE_MAFCIL",
                template="مَفْعِل",
                description="Place/time noun variant",
                pattern_type="noun_place_time",
                examples=["مَنْزِل", "مَسْجِد", "مَجْلِس"]
            ),
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_MUFAACIL",
                template="مُفَاعِل",
                description="Active participle Form III",
                pattern_type="noun_active_participle",
                examples=["مُقَاتِل", "مُسَافِر", "مُعَاوِن"]
            ),
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_MUTAFACCIL",
                template="مُتَفَعِّل",
                description="Active participle Form V",
                pattern_type="noun_active_participle",
                examples=["مُتَعَلِّم", "مُتَكَلِّم", "مُتَقَدِّم"]
            ),
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_MUNFACIL",
                template="مُنْفَعِل",
                description="Active participle Form VII",
                pattern_type="noun_active_participle",
                examples=["مُنْكَسِر", "مُنْفَتِح", "مُنْقَطِع"]
            ),
            PatternTemplate(
                name="ACTIVE_PARTICIPLE_MUFTACIL",
                template="مُفْتَعِل",
                description="Active participle Form VIII",
                pattern_type="noun_active_participle",
                examples=["مُجْتَمِع", "مُخْتَار", "مُشْتَغِل"]
            ),
            PatternTemplate(
                name="PASSIVE_PARTICIPLE_MUFACCAL",
                template="مُفَعَّل",
                description="Passive participle Form II",
                pattern_type="noun_passive_participle",
                examples=["مُعَلَّم", "مُكَسَّر", "مُقَدَّم"]
            ),
            PatternTemplate(
                name="PASSIVE_PARTICIPLE_MUFAACAL",
                template="مُفَاعَل",
                description="Passive participle Form III",
                pattern_type="noun_passive_participle",
                examples=["مُقَاتَل", "مُسَافَر", "مُكَافَأ"]
            ),
            PatternTemplate(
                name="MASDAR_MUFAACALA",
                template="مُفَاعَلَة",
                description="Masdar Form III",
                pattern_type="noun_masdar",
                examples=["مُقَاتَلَة", "مُشَارَكَة", "مُسَاعَدَة"]
            ),
            PatternTemplate(
                name="MASDAR_TAFACUL",
                template="تَفَاعُل",
                description="Masdar Form VI",
                pattern_type="noun_masdar",
                examples=["تَعَاوُن", "تَبَادُل", "تَفَاعُل"]
            ),
            PatternTemplate(
                name="MASDAR_IFTICAAL",
                template="اِفْتِعَال",
                description="Masdar Form VIII",
                pattern_type="noun_masdar",
                examples=["اِجْتِمَاع", "اِخْتِيَار", "اِشْتِغَال"]
            ),
            PatternTemplate(
                name="MASDAR_ISTIFCAAL",
                template="اِسْتِفْعَال",
                description="Masdar Form X",
                pattern_type="noun_masdar",
                examples=["اِسْتِعْمَال", "اِسْتِقْبَال", "اِسْتِخْدَام"]
            ),
            PatternTemplate(
                name="NOUN_FACL",
                template="فَعْل",
                description="Simple verbal noun",
                pattern_type="noun_masdar",
                examples=["عِلْم", "حُكْم", "فَهْم"]
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
            PatternTemplate(
                name="PLURAL_FICAAL",
                template="فِعَال",
                description="Broken plural - fiʿāl pattern",
                pattern_type="broken_plural",
                examples=["رِجَال", "كِتَاب", "جِبَال"]
            ),
            PatternTemplate(
                name="PLURAL_AFCUL",
                template="أَفْعُل",
                description="Broken plural - afʿul pattern",
                pattern_type="broken_plural",
                examples=["أَنْفُس", "أَعْيُن", "أَيْدٍ"]
            ),
            PatternTemplate(
                name="PLURAL_FUCAL",
                template="فُعَل",
                description="Broken plural - fuʿal pattern",
                pattern_type="broken_plural",
                examples=["دُوَل", "صُوَر", "غُرَف"]
            ),
            PatternTemplate(
                name="PLURAL_FICLAN",
                template="فِعْلَان",
                description="Broken plural - fiʿlān pattern",
                pattern_type="broken_plural",
                examples=["وِلْدَان", "غِلْمَان", "خِيلَان"]
            ),
            PatternTemplate(
                name="PLURAL_FAWAACIL",
                template="فَوَاعِل",
                description="Broken plural - fawāʿil pattern",
                pattern_type="broken_plural",
                examples=["فَوَاكِه", "جَوَامِع", "قَوَاعِد"]
            ),
            PatternTemplate(
                name="PLURAL_MAFAACIL",
                template="مَفَاعِل",
                description="Broken plural of instrument/place nouns",
                pattern_type="broken_plural",
                examples=["مَسَاجِد", "مَدَارِس", "مَطَابِخ"]
            ),
            PatternTemplate(
                name="PLURAL_FUCALAA2",
                template="فُعَّال",
                description="Broken plural - fuʿʿāl pattern",
                pattern_type="broken_plural",
                examples=["طُلَّاب", "حُكَّام", "كُتَّاب"]
            ),
            PatternTemplate(
                name="PLURAL_FUCUL",
                template="فُعُل",
                description="Broken plural - fuʿul pattern",
                pattern_type="broken_plural",
                examples=["كُتُب", "سُبُل", "رُسُل"]
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
            PatternTemplate(
                name="ADJECTIVE_FACOOL",
                template="فَعُول",
                description="Intensive adjective - faʿūl pattern",
                pattern_type="adjective",
                examples=["صَبُور", "شَكُور", "غَفُور"]
            ),
            PatternTemplate(
                name="ADJECTIVE_FACCAAL",
                template="فَعَّال",
                description="Intensive adjective - faʿʿāl pattern",
                pattern_type="adjective",
                examples=["عَلَّام", "صَبَّار", "تَوَّاب"]
            ),
            PatternTemplate(
                name="ADJECTIVE_FACLAN",
                template="فَعْلَان",
                description="Adjective denoting state",
                pattern_type="adjective",
                examples=["عَطْشَان", "جَوْعَان", "غَضْبَان"]
            ),
            PatternTemplate(
                name="ADJECTIVE_FACIL",
                template="فَاعِل",
                description="Adjective from active participle",
                pattern_type="adjective",
                examples=["عَالِم", "كَامِل", "صَالِح"]
            ),
            PatternTemplate(
                name="ADJECTIVE_MAFCOOL",
                template="مَفْعُول",
                description="Adjective from passive participle",
                pattern_type="adjective",
                examples=["مَعْرُوف", "مَحْمُود", "مَقْبُول"]
            ),
        ]


def create_default_catalog() -> PatternCatalog:
    """Factory function that creates and returns the default PatternCatalog."""
    return PatternCatalog()
