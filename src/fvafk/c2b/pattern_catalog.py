"""
Comprehensive Arabic morphological pattern catalog
"""
from enum import Enum
from typing import Dict, List

from .pattern_matcher import PatternTemplate


class PatternUniverse(Enum):
    """All Arabic morphological patterns"""
    # Verb patterns (Forms I-X)
    FORM_I = "فَعَلَ"
    FORM_II = "فَعَّلَ"
    FORM_III = "فَاعَلَ"
    FORM_IV = "أَفْعَلَ"
    FORM_V = "تَفَعَّلَ"
    FORM_VI = "تَفَاعَلَ"
    FORM_VII = "اِنْفَعَلَ"
    FORM_VIII = "اِفْتَعَلَ"
    FORM_IX = "اِفْعَلَّ"
    FORM_X = "اِسْتَفْعَلَ"
    
    # Noun patterns
    MASDAR_FORM_I = "فِعَال"
    ACTIVE_PARTICIPLE = "فَاعِل"
    PASSIVE_PARTICIPLE = "مَفْعُول"
    INSTRUMENT = "مِفْعَال"
    PLACE_TIME = "مَفْعَل"
    
    # Broken plurals
    AFAAL = "أَفْعَال"
    FUOOL = "فُعُول"
    FIAAL = "فِعَال"
    AFILA = "أَفْعِلَة"
    FUALA = "فُعَلَاء"
    MAFAAIL = "مَفَاعِيل"
    FAWAIL = "فَوَاعِل"
    
    # Diminutive
    FUAYL = "فُعَيْل"
    FUAYLA = "فُعَيْلَة"
    
    # Adjectives
    FAEEL = "فَعِيل"
    FAAL = "فَعَّال"
    MIFAAL = "مِفْعَال"
    AFAL = "أَفْعَل"


class PatternCatalog:
    """Organized catalog of morphological patterns"""
    
    @classmethod
    def load_full_catalog(cls) -> Dict[str, List[PatternTemplate]]:
        """Load all patterns from awzan + built-in
        
        Returns:
            Dictionary mapping pattern categories to lists of PatternTemplate objects
        """
        catalog = {
            "verb_forms": cls._load_verb_patterns(),
            "noun_patterns": cls._load_noun_patterns(),
            "broken_plurals": cls._load_plural_patterns(),
            "adjectives": cls._load_adjective_patterns(),
        }
        return catalog
    
    @classmethod
    def _load_verb_patterns(cls) -> List[PatternTemplate]:
        """Load verb form patterns (Forms I-X)"""
        patterns = [
            PatternTemplate(
                pattern=PatternUniverse.FORM_I.value,
                pattern_type="FORM_I",
                description="Basic trilateral verb",
                form="I",
                examples=["كَتَبَ", "ذَهَبَ", "قَرَأَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_II.value,
                pattern_type="FORM_II",
                description="Intensive/causative verb",
                form="II",
                examples=["عَلَّمَ", "كَسَّرَ", "فَهَّمَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_III.value,
                pattern_type="FORM_III",
                description="Conative verb (attempt)",
                form="III",
                examples=["قَاتَلَ", "سَافَرَ", "كَاتَبَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_IV.value,
                pattern_type="FORM_IV",
                description="Causative verb",
                form="IV",
                examples=["أَكْرَمَ", "أَرْسَلَ", "أَخْرَجَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_V.value,
                pattern_type="FORM_V",
                description="Reflexive of Form II",
                form="V",
                examples=["تَعَلَّمَ", "تَكَلَّمَ", "تَفَهَّمَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_VI.value,
                pattern_type="FORM_VI",
                description="Reciprocal verb",
                form="VI",
                examples=["تَقَاتَلَ", "تَبَادَلَ", "تَكَاتَبَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_VII.value,
                pattern_type="FORM_VII",
                description="Passive/reflexive verb",
                form="VII",
                examples=["اِنْكَسَرَ", "اِنْفَتَحَ", "اِنْقَطَعَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_VIII.value,
                pattern_type="FORM_VIII",
                description="Reflexive verb with infixed ت",
                form="VIII",
                examples=["اِفْتَرَضَ", "اِجْتَمَعَ", "اِكْتَسَبَ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_IX.value,
                pattern_type="FORM_IX",
                description="Color/defect verb",
                form="IX",
                examples=["اِحْمَرَّ", "اِصْفَرَّ", "اِخْضَرَّ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FORM_X.value,
                pattern_type="FORM_X",
                description="Request/deem verb",
                form="X",
                examples=["اِسْتَخْرَجَ", "اِسْتَعْمَلَ", "اِسْتَفْهَمَ"]
            ),
        ]
        return patterns
    
    @classmethod
    def _load_noun_patterns(cls) -> List[PatternTemplate]:
        """Load noun patterns (masdar, participles, etc.)"""
        patterns = [
            PatternTemplate(
                pattern=PatternUniverse.MASDAR_FORM_I.value,
                pattern_type="MASDAR_FORM_I",
                description="Verbal noun Form I",
                examples=["كِتَاب", "قِرَاءَة", "ذَهَاب"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.ACTIVE_PARTICIPLE.value,
                pattern_type="ACTIVE_PARTICIPLE",
                description="Active participle",
                examples=["كَاتِب", "ذَاهِب", "قَارِئ"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.PASSIVE_PARTICIPLE.value,
                pattern_type="PASSIVE_PARTICIPLE",
                description="Passive participle",
                examples=["مَكْتُوب", "مَقْرُوء", "مَفْعُول"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.INSTRUMENT.value,
                pattern_type="INSTRUMENT",
                description="Instrument noun",
                examples=["مِفْتَاح", "مِنْشَار", "مِقْيَاس"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.PLACE_TIME.value,
                pattern_type="PLACE_TIME",
                description="Place/time noun",
                examples=["مَكْتَب", "مَدْرَسَة", "مَطْبَخ"]
            ),
        ]
        return patterns
    
    @classmethod
    def _load_plural_patterns(cls) -> List[PatternTemplate]:
        """Load broken plural patterns"""
        patterns = [
            PatternTemplate(
                pattern=PatternUniverse.AFAAL.value,
                pattern_type="AFAAL",
                description="Broken plural pattern أَفْعَال",
                examples=["أَقْلَام", "أَبْوَاب", "أَفْكَار"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FUOOL.value,
                pattern_type="FUOOL",
                description="Broken plural pattern فُعُول",
                examples=["كُتُب", "بُيُوت", "قُلُوب"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FIAAL.value,
                pattern_type="FIAAL",
                description="Broken plural pattern فِعَال",
                examples=["كِلَاب", "رِجَال", "جِبَال"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.AFILA.value,
                pattern_type="AFILA",
                description="Broken plural pattern أَفْعِلَة",
                examples=["أَسْئِلَة", "أَطْعِمَة", "أَحْذِيَة"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FUALA.value,
                pattern_type="FUALA",
                description="Broken plural pattern فُعَلَاء",
                examples=["عُلَمَاء", "فُقَرَاء", "شُعَرَاء"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.MAFAAIL.value,
                pattern_type="MAFAAIL",
                description="Broken plural pattern مَفَاعِيل",
                examples=["مَفَاتِيح", "مَصَابِيح", "مَنَادِيل"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FAWAIL.value,
                pattern_type="FAWAIL",
                description="Broken plural pattern فَوَاعِل",
                examples=["كَوَاكِب", "نَوَافِذ", "رَوَائِح"]
            ),
        ]
        return patterns
    
    @classmethod
    def _load_adjective_patterns(cls) -> List[PatternTemplate]:
        """Load adjective patterns"""
        patterns = [
            PatternTemplate(
                pattern=PatternUniverse.FAEEL.value,
                pattern_type="FAEEL",
                description="Intensive adjective فَعِيل",
                examples=["كَبِير", "صَغِير", "جَمِيل"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.FAAL.value,
                pattern_type="FAAL",
                description="Intensive adjective فَعَّال",
                examples=["كَذَّاب", "نَجَّار", "حَدَّاد"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.MIFAAL.value,
                pattern_type="MIFAAL",
                description="Intensive adjective مِفْعَال",
                examples=["مِهْذَار", "مِعْطَار", "مِضْيَاف"]
            ),
            PatternTemplate(
                pattern=PatternUniverse.AFAL.value,
                pattern_type="AFAL",
                description="Comparative/superlative أَفْعَل",
                examples=["أَكْبَر", "أَصْغَر", "أَجْمَل"]
            ),
        ]
        return patterns
    
    @classmethod
    def get_pattern_by_type(cls, pattern_type: str) -> PatternTemplate:
        """Get a specific pattern by its type
        
        Args:
            pattern_type: The pattern type identifier (e.g., "FORM_I", "AFAAL")
            
        Returns:
            PatternTemplate matching the type, or None if not found
        """
        catalog = cls.load_full_catalog()
        for category_patterns in catalog.values():
            for pattern in category_patterns:
                if pattern.pattern_type == pattern_type:
                    return pattern
        return None
    
    @classmethod
    def get_all_patterns(cls) -> List[PatternTemplate]:
        """Get all patterns as a flat list
        
        Returns:
            List of all PatternTemplate objects
        """
        catalog = cls.load_full_catalog()
        all_patterns = []
        for category_patterns in catalog.values():
            all_patterns.extend(category_patterns)
        return all_patterns