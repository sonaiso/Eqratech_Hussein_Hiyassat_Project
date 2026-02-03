"""
PatternMatcher: Recognize Arabic morphological patterns.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set

from .morpheme import Pattern, PatternType, Root


@dataclass(frozen=True)
class PatternTemplate:
    template: str
    pattern_type: PatternType
    category: str
    form: Optional[str] = None
    meaning: Optional[str] = None

    def matches_root_type(self, root: Root) -> bool:
        count = sum(1 for c in self.template if c in {'ف', 'ع', 'ل'})
        if len(root.letters) >= count:
            return True
        return False


class PatternDatabase:
    def __init__(self) -> None:
        self.patterns: List[PatternTemplate] = []
        self._initialize_patterns()

    def _initialize_patterns(self) -> None:
        self.patterns.extend([
            PatternTemplate(template="فَعَلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعَلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعِلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعُلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعَّلَ", pattern_type=PatternType.FORM_II, category="verb", form="II"),
            PatternTemplate(template="فَاعَلَ", pattern_type=PatternType.FORM_III, category="verb", form="III"),
            PatternTemplate(template="أَفْعَلَ", pattern_type=PatternType.FORM_IV, category="verb", form="IV"),
            PatternTemplate(template="تَفَعَّلَ", pattern_type=PatternType.FORM_V, category="verb", form="V"),
            PatternTemplate(template="تَفَاعَلَ", pattern_type=PatternType.FORM_VI, category="verb", form="VI"),
            PatternTemplate(template="انْفَعَلَ", pattern_type=PatternType.FORM_VII, category="verb", form="VII"),
            PatternTemplate(template="افْتَعَلَ", pattern_type=PatternType.FORM_VIII, category="verb", form="VIII"),
            PatternTemplate(template="اسْتَفْعَلَ", pattern_type=PatternType.FORM_X, category="verb", form="X"),
            PatternTemplate(template="فَاعِل", pattern_type=PatternType.ACTIVE_PARTICIPLE, category="noun"),
            PatternTemplate(template="مَفْعُول", pattern_type=PatternType.PASSIVE_PARTICIPLE, category="noun"),
            PatternTemplate(template="مَفْعَل", pattern_type=PatternType.PLACE_TIME_NOUN, category="noun"),
            PatternTemplate(template="فِعَال", pattern_type=PatternType.VERBAL_NOUN, category="noun"),
            PatternTemplate(template="فَعِيل", pattern_type=PatternType.INTENSIVE, category="noun"),
            PatternTemplate(template="أَفْعَل", pattern_type=PatternType.ELATIVE, category="noun"),
            PatternTemplate(template="فَاعِلُون", pattern_type=PatternType.SOUND_MASCULINE_PLURAL, category="plural"),
            PatternTemplate(template="فَاعِلِين", pattern_type=PatternType.SOUND_MASCULINE_PLURAL, category="plural"),
            PatternTemplate(template="فَاعِلَات", pattern_type=PatternType.SOUND_FEMININE_PLURAL, category="plural"),
            PatternTemplate(template="فُعُول", pattern_type=PatternType.BROKEN_PLURAL_FUUL, category="plural"),
            PatternTemplate(template="فِعَال", pattern_type=PatternType.BROKEN_PLURAL_FIAAL, category="plural"),
            PatternTemplate(template="أَفْعَال", pattern_type=PatternType.BROKEN_PLURAL_AFAAL, category="plural"),
            PatternTemplate(template="فِعَل", pattern_type=PatternType.BROKEN_PLURAL_FIUL, category="plural"),
        ])

    def get_all(self) -> List[PatternTemplate]:
        return self.patterns

    def get_by_category(self, category: str) -> List[PatternTemplate]:
        return [p for p in self.patterns if p.category == category]


class PatternMatcher:
    """
    Matches Arabic words against morphological patterns.
    
    Recognizes verb forms (I-X), active/passive participles, noun patterns,
    and broken plurals by comparing normalized words against pattern templates.
    
    Example:
        >>> matcher = PatternMatcher()
        >>> root = Root(letters=('ك', 'ت', 'ب'), root_type=RootType.TRILATERAL)
        >>> pattern = matcher.match("كَاتِب", root)
        >>> print(pattern.name)
        ACTIVE_PARTICIPLE
    """
    def __init__(self, database: Optional[PatternDatabase] = None) -> None:
        """
        Initialize pattern matcher.
        
        Args:
            database: Optional PatternDatabase with pattern templates
        """
        self.database = database or PatternDatabase()

    def match(self, word: str, root: Root) -> Optional[Pattern]:
        """
        Match word to morphological pattern.
        
        Args:
            word: Arabic word (normalized)
            root: Extracted root
        
        Returns:
            Pattern object if match found, None otherwise
        """
        if not word or not root:
            return None
        normalized = self._normalize(word)
        categories = ["verb", "noun", "plural"]
        checked = set()
        for category in categories:
            for template in self.database.get_by_category(category):
                if id(template) in checked:
                    continue
                checked.add(id(template))
                if not template.matches_root_type(root):
                    continue
                candidate = self._instantiate_template(template.template, root)
                if self._matches(normalized, candidate, template.pattern_type):
                    return Pattern(
                        name=template.pattern_type.value,
                        template=template.template,
                        pattern_type=template.pattern_type,
                        stem=word
                    )
        for template in self.database.get_all():
            if id(template) in checked:
                continue
            if not template.matches_root_type(root):
                continue
            candidate = self._instantiate_template(template.template, root)
            if self._matches(normalized, candidate, template.pattern_type):
                return Pattern(
                    name=template.pattern_type.value,
                    template=template.template,
                    pattern_type=template.pattern_type,
                    stem=word
                )
        return None

    def _normalize(self, word: str) -> str:
        text = word.replace('ً', '').replace('ٌ', '').replace('ٍ', '')
        text = text.replace('أ', 'ا').replace('إ', 'ا').replace('آ', 'ا')
        text = text.replace('ى', 'ي')
        return text.strip()

    def _instantiate_template(self, template_str: str, root: Root) -> str:
        chars = []
        l_count = 0
        for ch in template_str:
            if ch == 'ف':
                chars.append(root.letters[0])
            elif ch == 'ع':
                chars.append(root.letters[1])
            elif ch == 'ل':
                if l_count == 0:
                    idx = 2
                else:
                    idx = min(3, len(root.letters) - 1)
                chars.append(root.letters[idx])
                l_count += 1
            else:
                chars.append(ch)
        return ''.join(chars)

    def _matches(self, word: str, candidate: str, pattern_type: PatternType) -> bool:
        if word == candidate:
            return True
        stripped_word = self._strip_diacritics(word)
        stripped_candidate = self._strip_diacritics(candidate)
        if pattern_type == PatternType.BROKEN_PLURAL_FUUL:
            candidate_no_waw = candidate.replace("و", "")
            stripped_candidate_no_waw = self._strip_diacritics(candidate_no_waw)
            if stripped_word == stripped_candidate_no_waw:
                return True
        if stripped_word != stripped_candidate:
            return False
        if len(word) == len(candidate):
            return True
        if pattern_type == PatternType.FORM_X:
            return True
        return False

    def _strip_diacritics(self, text: str) -> str:
        diacritics = "َُِْٰٓٔٱ" + "ًٌٍ"
        for d in diacritics:
            text = text.replace(d, '')
        text = re.sub(r'[\u064B-\u0650\u0652-\u065F\u0670]', '', text)
        return text
