"""
Pattern Catalog - Arabic Morphological Patterns
Comprehensive collection of verb forms, noun patterns, and broken plurals
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional

from .morpheme import PatternType, Root
from .pattern_matcher import PatternDatabase, PatternMatcher, PatternTemplate


class PatternCategory(Enum):
    """High-level category of a morphological pattern."""
    VERB = "verb"
    NOUN = "noun"
    PLURAL = "plural"
    PARTICIPLE = "participle"
    OTHER = "other"


# Mapping from PatternMatcher category strings to PatternCategory
_CATEGORY_MAP: Dict[str, PatternCategory] = {
    "verb": PatternCategory.VERB,
    "noun": PatternCategory.NOUN,
    "plural": PatternCategory.PLURAL,
}

# Participle pattern types
_PARTICIPLE_TYPES = {
    PatternType.ACTIVE_PARTICIPLE,
    PatternType.PASSIVE_PARTICIPLE,
}


@dataclass
class PatternInfo:
    """Rich description of a single Arabic morphological pattern."""
    template: str
    pattern_type: PatternType
    category: PatternCategory
    form: Optional[str] = None
    meaning: Optional[str] = None
    frequency_rank: Optional[int] = None

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
    pattern_info: PatternInfo
    confidence: float
    word: str = ""


def _template_to_info(tpl: PatternTemplate, rank: Optional[int] = None) -> PatternInfo:
    """Convert a PatternTemplate to a PatternInfo."""
    if tpl.pattern_type in _PARTICIPLE_TYPES:
        category = PatternCategory.PARTICIPLE
    else:
        category = _CATEGORY_MAP.get(tpl.category, PatternCategory.OTHER)
    return PatternInfo(
        template=tpl.template,
        pattern_type=tpl.pattern_type,
        category=category,
        form=tpl.form,
        meaning=tpl.meaning,
        frequency_rank=rank,
    )


class PatternCatalog:
    """Catalog of Arabic morphological patterns with rich query API."""

    def __init__(self) -> None:
        self._database = PatternDatabase()
        self._matcher = PatternMatcher(self._database)
        # Build the info cache, deduplicating by template
        seen: Dict[str, PatternInfo] = {}
        rank = 1
        for tpl in self._database.get_all():
            if tpl.template not in seen:
                info = _template_to_info(tpl, rank)
                seen[tpl.template] = info
                rank += 1
        self._pattern_info_cache: Dict[str, PatternInfo] = seen

    # ------------------------------------------------------------------
    # Category filtering
    # ------------------------------------------------------------------

    def get_by_category(self, category: PatternCategory) -> List[PatternInfo]:
        return [i for i in self._pattern_info_cache.values() if i.category == category]

    def get_participle_patterns(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.PARTICIPLE)

    def get_verb_forms(self) -> List[PatternInfo]:
        return self.get_by_category(PatternCategory.VERB)

    # ------------------------------------------------------------------
    # Search
    # ------------------------------------------------------------------

    def search_patterns(
        self,
        category: Optional[PatternCategory] = None,
        form: Optional[str] = None,
        min_frequency_rank: Optional[int] = None,
    ) -> List[PatternInfo]:
        results = list(self._pattern_info_cache.values())
        if category is not None:
            results = [i for i in results if i.category == category]
        if form is not None:
            results = [i for i in results if i.form == form]
        if min_frequency_rank is not None:
            results = [
                i for i in results
                if i.frequency_rank is not None and i.frequency_rank <= min_frequency_rank
            ]
        return results

    def get_pattern_by_template(self, template: str) -> Optional[PatternInfo]:
        return self._pattern_info_cache.get(template)

    # ------------------------------------------------------------------
    # Frequency ranking
    # ------------------------------------------------------------------

    def get_most_common(self, limit: int = 20) -> List[PatternInfo]:
        ranked = [i for i in self._pattern_info_cache.values() if i.frequency_rank is not None]
        ranked.sort(key=lambda i: i.frequency_rank)  # type: ignore[arg-type]
        return ranked[:limit]

    # ------------------------------------------------------------------
    # Pattern matching
    # ------------------------------------------------------------------

    def match_pattern(self, word: str, root: Root) -> Optional[PatternMatch]:
        if not word:
            return None
        pattern = self._matcher.match(word, root)
        if pattern is None:
            return None
        info = self._pattern_info_cache.get(pattern.template)
        if info is None:
            # Create an info on-the-fly for patterns not in cache
            category = _CATEGORY_MAP.get(
                pattern.features.get("category", ""), PatternCategory.OTHER
            )
            if pattern.pattern_type in _PARTICIPLE_TYPES:
                category = PatternCategory.PARTICIPLE
            info = PatternInfo(
                template=pattern.template,
                pattern_type=pattern.pattern_type,
                category=category,
                form=pattern.features.get("form"),
                meaning=pattern.features.get("meaning"),
            )
        try:
            confidence = float(pattern.features.get("confidence", 1.0))
        except (TypeError, ValueError):
            confidence = 1.0
        return PatternMatch(pattern_info=info, confidence=confidence, word=word)

    # ------------------------------------------------------------------
    # Statistics
    # ------------------------------------------------------------------

    def get_statistics(self) -> Dict[str, int]:
        total = len(self._pattern_info_cache)
        return {
            "total_patterns": total,
            "category_verb": sum(
                1 for i in self._pattern_info_cache.values()
                if i.category == PatternCategory.VERB
            ),
            "category_noun": sum(
                1 for i in self._pattern_info_cache.values()
                if i.category == PatternCategory.NOUN
            ),
            "category_plural": sum(
                1 for i in self._pattern_info_cache.values()
                if i.category == PatternCategory.PLURAL
            ),
            "category_participle": sum(
                1 for i in self._pattern_info_cache.values()
                if i.category == PatternCategory.PARTICIPLE
            ),
        }

    # ------------------------------------------------------------------
    # Backward-compatible API
    # ------------------------------------------------------------------

    @classmethod
    def load_full_catalog(cls) -> Dict[str, List[Any]]:
        """Return a dict of pattern lists for backward compatibility.

        Keys: ``verb_forms``, ``noun_patterns``, ``plural_patterns``, ``participle_patterns``
        Each item has attributes: ``name``, ``template``, ``pattern``, ``pattern_type``,
        ``description``, ``examples``, ``form``, ``meaning``.
        """
        instance = cls()
        result: Dict[str, List[Any]] = {
            "verb_forms": [],
            "noun_patterns": [],
            "plural_patterns": [],
            "participle_patterns": [],
        }
        for info in instance._pattern_info_cache.values():
            entry = _LegacyEntry(
                name=info.pattern_type.name,
                template=info.template,
                pattern=info.template,
                pattern_type=info.pattern_type.name,
                description=info.meaning or info.pattern_type.value.replace("_", " "),
                examples=None,
                form=info.form,
                meaning=info.meaning,
            )
            if info.category == PatternCategory.VERB:
                result["verb_forms"].append(entry)
            elif info.category == PatternCategory.PARTICIPLE:
                result["participle_patterns"].append(entry)
            elif info.category == PatternCategory.PLURAL:
                result["plural_patterns"].append(entry)
            else:
                result["noun_patterns"].append(entry)
        return result


def create_default_catalog() -> PatternCatalog:
    """Factory function returning a default PatternCatalog instance."""
    return PatternCatalog()


@dataclass
class _LegacyEntry:
    """Backward-compatible pattern entry returned by :meth:`PatternCatalog.load_full_catalog`."""
    name: str
    template: str
    pattern: str
    pattern_type: str
    description: str
    examples: Optional[List[str]] = None
    form: Optional[str] = None
    meaning: Optional[str] = None
