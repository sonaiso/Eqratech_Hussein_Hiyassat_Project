"""
Pattern Catalog - Arabic Morphological Patterns
Comprehensive collection of verb forms, noun patterns, and broken plurals
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any
from enum import Enum

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


class PatternCatalog:
    """Catalog of Arabic morphological patterns."""

    def __init__(self) -> None:
        self._pattern_info_cache: List[PatternInfo] = _build_pattern_info_cache()
        self._matcher = PatternMatcher()

    # ------------------------------------------------------------------
    # Query methods
    # ------------------------------------------------------------------

    def get_by_category(self, category: PatternCategory) -> List[PatternInfo]:
        """Return all PatternInfo entries for the given category."""
        return [p for p in self._pattern_info_cache if p.category == category]

    def get_participle_patterns(self) -> List[PatternInfo]:
        """Return participle patterns (active and passive)."""
        return self.get_by_category(PatternCategory.PARTICIPLE)

    def get_verb_forms(self) -> List[PatternInfo]:
        """Return all verb patterns."""
        return self.get_by_category(PatternCategory.VERB)

    def search_patterns(
        self,
        category: Optional[PatternCategory] = None,
        form: Optional[str] = None,
        min_frequency_rank: Optional[int] = None,
    ) -> List[PatternInfo]:
        """Filter patterns by optional criteria."""
        results = self._pattern_info_cache
        if category is not None:
            results = [p for p in results if p.category == category]
        if form is not None:
            results = [p for p in results if p.form == form]
        if min_frequency_rank is not None:
            results = [
                p for p in results
                if p.frequency_rank is None or p.frequency_rank <= min_frequency_rank
            ]
        return results

    def get_most_common(self, limit: int = 20) -> List[PatternInfo]:
        """Return the most common patterns sorted by frequency_rank."""
        ranked = [p for p in self._pattern_info_cache if p.frequency_rank is not None]
        ranked.sort(key=lambda p: p.frequency_rank or 0)
        return ranked[:limit]

    def get_pattern_by_template(self, template: str) -> Optional[PatternInfo]:
        """Return the PatternInfo matching the given template string."""
        for p in self._pattern_info_cache:
            if p.template == template:
                return p
        return None

    def match_pattern(self, word: str, root: Root) -> Optional[PatternMatch]:
        """Match a word+root against the catalog and return the best PatternMatch."""
        if not word:
            return None
        pattern = self._matcher.match_best(word, root)
        if pattern is None:
            return None
        confidence = float(pattern.features.get("confidence", "0.8"))
        info = self.get_pattern_by_template(pattern.template)
        if info is None:
            info = PatternInfo(
                template=pattern.template,
                pattern_type=pattern.pattern_type,
                category=_category_from_template(
                    type("_T", (), {
                        "pattern_type": pattern.pattern_type,
                        "category": pattern.features.get("category", "noun"),
                    })()
                ),
                form=pattern.features.get("form"),
                meaning=pattern.features.get("meaning"),
            )
        return PatternMatch(confidence=confidence, pattern_info=info)

    def get_statistics(self) -> Dict[str, int]:
        """Return basic statistics about the catalog."""
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
    def load_full_catalog(cls) -> Dict[str, List]:
        """Load complete pattern catalog (legacy API)."""
        instance = cls()
        return {
            "verb_forms": instance.get_by_category(PatternCategory.VERB),
            "noun_patterns": instance.get_by_category(PatternCategory.NOUN),
            "broken_plurals": instance.get_by_category(PatternCategory.PLURAL),
            "participles": instance.get_by_category(PatternCategory.PARTICIPLE),
        }


def create_default_catalog() -> PatternCatalog:
    """Factory function returning a default PatternCatalog instance."""
    return PatternCatalog()
