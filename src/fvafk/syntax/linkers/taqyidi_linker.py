"""
TAQYIDI Linker: Detects restriction/adjunct relations

This module implements the TaqyidiLinker which identifies:
- HAAL: circumstantial accusative (حال)
- TAMYEEZ: specifier accusative (تمييز)
- JAR_MAJROOR: prepositional phrase (جار ومجرور)
- SHART: conditional clause (شرط)

Author: Hussein Hiyassat
Date: 2025-02-27
Version: 1.0
"""

from dataclasses import dataclass
from typing import List, Set
import sys
sys.path.insert(0, 'src')

from fvafk.c2b.word_form import (
    WordForm, PartOfSpeech, Case, Number
)
from .link import Link, LinkType


# Arabic prepositions that govern genitive case
_JAR_PARTICLES: Set[str] = {
    "في", "من", "إلى", "على", "عن", "ب", "بـ", "ل", "لـ", "ك", "كـ",
    "مع", "حتى", "منذ", "خلال", "بين", "فوق", "تحت", "أمام", "وراء",
}

# Conditional particles
_SHART_PARTICLES: Set[str] = {
    "إن", "إذا", "لو", "لولا", "متى", "أينما", "كلما", "مهما", "من",
    "ما", "أيّ",
}

# Number-like words (cardinal numbers in Arabic)
_NUMBER_WORDS: Set[str] = {
    "واحد", "اثنان", "ثلاثة", "أربعة", "خمسة", "ستة", "سبعة", "ثمانية",
    "تسعة", "عشرة", "عشرون", "مئة", "مئتان", "ألف", "مليون",
}


def _bare_surface(wf: WordForm) -> str:
    """Return surface form stripped of diacritics for particle matching."""
    import unicodedata
    text = unicodedata.normalize("NFC", wf.surface)
    return "".join(
        ch for ch in text if unicodedata.combining(ch) == 0
    ).replace("ـ", "").strip()


@dataclass
class TaqyidiLink:
    """Represents a TAQYIDI (restriction/adjunct) link"""
    head_idx: int
    dep_idx: int
    link_type: str  # HAAL, TAMYEEZ, JAR_MAJROOR, SHART
    confidence: float = 1.0

    def __post_init__(self):
        if not 0.0 <= self.confidence <= 1.0:
            raise ValueError(f"Confidence must be between 0.0 and 1.0, got {self.confidence}")
        if self.head_idx == self.dep_idx:
            raise ValueError("Head and dependent cannot be the same word")


class TaqyidiLinker:
    """
    Identifies TAQYIDI (تقييدي) relations:
    - HAAL: verb/noun → following accusative noun (circumstantial)
    - TAMYEEZ: number-word → following accusative singular
    - JAR_MAJROOR: preposition → following noun
    - SHART: conditional particle → clause head
    """

    def link(self, word_forms: List[WordForm]) -> List[TaqyidiLink]:
        """
        Find all TAQYIDI links in the given word forms.

        Args:
            word_forms: List of WordForm instances representing a sentence

        Returns:
            List of TaqyidiLink instances
        """
        links: List[TaqyidiLink] = []
        used_dep: set = set()

        for i, word in enumerate(word_forms):
            bare = _bare_surface(word)

            # JAR_MAJROOR: preposition particle → following noun
            if word.is_particle and bare in _JAR_PARTICLES:
                for j in range(i + 1, min(i + 3, len(word_forms))):
                    if j in used_dep:
                        continue
                    candidate = word_forms[j]
                    if candidate.is_noun:
                        links.append(TaqyidiLink(
                            head_idx=i,
                            dep_idx=j,
                            link_type="JAR_MAJROOR",
                            confidence=0.90,
                        ))
                        used_dep.add(j)
                        break

            # SHART: conditional particle → clause head (next verb or noun)
            elif word.is_particle and bare in _SHART_PARTICLES:
                for j in range(i + 1, min(i + 4, len(word_forms))):
                    if j in used_dep:
                        continue
                    candidate = word_forms[j]
                    if candidate.is_verb or candidate.is_noun:
                        links.append(TaqyidiLink(
                            head_idx=i,
                            dep_idx=j,
                            link_type="SHART",
                            confidence=0.75,
                        ))
                        used_dep.add(j)
                        break

            # TAMYEEZ: number-word → following accusative singular
            elif bare in _NUMBER_WORDS:
                for j in range(i + 1, min(i + 3, len(word_forms))):
                    if j in used_dep:
                        continue
                    candidate = word_forms[j]
                    if (candidate.is_noun and
                            candidate.case == Case.ACCUSATIVE and
                            candidate.number == Number.SINGULAR):
                        links.append(TaqyidiLink(
                            head_idx=i,
                            dep_idx=j,
                            link_type="TAMYEEZ",
                            confidence=0.80,
                        ))
                        used_dep.add(j)
                        break

            # HAAL: verb or noun → following accusative noun (not already linked)
            elif (word.is_verb or word.is_noun):
                for j in range(i + 1, min(i + 4, len(word_forms))):
                    if j in used_dep:
                        continue
                    candidate = word_forms[j]
                    # Haal: accusative noun that is NOT in a JAR_MAJROOR chain
                    if (candidate.is_noun and
                            candidate.case == Case.ACCUSATIVE and
                            _bare_surface(candidate) not in _JAR_PARTICLES):
                        links.append(TaqyidiLink(
                            head_idx=i,
                            dep_idx=j,
                            link_type="HAAL",
                            confidence=0.60,
                        ))
                        used_dep.add(j)
                        break

        return links

    def to_links(self, word_forms: List[WordForm]) -> List[Link]:
        """Convert TaqyidiLinks to generic Link objects."""
        result = []
        for tl in self.link(word_forms):
            head = word_forms[tl.head_idx]
            dep = word_forms[tl.dep_idx]
            result.append(Link(
                link_type=LinkType.TAQYIDI,
                head_id=head.word_id if head.word_id is not None else tl.head_idx,
                dependent_id=dep.word_id if dep.word_id is not None else tl.dep_idx,
                confidence=tl.confidence,
                reason=f"TAQYIDI:{tl.link_type}",
            ))
        return result
