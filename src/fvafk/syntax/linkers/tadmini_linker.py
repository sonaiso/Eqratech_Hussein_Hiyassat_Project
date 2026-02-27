"""
TADMINI Linker: Detects transitive/subordination relations

This module implements the TadminiLinker which identifies:
- MAFOOL_BIH: verb-object relations (فعل + مفعول به)
- IDAFA: genitive/possessive relations (مضاف + مضاف إليه)
- SIFA: adjective-noun agreement (موصوف + صفة)

Author: Hussein Hiyassat
Date: 2025-02-27
Version: 1.0
"""

from dataclasses import dataclass
from typing import List, Optional
import sys
sys.path.insert(0, 'src')

from fvafk.c2b.word_form import (
    WordForm, PartOfSpeech, Case, Number, Gender
)
from .link import Link, LinkType


@dataclass
class TadminiLink:
    """Represents a TADMINI (transitive/subordination) link"""
    head_idx: int
    dep_idx: int
    link_type: str  # MAFOOL_BIH, IDAFA, SIFA
    confidence: float = 1.0

    def __post_init__(self):
        if not 0.0 <= self.confidence <= 1.0:
            raise ValueError(f"Confidence must be between 0.0 and 1.0, got {self.confidence}")
        if self.head_idx == self.dep_idx:
            raise ValueError("Head and dependent cannot be the same word")


class TadminiLinker:
    """
    Identifies TADMINI (تضميني) relations:
    - MAFOOL_BIH: verb → accusative noun
    - IDAFA: definite/construct noun → genitive noun
    - SIFA: noun → agreeing adjective
    """

    def link(self, word_forms: List[WordForm]) -> List[TadminiLink]:
        """
        Find all TADMINI links in the given word forms.

        Args:
            word_forms: List of WordForm instances representing a sentence

        Returns:
            List of TadminiLink instances
        """
        links: List[TadminiLink] = []
        used_dep: set = set()

        # Pass 1: MAFOOL_BIH — verb → next accusative noun
        for i, word in enumerate(word_forms):
            if not word.is_verb:
                continue
            for j in range(i + 1, min(i + 4, len(word_forms))):
                candidate = word_forms[j]
                if j in used_dep:
                    continue
                if candidate.is_noun and candidate.case == Case.ACCUSATIVE:
                    links.append(TadminiLink(
                        head_idx=i,
                        dep_idx=j,
                        link_type="MAFOOL_BIH",
                        confidence=0.85,
                    ))
                    used_dep.add(j)
                    break

        # Pass 2: IDAFA — noun → next genitive noun
        for i, word in enumerate(word_forms):
            if not word.is_noun:
                continue
            for j in range(i + 1, min(i + 3, len(word_forms))):
                candidate = word_forms[j]
                if j in used_dep:
                    continue
                if candidate.is_noun and candidate.case == Case.GENITIVE:
                    links.append(TadminiLink(
                        head_idx=i,
                        dep_idx=j,
                        link_type="IDAFA",
                        confidence=0.80,
                    ))
                    used_dep.add(j)
                    break

        # Pass 3: SIFA — noun → following adjective agreeing in number/gender
        for i, word in enumerate(word_forms):
            if not word.is_noun:
                continue
            for j in range(i + 1, min(i + 3, len(word_forms))):
                candidate = word_forms[j]
                if j in used_dep:
                    continue
                if (candidate.pos == PartOfSpeech.ADJECTIVE and
                        word.agrees_with(candidate, ['number', 'gender'])):
                    links.append(TadminiLink(
                        head_idx=i,
                        dep_idx=j,
                        link_type="SIFA",
                        confidence=0.80,
                    ))
                    used_dep.add(j)
                    break

        return links

    def to_links(self, word_forms: List[WordForm]) -> List[Link]:
        """Convert TadminiLinks to generic Link objects."""
        result = []
        for tl in self.link(word_forms):
            head = word_forms[tl.head_idx]
            dep = word_forms[tl.dep_idx]
            result.append(Link(
                link_type=LinkType.TADMINI,
                head_id=head.word_id if head.word_id is not None else tl.head_idx,
                dependent_id=dep.word_id if dep.word_id is not None else tl.dep_idx,
                confidence=tl.confidence,
                reason=f"TADMINI:{tl.link_type}",
            ))
        return result
