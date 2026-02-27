"""
Syntactic Parser: Combines all linkers into a unified syntactic graph.

Author: Hussein Hiyassat
Date: 2025-02-27
Version: 1.0
"""

from dataclasses import dataclass, field
from typing import List
import sys
sys.path.insert(0, 'src')

from fvafk.c2b.word_form import WordForm
from .linkers.isnadi_linker import IsnadiLinker
from .linkers.tadmini_linker import TadminiLinker, TadminiLink
from .linkers.taqyidi_linker import TaqyidiLinker, TaqyidiLink
from .linkers.link import Link, LinkType


@dataclass
class SyntacticGraph:
    """
    Unified syntactic representation of a sentence.

    Attributes:
        tokens: Word forms in the sentence
        isnadi_links: Subject-predicate links (IsnadiLink as generic Link)
        tadmini_links: Transitive/subordination links
        taqyidi_links: Restriction/adjunct links
    """
    tokens: List[WordForm] = field(default_factory=list)
    isnadi_links: List[Link] = field(default_factory=list)
    tadmini_links: List[TadminiLink] = field(default_factory=list)
    taqyidi_links: List[TaqyidiLink] = field(default_factory=list)

    @property
    def all_links(self) -> List[Link]:
        """Return all links as generic Link objects."""
        links = list(self.isnadi_links)
        n = len(self.tokens)
        # Build generic links from tadmini/taqyidi
        for tl in self.tadmini_links:
            head = self.tokens[tl.head_idx] if tl.head_idx < n else None
            dep = self.tokens[tl.dep_idx] if tl.dep_idx < n else None
            links.append(Link(
                link_type=LinkType.TADMINI,
                head_id=head.word_id if head and head.word_id is not None else tl.head_idx,
                dependent_id=dep.word_id if dep and dep.word_id is not None else tl.dep_idx,
                confidence=tl.confidence,
                reason=f"TADMINI:{tl.link_type}",
            ))
        for tq in self.taqyidi_links:
            head = self.tokens[tq.head_idx] if tq.head_idx < n else None
            dep = self.tokens[tq.dep_idx] if tq.dep_idx < n else None
            links.append(Link(
                link_type=LinkType.TAQYIDI,
                head_id=head.word_id if head and head.word_id is not None else tq.head_idx,
                dependent_id=dep.word_id if dep and dep.word_id is not None else tq.dep_idx,
                confidence=tq.confidence,
                reason=f"TAQYIDI:{tq.link_type}",
            ))
        return links


class SyntacticParser:
    """
    Runs all three linkers (Isnadi, Tadmini, Taqyidi) and returns a
    SyntacticGraph for the given word forms.
    """

    def __init__(self):
        self._isnadi = IsnadiLinker()
        self._tadmini = TadminiLinker()
        self._taqyidi = TaqyidiLinker()

    def parse(self, word_forms: List[WordForm]) -> SyntacticGraph:
        """
        Parse a list of word forms and return a SyntacticGraph.

        Args:
            word_forms: List of WordForm instances

        Returns:
            SyntacticGraph with all detected links
        """
        isnadi_links = self._isnadi.find_links(word_forms)
        tadmini_links = self._tadmini.link(word_forms)
        taqyidi_links = self._taqyidi.link(word_forms)

        return SyntacticGraph(
            tokens=list(word_forms),
            isnadi_links=isnadi_links,
            tadmini_links=tadmini_links,
            taqyidi_links=taqyidi_links,
        )
