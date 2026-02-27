"""
Tests for advanced syntax linkers: TadminiLinker, TaqyidiLinker,
SyntacticParser, and ConstraintValidator.

Author: Hussein Hiyassat
Date: 2025-02-27
"""

import pytest
import sys
sys.path.insert(0, 'src')

from fvafk.c2b.word_form import (
    WordForm, PartOfSpeech, Case, Number, Gender, Span
)
from fvafk.syntax.linkers.link import Link, LinkType
from fvafk.syntax.linkers.tadmini_linker import TadminiLinker, TadminiLink
from fvafk.syntax.linkers.taqyidi_linker import TaqyidiLinker, TaqyidiLink
from fvafk.syntax.syntactic_parser import SyntacticParser, SyntacticGraph
from fvafk.syntax.constraint_validator import ConstraintValidator, ConstraintViolation


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _noun(word_id, surface, case=Case.NOMINATIVE, number=Number.SINGULAR,
          gender=Gender.MASCULINE, definite=False):
    return WordForm(
        word_id=word_id,
        surface=surface,
        span=Span(word_id * 10, word_id * 10 + len(surface)),
        pos=PartOfSpeech.NOUN,
        case=case,
        number=number,
        gender=gender,
        definiteness=definite,
    )


def _verb(word_id, surface, number=Number.SINGULAR, gender=Gender.MASCULINE):
    return WordForm(
        word_id=word_id,
        surface=surface,
        span=Span(word_id * 10, word_id * 10 + len(surface)),
        pos=PartOfSpeech.VERB,
        case=Case.UNKNOWN,
        number=number,
        gender=gender,
    )


def _particle(word_id, surface):
    return WordForm(
        word_id=word_id,
        surface=surface,
        span=Span(word_id * 10, word_id * 10 + len(surface)),
        pos=PartOfSpeech.PARTICLE,
        case=Case.UNKNOWN,
    )


def _adjective(word_id, surface, case=Case.NOMINATIVE, number=Number.SINGULAR,
               gender=Gender.MASCULINE):
    return WordForm(
        word_id=word_id,
        surface=surface,
        span=Span(word_id * 10, word_id * 10 + len(surface)),
        pos=PartOfSpeech.ADJECTIVE,
        case=case,
        number=number,
        gender=gender,
    )


# ---------------------------------------------------------------------------
# Part 5.2: TadminiLinker
# ---------------------------------------------------------------------------

class TestTadminiLinker:

    def test_mafool_bih(self):
        """A verb followed by an accusative noun should produce MAFOOL_BIH."""
        words = [
            _verb(0, "كَتَبَ"),
            _noun(1, "الدَّرْسَ", case=Case.ACCUSATIVE),
        ]
        linker = TadminiLinker()
        links = linker.link(words)
        mafool = [l for l in links if l.link_type == "MAFOOL_BIH"]
        assert len(mafool) == 1
        assert mafool[0].head_idx == 0
        assert mafool[0].dep_idx == 1
        assert mafool[0].confidence > 0.0

    def test_idafa(self):
        """A noun followed by a genitive noun should produce IDAFA."""
        words = [
            _noun(0, "كِتَابُ", definite=True),
            _noun(1, "الطَّالِبِ", case=Case.GENITIVE, definite=True),
        ]
        linker = TadminiLinker()
        links = linker.link(words)
        idafa = [l for l in links if l.link_type == "IDAFA"]
        assert len(idafa) == 1
        assert idafa[0].head_idx == 0
        assert idafa[0].dep_idx == 1

    def test_sifa(self):
        """A noun followed by an adjective agreeing in gender/number should be SIFA."""
        words = [
            _noun(0, "الطَّالِبُ", definite=True),
            _adjective(1, "الْمُجْتَهِدُ"),
        ]
        linker = TadminiLinker()
        links = linker.link(words)
        sifa = [l for l in links if l.link_type == "SIFA"]
        assert len(sifa) == 1
        assert sifa[0].head_idx == 0
        assert sifa[0].dep_idx == 1

    def test_no_mafool_without_accusative(self):
        """Verb + nominative noun should NOT produce MAFOOL_BIH."""
        words = [
            _verb(0, "كَتَبَ"),
            _noun(1, "الطَّالِبُ", case=Case.NOMINATIVE),
        ]
        linker = TadminiLinker()
        links = linker.link(words)
        mafool = [l for l in links if l.link_type == "MAFOOL_BIH"]
        assert len(mafool) == 0

    def test_tadmini_link_dataclass_valid(self):
        """TadminiLink dataclass should raise on invalid confidence."""
        with pytest.raises(ValueError):
            TadminiLink(head_idx=0, dep_idx=1, link_type="MAFOOL_BIH", confidence=1.5)

    def test_tadmini_link_same_indices(self):
        """TadminiLink should raise if head_idx == dep_idx."""
        with pytest.raises(ValueError):
            TadminiLink(head_idx=0, dep_idx=0, link_type="IDAFA")


# ---------------------------------------------------------------------------
# Part 5.3: TaqyidiLinker
# ---------------------------------------------------------------------------

class TestTaqyidiLinker:

    def test_jar_majroor(self):
        """A preposition followed by a noun should produce JAR_MAJROOR."""
        words = [
            _particle(0, "في"),
            _noun(1, "الْبَيْتِ", case=Case.GENITIVE, definite=True),
        ]
        linker = TaqyidiLinker()
        links = linker.link(words)
        jar = [l for l in links if l.link_type == "JAR_MAJROOR"]
        assert len(jar) == 1
        assert jar[0].head_idx == 0
        assert jar[0].dep_idx == 1

    def test_shart(self):
        """A conditional particle followed by a verb should produce SHART."""
        words = [
            _particle(0, "إن"),
            _verb(1, "جَاءَ"),
        ]
        linker = TaqyidiLinker()
        links = linker.link(words)
        shart = [l for l in links if l.link_type == "SHART"]
        assert len(shart) == 1

    def test_haal(self):
        """A verb followed by an accusative noun should produce HAAL."""
        words = [
            _verb(0, "جَاءَ"),
            _noun(1, "فَرِحًا", case=Case.ACCUSATIVE),
        ]
        linker = TaqyidiLinker()
        links = linker.link(words)
        haal = [l for l in links if l.link_type == "HAAL"]
        assert len(haal) == 1

    def test_taqyidi_link_dataclass_valid(self):
        """TaqyidiLink should raise on invalid confidence."""
        with pytest.raises(ValueError):
            TaqyidiLink(head_idx=0, dep_idx=1, link_type="HAAL", confidence=2.0)

    def test_taqyidi_link_same_indices(self):
        """TaqyidiLink should raise if head_idx == dep_idx."""
        with pytest.raises(ValueError):
            TaqyidiLink(head_idx=1, dep_idx=1, link_type="JAR_MAJROOR")


# ---------------------------------------------------------------------------
# Part 5.4: SyntacticParser
# ---------------------------------------------------------------------------

class TestSyntacticParser:

    def test_syntactic_parser_runs(self):
        """SyntacticParser.parse() should return a SyntacticGraph with all three link lists."""
        words = [
            _noun(0, "الْكِتَابُ", definite=True),
            _noun(1, "مُفِيدٌ"),
        ]
        parser = SyntacticParser()
        graph = parser.parse(words)

        assert isinstance(graph, SyntacticGraph)
        assert hasattr(graph, 'isnadi_links')
        assert hasattr(graph, 'tadmini_links')
        assert hasattr(graph, 'taqyidi_links')
        assert isinstance(graph.isnadi_links, list)
        assert isinstance(graph.tadmini_links, list)
        assert isinstance(graph.taqyidi_links, list)

    def test_parser_nominal_sentence(self):
        """Parser should find an isnadi link in a nominal sentence."""
        words = [
            _noun(0, "الْكِتَابُ", definite=True),
            _noun(1, "مُفِيدٌ"),
        ]
        parser = SyntacticParser()
        graph = parser.parse(words)
        # Isnadi linker should find mubtada+khabar
        assert len(graph.isnadi_links) >= 1

    def test_parser_empty_input(self):
        """Parser should handle empty input gracefully."""
        parser = SyntacticParser()
        graph = parser.parse([])
        assert isinstance(graph, SyntacticGraph)
        assert graph.isnadi_links == []
        assert graph.tadmini_links == []
        assert graph.taqyidi_links == []


# ---------------------------------------------------------------------------
# Part 5.5: ConstraintValidator
# ---------------------------------------------------------------------------

class TestConstraintValidator:

    def test_no_violations(self):
        """A well-formed nominal sentence should produce no violations."""
        words = [
            _noun(0, "الْكِتَابُ", definite=True),
            _noun(1, "مُفِيدٌ"),
        ]
        parser = SyntacticParser()
        graph = parser.parse(words)

        validator = ConstraintValidator()
        violations = validator.validate(graph)
        assert isinstance(violations, list)
        # A simple well-formed sentence should have zero violations
        assert len(violations) == 0

    def test_subject_verb_agreement_violation(self):
        """Mismatched gender between subject and verb should produce SubjectVerbAgreement violation."""
        from fvafk.syntax.linkers.link import Link, LinkType

        # Build a graph manually with a gender mismatch
        verb = _verb(0, "كَتَبَ", gender=Gender.MASCULINE)
        subject = _noun(1, "الطَّالِبَةُ", case=Case.NOMINATIVE, gender=Gender.FEMININE)

        # Fake isnadi link verb → subject (verb is head)
        link = Link(link_type=LinkType.ISNADI, head_id=0, dependent_id=1, confidence=0.9)

        graph = SyntacticGraph(
            tokens=[verb, subject],
            isnadi_links=[link],
        )

        validator = ConstraintValidator()
        violations = validator.validate(graph)
        agreement_violations = [
            v for v in violations if v.constraint_name == "SubjectVerbAgreement"
        ]
        assert len(agreement_violations) == 1

    def test_isnadi_uniqueness_violation(self):
        """Two isnadi links to the same dependent should produce IsnadiUniqueness violation."""
        noun0 = _noun(0, "الطَّالِبُ", definite=True)
        noun1 = _noun(1, "مُجْتَهِدٌ")

        link1 = Link(link_type=LinkType.ISNADI, head_id=0, dependent_id=1, confidence=0.9)
        link2 = Link(link_type=LinkType.ISNADI, head_id=0, dependent_id=1, confidence=0.5)

        graph = SyntacticGraph(tokens=[noun0, noun1], isnadi_links=[link1, link2])
        validator = ConstraintValidator()
        violations = validator.validate(graph)
        uniqueness = [v for v in violations if v.constraint_name == "IsnadiUniqueness"]
        assert len(uniqueness) == 1

    def test_haal_accusative_violation(self):
        """A Haal with non-accusative case should produce HaalAccusative violation."""
        verb = _verb(0, "جَاءَ")
        haal_noun = _noun(1, "مُسْرِعًا", case=Case.NOMINATIVE)  # wrong case

        from fvafk.syntax.linkers.taqyidi_linker import TaqyidiLink
        tq_link = TaqyidiLink(head_idx=0, dep_idx=1, link_type="HAAL", confidence=0.7)

        graph = SyntacticGraph(tokens=[verb, haal_noun], taqyidi_links=[tq_link])
        validator = ConstraintValidator()
        violations = validator.validate(graph)
        haal_v = [v for v in violations if v.constraint_name == "HaalAccusative"]
        assert len(haal_v) == 1


# ---------------------------------------------------------------------------
# Part 5.1: IsnadiLinker (quick integration smoke test)
# ---------------------------------------------------------------------------

def test_isnadi_linker_verb_subject():
    """A verb followed by a nominative subject noun should potentially produce an ISNADI link."""
    from fvafk.syntax.linkers.isnadi_linker import IsnadiLinker
    words = [
        _verb(0, "كَتَبَ"),
        _noun(1, "الطَّالِبُ", case=Case.NOMINATIVE, definite=True),
    ]
    linker = IsnadiLinker()
    # verb at position 0 is not a noun, so it won't be treated as mubtada
    links = linker.find_links(words)
    # The verb is not a noun so no isnadi link; just confirm no error
    assert isinstance(links, list)


def test_isnadi_linker_nominal_sentence():
    """A mubtada followed by khabar should produce an ISNADI link."""
    from fvafk.syntax.linkers.isnadi_linker import IsnadiLinker
    words = [
        _noun(0, "الْكِتَابُ", case=Case.NOMINATIVE, definite=True),
        _noun(1, "مُفِيدٌ", case=Case.NOMINATIVE),
    ]
    linker = IsnadiLinker()
    links = linker.find_links(words)
    assert len(links) == 1
    assert links[0].link_type == LinkType.ISNADI


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
