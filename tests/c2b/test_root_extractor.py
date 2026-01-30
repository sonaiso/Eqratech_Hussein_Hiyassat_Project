"""Tests for RootExtractor."""

import pytest

from fvafk.c2b.morpheme import RootType
from fvafk.c2b.root_extractor import RootExtractor


class TestRootExtractorBasic:
    def test_simple_trilateral(self):
        extractor = RootExtractor()
        root = extractor.extract("كَتَبَ")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")
        assert root.root_type == RootType.TRILATERAL

    def test_without_diacritics(self):
        extractor = RootExtractor()
        root = extractor.extract("كتب")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_with_definite_article(self):
        extractor = RootExtractor()
        root = extractor.extract("الكِتَاب")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_active_participle(self):
        extractor = RootExtractor()
        root = extractor.extract("كَاتِب")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_passive_participle(self):
        extractor = RootExtractor()
        root = extractor.extract("مَكْتُوب")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")


class TestRootExtractorWeakRoots:
    def test_hollow_root(self):
        extractor = RootExtractor()
        root = extractor.extract("قَالَ")
        assert root is not None
        assert len(root.letters) == 3

    def test_defective_root(self):
        extractor = RootExtractor()
        root = extractor.extract("رَمَى")
        assert root is not None
        assert len(root.letters) == 3


class TestRootExtractorDoubled:
    def test_doubled_root(self):
        extractor = RootExtractor()
        root = extractor.extract("مَرَّ")
        assert root is not None
        assert len(root.letters) == 3


class TestRootExtractorQuadrilateral:
    def test_quadrilateral_root(self):
        extractor = RootExtractor()
        root = extractor.extract("دَحْرَجَ")
        assert root is not None
        assert len(root.letters) == 4
        assert root.root_type == RootType.QUADRILATERAL


class TestRootExtractorComplexAffixes:
    def test_multiple_prefixes(self):
        extractor = RootExtractor()
        root = extractor.extract("والكِتَاب")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_multiple_suffixes(self):
        extractor = RootExtractor()
        root = extractor.extract("كَاتِبُونَ")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_form_x(self):
        extractor = RootExtractor()
        root = extractor.extract("اسْتَكْتَبَ")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")


class TestRootExtractorNormalization:
    def test_hamza_normalization(self):
        extractor = RootExtractor()
        root1 = extractor.extract("أَكَلَ")
        root2 = extractor.extract("اكل")
        assert root1 is not None
        assert root2 is not None
        assert root1.letters == root2.letters

    def test_alif_maqsurah(self):
        extractor = RootExtractor()
        root = extractor.extract("رَمَى")
        assert root is not None
        assert len(root.letters) == 3


class TestRootExtractorValidation:
    def test_empty_string(self):
        extractor = RootExtractor()
        root = extractor.extract("")
        assert root is None

    def test_short_string(self):
        extractor = RootExtractor()
        root = extractor.extract("اب")
        assert root is None or len(root.letters) < 3

    def test_known_roots(self):
        known = {"ك-ت-ب", "ق-ر-أ"}
        extractor = RootExtractor(known_roots=known)
        root = extractor.extract("كَتَبَ")
        assert root is not None


class TestRootExtractorRealWorld:
    def test_quran_example_1(self):
        extractor = RootExtractor()
        root = extractor.extract("كِتَابٌ")
        assert root is not None
        assert root.letters == ("ك", "ت", "ب")

    def test_quran_example_2(self):
        extractor = RootExtractor()
        root = extractor.extract("مُؤْمِنُونَ")
        assert root is not None
        assert len(root.letters) == 3

    def test_quran_example_3(self):
        extractor = RootExtractor()
        root = extractor.extract("الرَّحْمَٰنِ")
        assert root is not None
        assert len(root.letters) == 3
