"""
Tests for MorphologyFlagsExtractor.

Tests cover:
- Case extraction (nominative, accusative, genitive)
- Number extraction (singular, dual, plural)
- Gender extraction (masculine, feminine)
- Definiteness detection
- Edge cases and integration
"""

import pytest

from fvafk.c2b.morphology_flags import (
    MorphologyFlagsExtractor,
    MorphologyFlags,
    extract_morphology_flags,
)


class TestCaseExtraction:
    """Tests for case extraction."""
    
    def test_nominative_tanwin(self):
        """Test nominative case with dammatan (ٌ)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابٌ")
        
        assert flags.case == 'nominative'
    
    def test_accusative_tanwin(self):
        """Test accusative case with fathatan (ً)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابًا")
        
        assert flags.case == 'accusative'
    
    def test_genitive_tanwin(self):
        """Test genitive case with kasratan (ٍ)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابٍ")
        
        assert flags.case == 'genitive'
    
    def test_nominative_damma(self):
        """Test nominative case with damma (ُ)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابُ")
        
        assert flags.case == 'nominative'
    
    def test_accusative_fatha(self):
        """Test accusative case with fatha (َ)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابَ")
        
        assert flags.case == 'accusative'
    
    def test_genitive_kasra(self):
        """Test genitive case with kasra (ِ)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابِ")
        
        assert flags.case == 'genitive'
    
    def test_no_case_marker(self):
        """Test word without case marker."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كتاب")
        
        assert flags.case is None


class TestNumberExtraction:
    """Tests for number extraction."""
    
    def test_singular_default(self):
        """Test singular as default."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابٌ")
        
        assert flags.number == 'singular'
    
    def test_dual_nominative(self):
        """Test dual with nominative suffix (ان)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابَانِ")
        
        assert flags.number == 'dual'
    
    def test_dual_accusative_genitive(self):
        """Test dual with accusative/genitive suffix (ين)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابَيْنِ")
        
        assert flags.number == 'dual'
    
    def test_masculine_plural_nominative(self):
        """Test masculine plural nominative (ون)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مُعَلِّمُونَ")
        
        assert flags.number == 'plural'
    
    def test_masculine_plural_accusative(self):
        """Test masculine plural accusative/genitive (ين)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مُعَلِّمِينَ")
        
        assert flags.number == 'plural'
    
    def test_feminine_plural(self):
        """Test feminine plural (ات)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مُعَلِّمَاتٌ")
        
        assert flags.number == 'plural'
        assert flags.gender == 'feminine'


class TestGenderExtraction:
    """Tests for gender extraction."""
    
    def test_masculine_default(self):
        """Test masculine as default."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابٌ")
        
        assert flags.gender == 'masculine'
    
    def test_feminine_ta_marbuta(self):
        """Test feminine with ta marbuta (ة)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مَدْرَسَةٌ")
        
        assert flags.gender == 'feminine'
    
    def test_feminine_plural_suffix(self):
        """Test feminine from plural suffix (ات)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مُعَلِّمَاتٌ")
        
        assert flags.gender == 'feminine'
    
    def test_feminine_alif_hamza(self):
        """Test feminine ending with اء."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("صَحْرَاءُ")
        
        assert flags.gender == 'feminine'


class TestDefinitenessExtraction:
    """Tests for definiteness extraction."""
    
    def test_definite_with_al(self):
        """Test definite article ال."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابُ")
        
        assert flags.definiteness is True
    
    def test_indefinite_without_al(self):
        """Test indefinite without ال."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كِتَابٌ")
        
        assert flags.definiteness is False
    
    def test_definite_with_al_variations(self):
        """Test ال with different hamza forms."""
        extractor = MorphologyFlagsExtractor()
        
        # Different hamza forms
        assert extractor.extract("الكتاب").definiteness is True
        assert extractor.extract("ٱلْكِتَابُ").definiteness is True


class TestIntegration:
    """Integration tests combining multiple features."""
    
    def test_definite_nominative_singular_masculine(self):
        """Test: الْكِتَابُ (the book - nominative)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابُ")
        
        assert flags.definiteness is True
        assert flags.case == 'nominative'
        assert flags.number == 'singular'
        assert flags.gender == 'masculine'
        assert flags.confidence > 0.5
    
    def test_indefinite_accusative_singular_feminine(self):
        """Test: مَدْرَسَةً (a school - accusative)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("مَدْرَسَةً")
        
        assert flags.definiteness is False
        assert flags.case == 'accusative'
        assert flags.number == 'singular'
        assert flags.gender == 'feminine'
    
    def test_definite_genitive_plural_masculine(self):
        """Test: الْمُعَلِّمِينَ (the teachers - genitive)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْمُعَلِّمِينَ")
        
        assert flags.definiteness is True
        assert flags.case == 'genitive'  # May be None due to plural suffix
        assert flags.number == 'plural'
        assert flags.gender == 'masculine'
    
    def test_definite_nominative_dual_masculine(self):
        """Test: الْكِتَابَانِ (the two books - nominative)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابَانِ")
        
        assert flags.definiteness is True
        assert flags.number == 'dual'
        assert flags.gender == 'masculine'
    
    def test_definite_plural_feminine(self):
        """Test: الْمُعَلِّمَاتُ (the teachers-fem - nominative)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْمُعَلِّمَاتُ")
        
        assert flags.definiteness is True
        assert flags.case == 'nominative'
        assert flags.number == 'plural'
        assert flags.gender == 'feminine'


class TestConfidenceScoring:
    """Tests for confidence scoring."""
    
    def test_high_confidence_with_all_features(self):
        """Test high confidence when all features present."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْكِتَابُ")
        
        # Has definiteness, case, number, gender
        assert flags.confidence >= 0.8
    
    def test_lower_confidence_without_diacritics(self):
        """Test lower confidence without diacritics."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("كتاب")
        
        # No diacritics, less information
        assert flags.confidence < 0.8


class TestEdgeCases:
    """Tests for edge cases."""
    
    def test_empty_string(self):
        """Test empty string returns default flags."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("")
        
        assert flags.case is None
        assert flags.number is None
        assert flags.gender is None
        assert flags.definiteness is False
    
    def test_whitespace_only(self):
        """Test whitespace-only string."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("   ")
        
        assert flags.case is None
    
    def test_non_arabic_text(self):
        """Test non-Arabic text handled gracefully."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("hello")
        
        # Should not crash
        assert flags is not None
    
    def test_single_character(self):
        """Test single character."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("و")
        
        assert flags is not None
    
    def test_only_diacritics(self):
        """Test string with only diacritics."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("َُِّْ")
        
        assert flags is not None


class TestConvenienceFunction:
    """Tests for convenience function."""
    
    def test_convenience_function_works(self):
        """Test convenience function returns correct results."""
        flags = extract_morphology_flags("الْكِتَابُ")
        
        assert flags.definiteness is True
        assert flags.case == 'nominative'
    
    def test_convenience_function_multiple_calls(self):
        """Test convenience function can be called multiple times."""
        flags1 = extract_morphology_flags("كِتَابٌ")
        flags2 = extract_morphology_flags("مَدْرَسَةٌ")
        
        assert flags1.gender == 'masculine'
        assert flags2.gender == 'feminine'


class TestRealWorldExamples:
    """Tests with real-world Quranic examples."""
    
    def test_quran_bismillah(self):
        """Test: بِسْمِ (in the name of - genitive)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("بِسْمِ")
        
        assert flags.case == 'genitive'
        assert flags.number == 'singular'
    
    def test_quran_alhamdulillah(self):
        """Test: الْحَمْدُ (the praise - nominative)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الْحَمْدُ")
        
        assert flags.definiteness is True
        assert flags.case == 'nominative'
    
    def test_quran_alrahman(self):
        """Test: الرَّحْمَٰنِ (the Most Gracious - genitive)."""
        extractor = MorphologyFlagsExtractor()
        flags = extractor.extract("الرَّحْمَٰنِ")
        
        assert flags.definiteness is True
        assert flags.case == 'genitive'


class TestMorphologyFlagsDataclass:
    """Tests for MorphologyFlags dataclass."""
    
    def test_create_flags(self):
        """Test creating MorphologyFlags object."""
        flags = MorphologyFlags(
            case='nominative',
            number='singular',
            gender='masculine',
            definiteness=True,
            confidence=0.9
        )
        
        assert flags.case == 'nominative'
        assert flags.number == 'singular'
        assert flags.gender == 'masculine'
        assert flags.definiteness is True
        assert flags.confidence == 0.9
    
    def test_default_values(self):
        """Test default values."""
        flags = MorphologyFlags()
        
        assert flags.case is None
        assert flags.number is None
        assert flags.gender is None
        assert flags.definiteness is False
        assert flags.confidence == 0.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])