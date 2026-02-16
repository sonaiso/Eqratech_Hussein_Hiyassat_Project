"""
Tests for WordBoundaryDetector Plan B
"""

import pytest
from fvafk.c2b.word_boundary_detector import (
    WordBoundaryDetectorPlanB,
    WordBoundary,
    CliticDatabase,
    detect_word_boundaries
)


class TestCliticDatabase:
    """Test clitic database functionality"""
    
    def test_has_common_prefixes(self):
        """Test that database contains common prefixes"""
        prefixes = CliticDatabase.get_all_prefixes()
        assert 'ال' in prefixes  # definite article
        assert 'و' in prefixes   # conjunction
        assert 'ب' in prefixes   # preposition
        assert 'ل' in prefixes   # preposition
    
    def test_has_common_suffixes(self):
        """Test that database contains common suffixes"""
        suffixes = CliticDatabase.get_all_suffixes()
        assert 'ه' in suffixes   # his/him
        assert 'ها' in suffixes  # her
        assert 'هم' in suffixes  # their
        assert 'ك' in suffixes   # your
    
    def test_has_compound_prefixes(self):
        """Test compound prefixes exist"""
        prefixes = CliticDatabase.get_all_prefixes()
        assert 'وال' in prefixes  # و + ال
        assert 'فال' in prefixes  # ف + ال
        assert 'بال' in prefixes  # ب + ال


class TestWordBoundary:
    """Test WordBoundary dataclass"""
    
    def test_word_boundary_creation(self):
        """Test creating WordBoundary object"""
        boundary = WordBoundary(
            text="الكتاب",
            start=0,
            end=6,
            confidence=0.9,
            syllable_count=3,
            has_prefix=True,
            has_suffix=False
        )
        
        assert boundary.text == "الكتاب"
        assert boundary.start == 0
        assert boundary.end == 6
        assert boundary.confidence == 0.9
        assert boundary.syllable_count == 3
        assert boundary.has_prefix is True
        assert boundary.has_suffix is False
    
    def test_word_boundary_confidence_validation(self):
        """Test confidence must be in [0, 1]"""
        with pytest.raises(AssertionError):
            WordBoundary(
                text="test",
                start=0,
                end=4,
                confidence=1.5,  # Invalid
                syllable_count=1
            )
    
    def test_word_boundary_span_validation(self):
        """Test start must be <= end"""
        with pytest.raises(AssertionError):
            WordBoundary(
                text="test",
                start=10,
                end=5,  # Invalid: end before start
                confidence=0.5,
                syllable_count=1
            )


class TestWordBoundaryDetectorPlanB:
    """Test WordBoundaryDetector Plan B"""
    
    @pytest.fixture
    def detector(self):
        """Create detector instance"""
        return WordBoundaryDetectorPlanB()
    
    def test_detector_initialization(self, detector):
        """Test detector initializes correctly"""
        assert detector.syllabifier is not None
        assert detector.clitics is not None
    
    def test_empty_text(self, detector):
        """Test empty text returns empty list"""
        boundaries = detector.detect_boundaries("")
        assert boundaries == []
    
    def test_whitespace_only(self, detector):
        """Test whitespace-only text returns empty list"""
        boundaries = detector.detect_boundaries("   ")
        assert boundaries == []
    
    def test_single_word_simple(self, detector):
        """Test single simple word"""
        boundaries = detector.detect_boundaries("كتاب")
        
        assert len(boundaries) == 1
        assert boundaries[0].text == "كتاب"
        assert boundaries[0].start == 0
        assert boundaries[0].end == 4
        assert 0.0 <= boundaries[0].confidence <= 1.0
    
    def test_single_word_with_definite_article(self, detector):
        """Test word with ال prefix"""
        boundaries = detector.detect_boundaries("الكتاب")
        
        assert len(boundaries) == 1
        assert boundaries[0].text == "الكتاب"
        assert boundaries[0].has_prefix is True
        assert boundaries[0].confidence > 0.5  # Higher confidence with clitic
    
    def test_single_word_with_conjunction(self, detector):
        """Test word with و prefix"""
        boundaries = detector.detect_boundaries("وكتاب")
        
        assert len(boundaries) == 1
        assert boundaries[0].has_prefix is True
    
    def test_single_word_with_suffix(self, detector):
        """Test word with possessive suffix"""
        boundaries = detector.detect_boundaries("كتابه")
        
        assert len(boundaries) == 1
        assert boundaries[0].has_suffix is True
    
    def test_multiple_words(self, detector):
        """Test multiple words separated by spaces"""
        boundaries = detector.detect_boundaries("الكتاب على الطاولة")
        
        assert len(boundaries) == 3
        assert boundaries[0].text == "الكتاب"
        assert boundaries[1].text == "على"
        assert boundaries[2].text == "الطاولة"
    
    def test_word_with_diacritics(self, detector):
        """Test word with full diacritization"""
        boundaries = detector.detect_boundaries("الْكِتَابُ")
        
        assert len(boundaries) == 1
        assert boundaries[0].text == "الْكِتَابُ"  # Preserves original
        assert boundaries[0].has_prefix is True
    
    def test_compound_prefix(self, detector):
        """Test compound prefix (وال)"""
        boundaries = detector.detect_boundaries("والكتاب")
        
        assert len(boundaries) == 1
        assert boundaries[0].has_prefix is True
        assert boundaries[0].text == "والكتاب"
    
    def test_syllable_count_estimation(self, detector):
        """Test syllable counting"""
        boundaries = detector.detect_boundaries("كتاب")
        
        assert len(boundaries) == 1
        # كتاب has roughly 2 syllables: ki-taab
        assert boundaries[0].syllable_count >= 1
    
    def test_confidence_scoring(self, detector):
        """Test confidence scores are reasonable"""
        boundaries = detector.detect_boundaries("الكتاب")
        
        # Word with definite article should have high confidence
        assert boundaries[0].confidence >= 0.6
        
        # Very short word should have lower confidence
        boundaries_short = detector.detect_boundaries("في")
        assert boundaries_short[0].confidence < boundaries[0].confidence
    
    def test_span_offsets(self, detector):
        """Test span offsets are correct"""
        text = "الكتاب على الطاولة"
        boundaries = detector.detect_boundaries(text)
        
        # Verify each boundary extracts correct substring
        for boundary in boundaries:
            extracted = text[boundary.start:boundary.end]
            assert extracted == boundary.text
    
    def test_real_sentence(self, detector):
        """Test realistic Arabic sentence"""
        text = "ذَهَبَ الطَّالِبُ إِلَى الْمَدْرَسَةِ"
        boundaries = detector.detect_boundaries(text)
        
        assert len(boundaries) == 4
        assert all(b.confidence > 0.0 for b in boundaries)
        assert any(b.has_prefix for b in boundaries)  # At least one with prefix


class TestConvenienceFunction:
    """Test convenience function"""
    
    def test_detect_word_boundaries_function(self):
        """Test convenience function works"""
        boundaries = detect_word_boundaries("الكتاب على الطاولة")
        
        assert len(boundaries) == 3
        assert isinstance(boundaries[0], WordBoundary)
    
    def test_convenience_function_empty(self):
        """Test convenience function with empty text"""
        boundaries = detect_word_boundaries("")
        assert boundaries == []


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    @pytest.fixture
    def detector(self):
        return WordBoundaryDetectorPlanB()
    
    def test_single_character(self, detector):
        """Test single character word"""
        boundaries = detector.detect_boundaries("و")
        
        assert len(boundaries) == 1
        assert boundaries[0].text == "و"
    
    def test_very_long_word(self, detector):
        """Test very long word"""
        long_word = "استخراجاتهم"
        boundaries = detector.detect_boundaries(long_word)
        
        assert len(boundaries) == 1
        assert boundaries[0].confidence > 0.5  # Should be confident
    
    def test_numbers_mixed(self, detector):
        """Test text with numbers"""
        boundaries = detector.detect_boundaries("كتاب 123")
        
        assert len(boundaries) == 2
    
    def test_punctuation_attached(self, detector):
        """Test punctuation attached to words"""
        boundaries = detector.detect_boundaries("الكتاب،")
        
        # Punctuation gets grouped with word
        assert len(boundaries) == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
