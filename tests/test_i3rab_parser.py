"""Tests for I3rab parser.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.2
"""

import pytest
from fvafk.c2b.syntax import I3rabParser, parse_i3rab, I3rabComponents


class TestI3rabParser:
    """Test I3rab parser."""
    
    def test_parse_mubtada(self):
        """Test parsing mubtada (مبتدأ)."""
        parser = I3rabParser()
        text = "مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "mubtada"
        assert result.case == "nominative"
        assert result.case_marker == "damma"
        assert result.confidence > 0.8
    
    def test_parse_khabar(self):
        """Test parsing khabar (خبر)."""
        parser = I3rabParser()
        text = "خبر مرفوع وعلامة رفعه الضمة"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "khabar"
        assert result.case == "nominative"
        assert result.case_marker == "damma"
    
    def test_parse_fail(self):
        """Test parsing fa'il (فاعل)."""
        parser = I3rabParser()
        text = "فاعل مرفوع وعلامة رفعه الضمة"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "fa'il"
        assert result.case == "nominative"
    
    def test_parse_mafool_bihi(self):
        """Test parsing maf'ul bihi (مفعول به)."""
        parser = I3rabParser()
        text = "مفعول به منصوب وعلامة نصبه الفتحة"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "maf'ul_bihi"
        assert result.case == "accusative"
        assert result.case_marker == "fatha"
    
    def test_parse_harf(self):
        """Test parsing harf (حرف)."""
        parser = I3rabParser()
        text = "حرف جر مبني على الكسر"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "harf"
        # مبني means indeclinable, no case extracted
        assert result.case is None
    
    def test_parse_with_mahall(self):
        """Test parsing with mahall (syntactic position)."""
        parser = I3rabParser()
        text = "ضمير متصل مبني في محل رفع فاعل"
        
        result = parser.parse(text)
        
        assert result.mahall == "في محل"
    
    def test_parse_no_mahall(self):
        """Test parsing 'لا محل له من الإعراب'."""
        parser = I3rabParser()
        text = "حرف لا محل له من الإعراب"
        
        result = parser.parse(text)
        
        assert result.mahall == "لا محل له"
    
    def test_confidence_scoring(self):
        """Test confidence scoring."""
        parser = I3rabParser()
        
        # Full information = high confidence
        full = parser.parse("مبتدأ مرفوع وعلامة رفعه الضمة في محل رفع")
        assert abs(full.confidence - 1.0) < 0.01
        
        # Only I3rab type = lower confidence
        partial = parser.parse("مبتدأ")
        assert partial.confidence == 0.4
        
        # No valid data = zero confidence
        empty = parser.parse("بعض النص العشوائي")
        assert empty.confidence == 0.0
    
    def test_parse_with_validation(self):
        """Test parse with validation."""
        parser = I3rabParser()
        
        # Valid parse
        components, is_valid = parser.parse_with_validation("مبتدأ مرفوع")
        assert is_valid is True
        assert components.i3rab_type == "mubtada"
        
        # Invalid parse (no I3rab type)
        components, is_valid = parser.parse_with_validation("نص عشوائي")
        assert is_valid is False
        assert components.i3rab_type is None
    
    def test_convenience_function(self):
        """Test convenience parse_i3rab function."""
        result = parse_i3rab("خبر منصوب وعلامة نصبه الفتحة")
        
        assert isinstance(result, I3rabComponents)
        assert result.i3rab_type == "khabar"
        assert result.case == "accusative"
    
    def test_empty_text(self):
        """Test parsing empty text."""
        parser = I3rabParser()
        result = parser.parse("")
        
        assert result.i3rab_type is None
        assert result.confidence == 0.0


class TestRealCorpusExamples:
    """Test with real examples from Quranic I3rab corpus."""
    
    def test_bismillah_first_word(self):
        """Test: بِسْمِ - from Bismillah."""
        parser = I3rabParser()
        # Simplified version of actual I3rab
        text = "اسم مجرور وعلامة جره الكسرة"
        
        result = parser.parse(text)
        
        assert result.case == "genitive"
        assert result.case_marker == "kasra"
    
    def test_alhamdulillah(self):
        """Test: الْحَمْدُ - from Al-Hamdulillah."""
        parser = I3rabParser()
        text = "مبتدأ مرفوع وعلامة رف��ه الضمة الظاهرة"
        
        result = parser.parse(text)
        
        assert result.i3rab_type == "mubtada"
        assert result.case == "nominative"
        assert result.case_marker == "damma"


