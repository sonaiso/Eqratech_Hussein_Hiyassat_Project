"""Tests for syntax data models.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.1
"""

import pytest
from fvafk.c2b.syntax import (
    I3rabAnnotation,
    I3rabComponents,
    SyntaxFeatures,
    I3RAB_TYPE_AR_TO_EN,
    CASE_AR_TO_EN,
    map_i3rab_to_role,
    map_ar_to_en,
)


class TestI3rabAnnotation:
    """Test I3rabAnnotation (Layer 1)."""
    
    def test_creation(self):
        """Test creating I3rab annotation."""
        ann = I3rabAnnotation(
            word="الْحَمْدُ",
            i3rab_text="مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة",
            surah=1,
            ayah=2,
            word_index=0,
        )
        
        assert ann.word == "الْحَمْدُ"
        assert "مبتدأ" in ann.i3rab_text
        assert ann.surah == 1
        assert ann.ayah == 2
        assert ann.word_index == 0


class TestI3rabComponents:
    """Test I3rabComponents (Layer 2)."""
    
    def test_default_values(self):
        """Test default component values."""
        comp = I3rabComponents()
        
        assert comp.i3rab_type is None
        assert comp.case is None
        assert comp.confidence == 0.0
    
    def test_with_values(self):
        """Test components with values."""
        comp = I3rabComponents(
            i3rab_type="mubtada",
            case="nominative",
            case_marker="damma",
            confidence=0.9,
            raw_text="مبتدأ مرفوع",
        )
        
        assert comp.i3rab_type == "mubtada"
        assert comp.case == "nominative"
        assert comp.case_marker == "damma"
        assert comp.confidence == 0.9


class TestSyntaxFeatures:
    """Test SyntaxFeatures (Layer 3)."""
    
    def test_high_confidence(self):
        """Test high confidence - no warning."""
        feat = SyntaxFeatures(
            syntactic_role="subject",
            case="nominative",
            i3rab_type_ar="مبتدأ",
            i3rab_type_en="mubtada",
            confidence=0.9,
        )
        
        assert feat.warning is None
    
    def test_medium_confidence(self):
        """Test medium confidence - gets warning."""
        feat = SyntaxFeatures(
            syntactic_role="subject",
            case="nominative",
            i3rab_type_ar="مبتدأ",
            i3rab_type_en="mubtada",
            confidence=0.6,
        )
        
        assert feat.warning == "Medium confidence"
    
    def test_low_confidence(self):
        """Test low confidence - gets warning."""
        feat = SyntaxFeatures(
            syntactic_role="subject",
            case="nominative",
            i3rab_type_ar="مبتدأ",
            i3rab_type_en="mubtada",
            confidence=0.3,
        )
        
        assert feat.warning == "Low confidence - verify manually"


class TestMappings:
    """Test Arabic-English mappings."""
    
    def test_i3rab_type_mapping(self):
        """Test I3rab type mappings."""
        assert I3RAB_TYPE_AR_TO_EN["مبتدأ"] == "mubtada"
        assert I3RAB_TYPE_AR_TO_EN["خبر"] == "khabar"
        assert I3RAB_TYPE_AR_TO_EN["فاعل"] == "fa'il"
    
    def test_case_mapping(self):
        """Test case mappings."""
        assert CASE_AR_TO_EN["مرفوع"] == "nominative"
        assert CASE_AR_TO_EN["منصوب"] == "accusative"
        assert CASE_AR_TO_EN["مجرور"] == "genitive"
    
    def test_role_mapping(self):
        """Test I3rab to syntactic role mapping."""
        assert map_i3rab_to_role("mubtada") == "subject"
        assert map_i3rab_to_role("khabar") == "predicate"
        assert map_i3rab_to_role("fa'il") == "agent"
    
    def test_generic_mapper(self):
        """Test generic Arabic to English mapper."""
        assert map_ar_to_en("مبتدأ", "i3rab_type") == "mubtada"
        assert map_ar_to_en("مرفوع", "case") == "nominative"
        assert map_ar_to_en("الضمة", "case_marker") == "damma"
        assert map_ar_to_en("unknown", "i3rab_type") == "unknown"