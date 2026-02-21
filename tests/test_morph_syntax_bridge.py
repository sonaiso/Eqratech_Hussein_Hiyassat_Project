"""Tests for morph-syntax bridge.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.4
"""

import pytest
from fvafk.c2b.morphology_flags import MorphologyFlags
from fvafk.c2b.syntax import (
    MorphSyntaxBridge,
    SimpleContextAnalyzer,
    SyntaxFeatures,
    predict_syntax_from_morphology,
)


class TestMorphSyntaxBridge:
    """Test morph-syntax bridge."""
    
    def test_mubtada_inference(self):
        """Test inferring mubtada (subject at sentence start)."""
        bridge = MorphSyntaxBridge()
        
        # Definite nominative at start → mubtada
        morph = MorphologyFlags(
            case="nominative",
            definiteness=True,
        )
        
        i3rab_type, conf = bridge.infer_i3rab_type(morph, position=0, total_words=5)
        
        assert i3rab_type == "mubtada"
        assert conf == 0.8
    
    def test_mafool_bihi_inference(self):
        """Test inferring maf'ul bihi (object)."""
        bridge = MorphSyntaxBridge()
        
        # Indefinite accusative → maf'ul bihi
        morph = MorphologyFlags(
            case="accusative",
            definiteness=False,
        )
        
        i3rab_type, conf = bridge.infer_i3rab_type(morph, position=2, total_words=5)
        
        assert i3rab_type == "maf'ul_bihi"
        assert conf == 0.7
    
    def test_genitive_after_word(self):
        """Test genitive case inference."""
        bridge = MorphSyntaxBridge()
        
        morph = MorphologyFlags(case="genitive")
        prev_morph = MorphologyFlags(case="nominative")
        
        i3rab_type, conf = bridge.infer_i3rab_type(
            morph, position=2, total_words=5, prev_morph=prev_morph
        )
        
        # Should infer mudaf_ilayhi or harf
        assert i3rab_type in ["mudaf_ilayhi", "harf"]
    
    def test_khabar_inference(self):
        """Test inferring khabar (predicate)."""
        bridge = MorphSyntaxBridge()
        
        morph = MorphologyFlags(case="nominative")
        prev_morph = MorphologyFlags(case="nominative")
        
        i3rab_type, conf = bridge.infer_i3rab_type(
            morph, position=1, total_words=3, prev_morph=prev_morph
        )
        
        assert i3rab_type == "khabar"
    
    def test_predict_syntax(self):
        """Test full syntax prediction."""
        bridge = MorphSyntaxBridge()
        
        morph = MorphologyFlags(
            case="nominative",
            definiteness=True,
        )
        
        syntax = bridge.predict_syntax(morph, position=0, total_words=3)
        
        assert isinstance(syntax, SyntaxFeatures)
        assert syntax.i3rab_type_en == "mubtada"
        assert syntax.syntactic_role == "subject"
        assert syntax.case == "nominative"
        assert syntax.confidence > 0.0
    
    def test_predict_sentence(self):
        """Test predicting entire sentence."""
        bridge = MorphSyntaxBridge()
        
        # الحمد لله (Al-Hamdu lillah)
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),  # الحمد (mubtada)
            MorphologyFlags(case="genitive", definiteness=False),   # لله (khabar with prep)
        ]
        
        predictions = bridge.predict_sentence(morphologies)
        
        assert len(predictions) == 2
        assert predictions[0].i3rab_type_en == "mubtada"
        assert all(isinstance(p, SyntaxFeatures) for p in predictions)
    
    def test_unknown_inference(self):
        """Test unknown inference when no rules match."""
        bridge = MorphSyntaxBridge()
        
        morph = MorphologyFlags(case=None)
        
        i3rab_type, conf = bridge.infer_i3rab_type(morph, position=0, total_words=1)
        
        assert i3rab_type == "unknown"
        assert conf == 0.0


class TestSimpleContextAnalyzer:
    """Test context analyzer."""
    
    def test_is_after_verb(self):
        """Test detecting position after verb."""
        morphologies = [
            MorphologyFlags(case="nominative"),
            MorphologyFlags(case="accusative"),
        ]
        
        # Currently returns False (not implemented without POS)
        assert SimpleContextAnalyzer.is_after_verb(morphologies, 1) is False
        assert SimpleContextAnalyzer.is_after_verb(morphologies, 0) is False
    
    def test_is_after_preposition(self):
        """Test detecting position after preposition."""
        morphologies = [
            MorphologyFlags(case="genitive"),  # Genitive suggests preposition
            MorphologyFlags(case="nominative"),
        ]
        
        # Previous word genitive → likely after preposition
        assert SimpleContextAnalyzer.is_after_preposition(morphologies, 1) is True
        assert SimpleContextAnalyzer.is_after_preposition(morphologies, 0) is False
    
    def test_is_sentence_start(self):
        """Test sentence start detection."""
        assert SimpleContextAnalyzer.is_sentence_start(0) is True
        assert SimpleContextAnalyzer.is_sentence_start(1) is False
    
    def test_is_sentence_end(self):
        """Test sentence end detection."""
        assert SimpleContextAnalyzer.is_sentence_end(4, 5) is True
        assert SimpleContextAnalyzer.is_sentence_end(3, 5) is False


class TestConvenienceFunction:
    """Test convenience function."""
    
    def test_predict_syntax_from_morphology(self):
        """Test convenience function."""
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),
            MorphologyFlags(case="genitive", definiteness=False),
        ]
        
        predictions = predict_syntax_from_morphology(morphologies)
        
        assert len(predictions) == 2
        assert all(isinstance(p, SyntaxFeatures) for p in predictions)
        assert predictions[0].i3rab_type_en == "mubtada"


class TestRealExamples:
    """Test with real sentence examples."""
    
    def test_bismillah(self):
        """Test: بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ"""
        bridge = MorphSyntaxBridge()
        
        morphologies = [
            MorphologyFlags(case="genitive", definiteness=False),  # بسم
            MorphologyFlags(case="genitive", definiteness=True),   # الله
            MorphologyFlags(case="genitive", definiteness=True),   # الرحمن
            MorphologyFlags(case="genitive", definiteness=True),   # الرحيم
        ]
        
        predictions = bridge.predict_sentence(morphologies)
        
        assert len(predictions) == 4
        # All should have genitive case
        assert all(p.case == "genitive" for p in predictions)
    
    def test_alhamdulillah(self):
        """Test: الْحَمْدُ لِلَّهِ"""
        bridge = MorphSyntaxBridge()
        
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),  # الحمد
            MorphologyFlags(case="genitive", definiteness=False),   # لله
        ]
        
        predictions = bridge.predict_sentence(morphologies)
        
        assert len(predictions) == 2
        assert predictions[0].i3rab_type_en == "mubtada"
        assert predictions[0].syntactic_role == "subject"