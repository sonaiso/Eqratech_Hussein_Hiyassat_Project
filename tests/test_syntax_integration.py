"""Integration tests for syntax module.

Tests the full syntax pipeline with real corpus data.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.5
"""

import pytest
import pandas as pd
from pathlib import Path
from fvafk.c2b.syntax import (
    I3rabAnnotation,
    I3rabParser,
    parse_i3rab,
    I3rabComponents,
    SyntaxEvaluator,
    MorphSyntaxBridge,
)
from fvafk.c2b.morphology_flags import MorphologyFlags


class TestI3rabCorpusLoading:
    """Test loading I3rab corpus data."""
    
    def test_corpus_file_exists(self):
        """Test that I3rab corpus file exists."""
        corpus_path = Path("data/i3rab/quran_i3rab.csv")
        assert corpus_path.exists(), f"Corpus file not found: {corpus_path}"
    
    def test_load_corpus_sample(self):
        """Test loading a sample from corpus."""
        corpus_path = Path("data/i3rab/quran_i3rab.csv")
        
        if not corpus_path.exists():
            pytest.skip("Corpus file not found")
        
        df = pd.read_csv(corpus_path)
        
        # Check expected columns
        assert "word" in df.columns or "Word" in df.columns
        assert "i3rab" in df.columns or "I3rab" in df.columns or "Irab" in df.columns
        
        # Check we have data
        assert len(df) > 0
        assert len(df) >= 100  # At least 100 words


class TestParserIntegration:
    """Test I3rab parser with real corpus data."""
    
    def test_parse_real_mubtada(self):
        """Test parsing real mubtada example."""
        parser = I3rabParser()
        
        # Real example from corpus
        i3rab_text = "مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة على آخره"
        
        result = parser.parse(i3rab_text)
        
        assert result.i3rab_type == "mubtada"
        assert result.case == "nominative"
        assert result.case_marker == "damma"
        assert result.confidence > 0.8
    
    def test_parse_real_khabar(self):
        """Test parsing real khabar example."""
        parser = I3rabParser()
        
        i3rab_text = "خبر مرفوع وعلامة رفعه الضمة"
        
        result = parser.parse(i3rab_text)
        
        assert result.i3rab_type == "khabar"
        assert result.case == "nominative"
    
    def test_parse_real_fail(self):
        """Test parsing real fa'il example."""
        parser = I3rabParser()
        
        i3rab_text = "فاعل مرفوع وعلامة رفعه الضمة الظاهرة"
        
        result = parser.parse(i3rab_text)
        
        assert result.i3rab_type == "fa'il"
        assert result.case == "nominative"
    
    def test_parse_real_mafool(self):
        """Test parsing real maf'ul bihi example."""
        parser = I3rabParser()
        
        i3rab_text = "مفعول به منصوب وعلامة نصبه الفتحة الظاهرة على آخره"
        
        result = parser.parse(i3rab_text)
        
        assert result.i3rab_type == "maf'ul_bihi"
        assert result.case == "accusative"
        assert result.case_marker == "fatha"
    
    def test_parse_real_harf(self):
        """Test parsing real harf example."""
        parser = I3rabParser()
        
        i3rab_text = "حرف جر مبني على الكسر لا محل له من الإعراب"
        
        result = parser.parse(i3rab_text)
        
        assert result.i3rab_type == "harf"
        assert result.mahall == "لا محل له"


class TestEvaluatorIntegration:
    """Test syntax evaluator with realistic data."""
    
    def test_evaluate_perfect_predictions(self):
        """Test evaluator with perfect predictions."""
        evaluator = SyntaxEvaluator()
        
        # Simulate perfect predictions
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="fa'il", case="nominative", case_marker="damma"),
        ]
        
        gold = predictions.copy()
        
        result = evaluator.evaluate(predictions, gold)
        
        assert result.overall_accuracy() == 1.0
        assert result.coverage == 1.0
        assert result.total_words == 3
    
    def test_evaluate_with_errors(self):
        """Test evaluator with some errors."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="fa'il", case="accusative"),  # Wrong
            I3rabComponents(i3rab_type="khabar", case="nominative"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        # Should have 2/3 correct I3rab type, 2/3 correct case
        assert result.i3rab_type_metrics.accuracy == 2/3
        assert result.case_metrics.accuracy == 2/3


class TestBridgeIntegration:
    """Test morph-syntax bridge with realistic scenarios."""
    
    def test_bridge_simple_sentence(self):
        """Test bridge with simple sentence structure."""
        bridge = MorphSyntaxBridge()
        
        # الحمد لله (Al-Hamdu lillah)
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),   # الحمد
            MorphologyFlags(case="genitive", definiteness=False),    # لله
        ]
        
        predictions = bridge.predict_sentence(morphologies)
        
        assert len(predictions) == 2
        assert predictions[0].i3rab_type_en == "mubtada"
        assert predictions[0].syntactic_role == "subject"
        assert predictions[0].case == "nominative"
    
    def test_bridge_longer_sentence(self):
        """Test bridge with longer sentence."""
        bridge = MorphSyntaxBridge()
        
        # Simulate: [definite-nom] [indef-acc] [gen] [gen]
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),
            MorphologyFlags(case="accusative", definiteness=False),
            MorphologyFlags(case="genitive", definiteness=True),
            MorphologyFlags(case="genitive", definiteness=True),
        ]
        
        predictions = bridge.predict_sentence(morphologies)
        
        assert len(predictions) == 4
        assert predictions[0].i3rab_type_en == "mubtada"
        assert predictions[1].i3rab_type_en == "maf'ul_bihi"


class TestEndToEndPipeline:
    """Test complete end-to-end syntax pipeline."""
    
    def test_parse_and_evaluate(self):
        """Test parsing I3rab text and evaluating."""
        parser = I3rabParser()
        evaluator = SyntaxEvaluator()
        
        # Parse some I3rab texts
        i3rab_texts = [
            "مبتدأ مرفوع وعلامة رفعه الضمة",
            "خبر مرفوع وعلامة رفعه الضمة",
            "فاعل مرفوع وعلامة رفعه الضمة",
        ]
        
        predictions = [parser.parse(text) for text in i3rab_texts]
        
        # Create gold standard
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="fa'il", case="nominative", case_marker="damma"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        # Parser should extract all correctly
        assert result.overall_accuracy() == 1.0
    
    def test_morphology_to_syntax_pipeline(self):
        """Test full pipeline from morphology to syntax."""
        bridge = MorphSyntaxBridge()
        
        # Create morphology features
        morphologies = [
            MorphologyFlags(case="nominative", definiteness=True),
            MorphologyFlags(case="nominative", definiteness=False),
        ]
        
        # Predict syntax
        syntax_predictions = bridge.predict_sentence(morphologies)
        
        # Verify predictions
        assert len(syntax_predictions) == 2
        assert syntax_predictions[0].i3rab_type_en == "mubtada"
        assert syntax_predictions[1].i3rab_type_en == "khabar"
    
    def test_annotation_to_components(self):
        """Test converting annotation to components."""
        parser = I3rabParser()
        
        # Create annotation
        annotation = I3rabAnnotation(
            word="الْحَمْدُ",
            i3rab_text="مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة",
            surah=1,
            ayah=2,
            word_index=0,
        )
        
        # Parse to components
        components = parser.parse(annotation.i3rab_text)
        
        assert components.i3rab_type == "mubtada"
        assert components.case == "nominative"
        assert components.case_marker == "damma"


class TestRealWorldScenarios:
    """Test with real-world Quranic examples."""
    
    def test_fatiha_first_word(self):
        """Test first word of Al-Fatiha: الْحَمْدُ"""
        parser = I3rabParser()
        
        # Real I3rab for الحمد
        i3rab = "مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة على آخره"
        
        result = parser.parse(i3rab)
        
        assert result.i3rab_type == "mubtada"
        assert result.case == "nominative"
        assert result.confidence >= 0.8
    
    def test_bismillah_words(self):
        """Test Bismillah words parsing."""
        parser = I3rabParser()
        
        # بِسْمِ - typically starts with preposition construction
        # Simplified I3rab
        i3rab_bism = "اسم مجرور وعلامة جره الكسرة"
        
        result = parser.parse(i3rab_bism)
        
        assert result.case == "genitive"
        assert result.case_marker == "kasra"
    
    def test_prediction_confidence_levels(self):
        """Test that confidence levels are reasonable."""
        parser = I3rabParser()
        
        test_cases = [
            ("مبتدأ مرفوع وعلامة رفعه الضمة الظاهرة على آخره", 0.9),  # Full info
            ("مبتدأ مرفوع وعلامة رفعه الضمة", 0.8),  # Good info
            ("مبتدأ مرفوع", 0.6),  # Partial info
            ("مبتدأ", 0.4),  # Minimal info
        ]
        
        for i3rab_text, min_confidence in test_cases:
            result = parser.parse(i3rab_text)
            assert result.confidence >= min_confidence - 0.1, \
                f"Expected confidence >= {min_confidence} for '{i3rab_text}', got {result.confidence}"