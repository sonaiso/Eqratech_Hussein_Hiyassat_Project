"""Tests for syntax evaluator.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.3
"""

import pytest
from fvafk.c2b.syntax import (
    SyntaxEvaluator,
    SyntaxEvaluationResult,
    SyntaxMetrics,
    I3rabComponents,
    SyntaxFeatures,
    evaluate_syntax,
)


class TestSyntaxEvaluator:
    """Test syntax evaluator."""
    
    def test_perfect_predictions(self):
        """Test evaluation with perfect predictions."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative", case_marker="damma"),
            I3rabComponents(i3rab_type="khabar", case="nominative", case_marker="damma"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        assert result.total_words == 2
        assert result.words_evaluated == 2
        assert result.i3rab_type_metrics.accuracy == 1.0
        assert result.case_metrics.accuracy == 1.0
        assert result.case_marker_metrics.accuracy == 1.0
        assert result.overall_accuracy() == 1.0
        assert result.coverage == 1.0
    
    def test_some_errors(self):
        """Test evaluation with some errors."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="fa'il", case="accusative"),  # Wrong type and case
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        assert result.total_words == 2
        assert result.i3rab_type_metrics.accuracy == 0.5  # 1/2 correct
        assert result.case_metrics.accuracy == 0.5  # 1/2 correct
    
    def test_mismatched_lengths(self):
        """Test that mismatched lengths raise error."""
        evaluator = SyntaxEvaluator()
        
        predictions = [I3rabComponents(i3rab_type="mubtada")]
        gold = [
            I3rabComponents(i3rab_type="mubtada"),
            I3rabComponents(i3rab_type="khabar"),
        ]
        
        with pytest.raises(ValueError, match="same length"):
            evaluator.evaluate(predictions, gold)
    
    def test_none_handling(self):
        """Test handling of None values."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type=None, case="nominative"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        assert result.i3rab_type_metrics.accuracy == 0.0
        assert result.case_metrics.accuracy == 1.0
    
    def test_coverage_calculation(self):
        """Test coverage calculation."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),  # Evaluated
            I3rabComponents(),  # Not evaluated (no data)
            I3rabComponents(case="genitive"),  # Evaluated (has case)
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
            I3rabComponents(i3rab_type="harf", case="genitive"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        assert result.total_words == 3
        assert result.words_evaluated == 2
        assert result.coverage == 2/3
    
    def test_overall_f1(self):
        """Test overall F1 score calculation."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
            I3rabComponents(i3rab_type="khabar", case="nominative"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        
        # Perfect predictions should have F1 = 1.0
        assert result.overall_f1() == 1.0
    
    def test_evaluate_from_syntax_features(self):
        """Test evaluating from SyntaxFeatures (Layer 3)."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            SyntaxFeatures(
                syntactic_role="subject",
                case="nominative",
                i3rab_type_ar="مبتدأ",
                i3rab_type_en="mubtada",
                confidence=0.9,
            ),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        result = evaluator.evaluate_from_syntax_features(predictions, gold)
        
        assert result.i3rab_type_metrics.accuracy == 1.0
        assert result.case_metrics.accuracy == 1.0
    
    def test_convenience_function(self):
        """Test convenience evaluate_syntax function."""
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        result = evaluate_syntax(predictions, gold)
        
        assert isinstance(result, SyntaxEvaluationResult)
        assert result.overall_accuracy() == 1.0
    
    def test_summary_generation(self):
        """Test summary dictionary generation."""
        evaluator = SyntaxEvaluator()
        
        predictions = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        gold = [
            I3rabComponents(i3rab_type="mubtada", case="nominative"),
        ]
        
        result = evaluator.evaluate(predictions, gold)
        summary = result.summary()
        
        assert "overall_accuracy" in summary
        assert "overall_f1" in summary
        assert "coverage" in summary
        assert "features" in summary
        assert "i3rab_type" in summary["features"]
        assert "case" in summary["features"]


class TestSyntaxMetrics:
    """Test SyntaxMetrics class."""
    
    def test_initialization(self):
        """Test metrics initialization."""
        metrics = SyntaxMetrics("test_feature")
        
        assert metrics.feature_name == "test_feature"
        assert metrics.accuracy == 0.0
        assert metrics.total_predictions == 0
        assert metrics.correct_predictions == 0
    
    def test_compute_accuracy(self):
        """Test accuracy computation."""
        metrics = SyntaxMetrics("test")
        metrics.total_predictions = 10
        metrics.correct_predictions = 7
        metrics.compute_accuracy()
        
        assert metrics.accuracy == 0.7
    
    def test_to_dict(self):
        """Test conversion to dictionary."""
        metrics = SyntaxMetrics("test")
        metrics.total_predictions = 10
        metrics.correct_predictions = 8
        metrics.compute_accuracy()
        
        result = metrics.to_dict()
        
        assert result["feature"] == "test"
        assert result["accuracy"] == 0.8
        assert result["total"] == 10
        assert result["correct"] == 8