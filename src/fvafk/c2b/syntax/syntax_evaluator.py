"""Syntax Evaluator - Compare syntax predictions vs gold standard.

Similar to MorphologyEvaluator but focused on I3rab (syntax) features.

Author: Hussein Hiyassat
Date: 2026-02-21
Sprint: 4 - Task 4.3
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional
from ..evaluation.metrics import ConfusionMatrix, compute_accuracy
from .models import I3rabComponents, SyntaxFeatures


@dataclass
class SyntaxMetrics:
    """Metrics for a single syntax feature."""
    feature_name: str
    confusion_matrix: ConfusionMatrix = field(default_factory=ConfusionMatrix)
    accuracy: float = 0.0
    total_predictions: int = 0
    correct_predictions: int = 0
    
    def compute_accuracy(self):
        """Compute accuracy from correct/total predictions."""
        self.accuracy = compute_accuracy(self.correct_predictions, self.total_predictions)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert metrics to dictionary."""
        cm_summary = self.confusion_matrix.summary()
        return {
            "feature": self.feature_name,
            "accuracy": self.accuracy,
            "total": self.total_predictions,
            "correct": self.correct_predictions,
            "macro_precision": cm_summary["macro_precision"],
            "macro_recall": cm_summary["macro_recall"],
            "macro_f1": cm_summary["macro_f1"],
            "micro_precision": cm_summary["micro_precision"],
            "micro_recall": cm_summary["micro_recall"],
            "micro_f1": cm_summary["micro_f1"],
            "per_class": cm_summary["per_class"],
        }


@dataclass
class SyntaxEvaluationResult:
    """Complete syntax evaluation results."""
    i3rab_type_metrics: SyntaxMetrics = field(default_factory=lambda: SyntaxMetrics("i3rab_type"))
    case_metrics: SyntaxMetrics = field(default_factory=lambda: SyntaxMetrics("case"))
    case_marker_metrics: SyntaxMetrics = field(default_factory=lambda: SyntaxMetrics("case_marker"))
    total_words: int = 0
    words_evaluated: int = 0
    coverage: float = 0.0  # Percentage of words successfully analyzed
    
    def overall_accuracy(self) -> float:
        """Compute overall accuracy across all features."""
        all_metrics = [
            self.i3rab_type_metrics,
            self.case_metrics,
            self.case_marker_metrics,
        ]
        total_correct = sum(m.correct_predictions for m in all_metrics)
        total_predictions = sum(m.total_predictions for m in all_metrics)
        return compute_accuracy(total_correct, total_predictions)
    
    def overall_f1(self) -> float:
        """Compute overall F1 score (macro average)."""
        all_metrics = [
            self.i3rab_type_metrics,
            self.case_metrics,
            self.case_marker_metrics,
        ]
        f1_scores = [m.to_dict()["macro_f1"] for m in all_metrics]
        valid_f1 = [f1 for f1 in f1_scores if f1 > 0]
        return sum(valid_f1) / len(valid_f1) if valid_f1 else 0.0
    
    def compute_coverage(self):
        """Compute coverage (% of words analyzed)."""
        if self.total_words > 0:
            self.coverage = self.words_evaluated / self.total_words
    
    def summary(self) -> Dict[str, Any]:
        """Generate summary dictionary."""
        return {
            "overall_accuracy": self.overall_accuracy(),
            "overall_f1": self.overall_f1(),
            "coverage": self.coverage,
            "total_words": self.total_words,
            "words_evaluated": self.words_evaluated,
            "features": {
                "i3rab_type": self.i3rab_type_metrics.to_dict(),
                "case": self.case_metrics.to_dict(),
                "case_marker": self.case_marker_metrics.to_dict(),
            }
        }


class SyntaxEvaluator:
    """Evaluate syntax predictions against gold standard.
    
    Compares predicted I3rab components against gold annotations.
    """
    
    def evaluate(
        self,
        predictions: List[I3rabComponents],
        gold_standard: List[I3rabComponents]
    ) -> SyntaxEvaluationResult:
        """Evaluate syntax predictions.
        
        Args:
            predictions: Predicted I3rab components
            gold_standard: Gold standard I3rab components
            
        Returns:
            SyntaxEvaluationResult with metrics
            
        Raises:
            ValueError: If prediction and gold lists have different lengths
        """
        if len(predictions) != len(gold_standard):
            raise ValueError(
                f"Prediction and gold lists must have same length. "
                f"Got {len(predictions)} vs {len(gold_standard)}"
            )
        
        result = SyntaxEvaluationResult()
        result.total_words = len(predictions)
        
        # Evaluate each word
        for pred, gold in zip(predictions, gold_standard):
            # Only count as evaluated if we extracted something
            if pred.i3rab_type or pred.case or pred.case_marker:
                result.words_evaluated += 1
            
            self._evaluate_word(pred, gold, result)
        
        # Compute accuracies
        result.i3rab_type_metrics.compute_accuracy()
        result.case_metrics.compute_accuracy()
        result.case_marker_metrics.compute_accuracy()
        result.compute_coverage()
        
        return result
    
    def _evaluate_word(
        self,
        pred: I3rabComponents,
        gold: I3rabComponents,
        result: SyntaxEvaluationResult
    ):
        """Evaluate a single word's syntax.
        
        Args:
            pred: Predicted components
            gold: Gold standard components
            result: Result object to update
        """
        # Evaluate I3rab type
        self._evaluate_feature(
            pred.i3rab_type,
            gold.i3rab_type,
            result.i3rab_type_metrics
        )
        
        # Evaluate case
        self._evaluate_feature(
            pred.case,
            gold.case,
            result.case_metrics
        )
        
        # Evaluate case marker
        self._evaluate_feature(
            pred.case_marker,
            gold.case_marker,
            result.case_marker_metrics
        )
    
    def _evaluate_feature(
        self,
        predicted: Optional[str],
        gold: Optional[str],
        metrics: SyntaxMetrics
    ):
        """Evaluate a single feature.
        
        Args:
            predicted: Predicted value
            gold: Gold standard value
            metrics: Metrics object to update
        """
        metrics.confusion_matrix.add_prediction(predicted, gold)
        metrics.total_predictions += 1
        
        if predicted == gold:
            metrics.correct_predictions += 1
    
    def evaluate_from_syntax_features(
        self,
        predictions: List[SyntaxFeatures],
        gold_standard: List[I3rabComponents]
    ) -> SyntaxEvaluationResult:
        """Evaluate from SyntaxFeatures (Layer 3) against I3rabComponents (Layer 2).
        
        Args:
            predictions: Predicted SyntaxFeatures
            gold_standard: Gold I3rabComponents
            
        Returns:
            SyntaxEvaluationResult
        """
        # Convert SyntaxFeatures to I3rabComponents for evaluation
        pred_components = [
            I3rabComponents(
                i3rab_type=feat.i3rab_type_en,
                case=feat.case,
                confidence=feat.confidence,
            )
            for feat in predictions
        ]
        
        return self.evaluate(pred_components, gold_standard)


# Convenience function
def evaluate_syntax(
    predictions: List[I3rabComponents],
    gold_standard: List[I3rabComponents]
) -> SyntaxEvaluationResult:
    """Evaluate syntax predictions (convenience function).
    
    Args:
        predictions: Predicted I3rab components
        gold_standard: Gold standard components
        
    Returns:
        Evaluation results
    """
    evaluator = SyntaxEvaluator()
    return evaluator.evaluate(predictions, gold_standard)