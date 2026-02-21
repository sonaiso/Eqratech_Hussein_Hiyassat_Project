"""
Evaluation metrics for morphological analysis.

This package compares system predictions against gold-standard annotations.
It does NOT use gold data during analysis - only for evaluation.

Author: Hussein Hiyassat
Date: 2026-02-20
Sprint: 3 - Task 3.5
"""

from .metrics import (
    compute_precision,
    compute_recall,
    compute_f1_score,
    compute_accuracy,
    ConfusionMatrix,
)
from .evaluator import (
    MorphologyEvaluator,
    EvaluationResult,
    FeatureMetrics,
)

__all__ = [
    'compute_precision',
    'compute_recall',
    'compute_f1_score',
    'compute_accuracy',
    'ConfusionMatrix',
    'MorphologyEvaluator',
    'EvaluationResult',
    'FeatureMetrics',
]
