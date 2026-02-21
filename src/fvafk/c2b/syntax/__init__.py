"""Syntax package - I3rab and syntax analysis."""

from .models import (
    I3rabAnnotation,
    I3rabComponents,
    SyntaxFeatures,
)

from .mappings import (
    I3RAB_TYPE_AR_TO_EN,
    CASE_AR_TO_EN,
    CASE_MARKER_AR_TO_EN,
    map_i3rab_to_role,
    map_ar_to_en,
)

from .i3rab_parser import (
    I3rabParser,
    parse_i3rab,
)

from .syntax_evaluator import (
    SyntaxMetrics,
    SyntaxEvaluationResult,
    SyntaxEvaluator,
    evaluate_syntax,
)

from .morph_syntax_bridge import (
    MorphSyntaxBridge,
    SimpleContextAnalyzer,
    predict_syntax_from_morphology,
)

__all__ = [
    # Models
    "I3rabAnnotation",
    "I3rabComponents",
    "SyntaxFeatures",
    # Mappings
    "I3RAB_TYPE_AR_TO_EN",
    "CASE_AR_TO_EN",
    "CASE_MARKER_AR_TO_EN",
    "map_i3rab_to_role",
    "map_ar_to_en",
    # Parser
    "I3rabParser",
    "parse_i3rab",
    # Evaluator
    "SyntaxMetrics",
    "SyntaxEvaluationResult",
    "SyntaxEvaluator",
    "evaluate_syntax",
    # Bridge
    "MorphSyntaxBridge",
    "SimpleContextAnalyzer",
    "predict_syntax_from_morphology",
]