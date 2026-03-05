"""C2c — Semantic gates and evidence integration (Part 2.5)"""
from .evidence import (
    EvidenceWeight, EvidenceSource, EvidenceResult,
    RealityLink, ScopeStatus, TruthStatus, ReferenceStatus,
    WeightedScore, MIN_SCORE,
)
from .semantic_gates import (
    SemanticGate, SemanticGatesWrapper, GateInput,
    RootGate, PatternGate, SyntaxGate, LexiconGate,
)
from .assurance import (
    AssuranceMode, accepted_under_mode,
    FalsifiabilityProtocol, FalsifiabilityReport,
    FalsifiabilityClause, DEFAULT_CLAUSES,
)
__all__ = [
    "EvidenceWeight", "EvidenceSource", "EvidenceResult",
    "RealityLink", "ScopeStatus", "TruthStatus", "ReferenceStatus",
    "WeightedScore", "MIN_SCORE",
    "SemanticGate", "SemanticGatesWrapper", "GateInput",
    "RootGate", "PatternGate", "SyntaxGate", "LexiconGate",
    "AssuranceMode", "accepted_under_mode",
    "FalsifiabilityProtocol", "FalsifiabilityReport",
    "FalsifiabilityClause", "DEFAULT_CLAUSES",
]
