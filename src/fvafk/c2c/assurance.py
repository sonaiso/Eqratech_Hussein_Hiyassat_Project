"""
C2c — Assurance Mode and Falsifiability Protocol
Parts 2.5.4 + 2.5.5
"""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import Callable, List

from .evidence import EvidenceResult, MIN_SCORE, TruthStatus, ReferenceStatus


class AssuranceMode(Enum):
    STRICT  = "strict"
    RELAXED = "relaxed"


_THRESHOLDS = {
    AssuranceMode.STRICT:  0.7,
    AssuranceMode.RELAXED: 0.4,
}


def accepted_under_mode(result: EvidenceResult, mode: AssuranceMode) -> bool:
    threshold = _THRESHOLDS[mode]
    score_ok  = result.evidence.composed_score >= threshold
    if mode == AssuranceMode.STRICT:
        return score_ok and result.reality.all_ok
    else:
        truth_ok = result.reality.truth != TruthStatus.CONTRADICTED
        ref_ok   = result.reality.reference != ReferenceStatus.MISSING
        return score_ok and truth_ok and ref_ok


@dataclass
class FalsifiabilityClause:
    condition_name: str
    predicate:      Callable[[EvidenceResult], bool]
    description:    str = ""

    def is_falsified(self, result: EvidenceResult) -> bool:
        return self.predicate(result)


CLAUSE_LOW_SCORE = FalsifiabilityClause(
    condition_name="low_score",
    predicate=lambda r: r.evidence.composed_score < MIN_SCORE,
    description="Falsified if composed score falls below MIN_SCORE",
)
CLAUSE_CONTRADICTED = FalsifiabilityClause(
    condition_name="contradicted_truth",
    predicate=lambda r: not r.reality.truth_ok,
    description="Falsified if truth status is CONTRADICTED",
)
CLAUSE_MISSING_REF = FalsifiabilityClause(
    condition_name="missing_reference",
    predicate=lambda r: not r.reality.reference_ok,
    description="Falsified if referenced entity is not found",
)
CLAUSE_BAD_SCOPE = FalsifiabilityClause(
    condition_name="bad_scope",
    predicate=lambda r: not r.reality.scope_ok,
    description="Falsified if evidence scope is not applicable",
)

DEFAULT_CLAUSES: List[FalsifiabilityClause] = [
    CLAUSE_LOW_SCORE,
    CLAUSE_CONTRADICTED,
    CLAUSE_MISSING_REF,
    CLAUSE_BAD_SCOPE,
]


@dataclass
class FalsifiabilityProtocol:
    clauses: List[FalsifiabilityClause] = field(
        default_factory=lambda: list(DEFAULT_CLAUSES)
    )

    def check(self, result: EvidenceResult) -> "FalsifiabilityReport":
        triggered = [c for c in self.clauses if c.is_falsified(result)]
        return FalsifiabilityReport(result=result, triggered=triggered)


@dataclass
class FalsifiabilityReport:
    result:    EvidenceResult
    triggered: List[FalsifiabilityClause] = field(default_factory=list)

    @property
    def is_falsified(self) -> bool:
        return len(self.triggered) > 0

    @property
    def triggered_names(self) -> List[str]:
        return [c.condition_name for c in self.triggered]

    def to_dict(self) -> dict:
        return {
            "is_falsified":    self.is_falsified,
            "triggered":       self.triggered_names,
            "result_accepted": self.result.accepted,
            "score":           round(self.result.evidence.composed_score, 4),
        }
