"""
C2c — Evidence and Reality Integration
Part 2.5.2: EvidenceWeight composition and RealityLink checks
"""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import List, Optional


class EvidenceSource(Enum):
    PHONOLOGY  = "phonology"
    MORPHOLOGY = "morphology"
    SYNTAX     = "syntax"
    LEXICON    = "lexicon"
    CORPUS     = "corpus"
    MANUAL     = "manual"
    HEURISTIC  = "heuristic"


class ScopeStatus(Enum):
    OK      = "ok"
    NARROW  = "narrow"
    BROAD   = "broad"
    UNKNOWN = "unknown"


class TruthStatus(Enum):
    OK           = "ok"
    CONTRADICTED = "contradicted"
    UNVERIFIED   = "unverified"
    UNKNOWN      = "unknown"


class ReferenceStatus(Enum):
    OK        = "ok"
    MISSING   = "missing"
    AMBIGUOUS = "ambiguous"
    UNKNOWN   = "unknown"


@dataclass
class WeightedScore:
    source: EvidenceSource
    score:  float
    weight: float = 1.0
    note:   Optional[str] = None

    def __post_init__(self) -> None:
        if not 0.0 <= self.score <= 1.0:
            raise ValueError(f"score must be in [0,1], got {self.score}")
        if self.weight < 0:
            raise ValueError(f"weight must be >= 0, got {self.weight}")


@dataclass
class EvidenceWeight:
    items: List[WeightedScore] = field(default_factory=list)

    def add(self, source: EvidenceSource, score: float,
            weight: float = 1.0, note: Optional[str] = None) -> "EvidenceWeight":
        self.items.append(WeightedScore(source, score, weight, note))
        return self

    @property
    def composed_score(self) -> float:
        if not self.items:
            return 0.0
        total_weight = sum(i.weight for i in self.items)
        if total_weight == 0.0:
            return 0.0
        return sum(i.score * i.weight for i in self.items) / total_weight

    @property
    def dominant_source(self) -> Optional[EvidenceSource]:
        if not self.items:
            return None
        return max(self.items, key=lambda i: i.weight).source

    def to_dict(self) -> dict:
        return {
            "composed_score": round(self.composed_score, 4),
            "dominant_source": self.dominant_source.value if self.dominant_source else None,
            "items": [{"source": i.source.value, "score": i.score,
                       "weight": i.weight, "note": i.note} for i in self.items],
        }


@dataclass
class RealityLink:
    scope:     ScopeStatus     = ScopeStatus.UNKNOWN
    truth:     TruthStatus     = TruthStatus.UNKNOWN
    reference: ReferenceStatus = ReferenceStatus.UNKNOWN
    notes:     List[str]       = field(default_factory=list)

    @property
    def scope_ok(self) -> bool:
        return self.scope == ScopeStatus.OK

    @property
    def truth_ok(self) -> bool:
        return self.truth == TruthStatus.OK

    @property
    def reference_ok(self) -> bool:
        return self.reference == ReferenceStatus.OK

    @property
    def all_ok(self) -> bool:
        return self.scope_ok and self.truth_ok and self.reference_ok

    def to_dict(self) -> dict:
        return {
            "scope": self.scope.value, "truth": self.truth.value,
            "reference": self.reference.value,
            "scope_ok": self.scope_ok, "truth_ok": self.truth_ok,
            "reference_ok": self.reference_ok, "all_ok": self.all_ok,
            "notes": self.notes,
        }


MIN_SCORE: float = 0.5


@dataclass
class EvidenceResult:
    evidence: EvidenceWeight
    reality:  RealityLink
    label:    str = ""

    @property
    def accepted(self) -> bool:
        return self.evidence.composed_score >= MIN_SCORE and self.reality.all_ok

    @property
    def rejection_reasons(self) -> List[str]:
        reasons: List[str] = []
        if self.evidence.composed_score < MIN_SCORE:
            reasons.append(f"score {self.evidence.composed_score:.3f} < {MIN_SCORE}")
        if not self.reality.scope_ok:
            reasons.append(f"scope={self.reality.scope.value}")
        if not self.reality.truth_ok:
            reasons.append(f"truth={self.reality.truth.value}")
        if not self.reality.reference_ok:
            reasons.append(f"reference={self.reality.reference.value}")
        return reasons

    def to_dict(self) -> dict:
        return {
            "label": self.label, "accepted": self.accepted,
            "rejection_reasons": self.rejection_reasons,
            "evidence": self.evidence.to_dict(), "reality": self.reality.to_dict(),
        }
