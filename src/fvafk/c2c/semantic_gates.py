"""
C2c — Semantic Gates Wrapper
Part 2.5.1: semantic_gates_wrapper as base layer
"""
from __future__ import annotations
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from .evidence import (
    EvidenceResult, EvidenceSource, EvidenceWeight,
    RealityLink, ReferenceStatus, ScopeStatus, TruthStatus,
)


@dataclass
class GateInput:
    word:      str
    root:      Optional[str]  = None
    pattern:   Optional[str]  = None
    kind:      str            = "unknown"
    link_conf: float          = 0.0
    extra:     Dict[str, Any] = field(default_factory=dict)


class SemanticGate(ABC):
    name: str = "base"

    @abstractmethod
    def evaluate(self, inp: GateInput) -> EvidenceResult: ...

    def __repr__(self) -> str:
        return f"<SemanticGate:{self.name}>"


class RootGate(SemanticGate):
    name = "root"

    def __init__(self, valid_roots: frozenset) -> None:
        self._roots = valid_roots

    def evaluate(self, inp: GateInput) -> EvidenceResult:
        root = inp.root or ""
        is_valid = bool(root) and root in self._roots
        ew = EvidenceWeight().add(
            source=EvidenceSource.LEXICON,
            score=0.9 if is_valid else 0.1,
            weight=1.5,
            note=f"root={root!r} valid={is_valid}",
        )
        rl = RealityLink(
            scope=ScopeStatus.OK,
            truth=TruthStatus.OK if is_valid else TruthStatus.UNVERIFIED,
            reference=ReferenceStatus.OK if is_valid else ReferenceStatus.MISSING,
        )
        return EvidenceResult(evidence=ew, reality=rl, label=f"root:{root}")


class PatternGate(SemanticGate):
    name = "pattern"

    def evaluate(self, inp: GateInput) -> EvidenceResult:
        pattern = inp.pattern or ""
        has_pattern = bool(pattern)
        score = min(0.9, 0.4 + len(pattern) * 0.05) if has_pattern else 0.1
        ew = EvidenceWeight().add(
            source=EvidenceSource.MORPHOLOGY,
            score=score,
            weight=1.2,
            note=f"pattern={pattern!r}",
        )
        rl = RealityLink(
            scope=ScopeStatus.OK,
            truth=TruthStatus.OK if has_pattern else TruthStatus.UNVERIFIED,
            reference=ReferenceStatus.OK if has_pattern else ReferenceStatus.AMBIGUOUS,
        )
        return EvidenceResult(evidence=ew, reality=rl, label=f"pattern:{pattern}")


class SyntaxGate(SemanticGate):
    name = "syntax"

    def evaluate(self, inp: GateInput) -> EvidenceResult:
        score = max(0.0, min(1.0, inp.link_conf))
        ew = EvidenceWeight().add(
            source=EvidenceSource.SYNTAX,
            score=score,
            weight=1.0,
            note=f"link_conf={score:.2f}",
        )
        rl = RealityLink(
            scope=ScopeStatus.OK,
            truth=TruthStatus.OK if score >= 0.5 else TruthStatus.UNVERIFIED,
            reference=ReferenceStatus.OK,
        )
        return EvidenceResult(evidence=ew, reality=rl, label="syntax")


class LexiconGate(SemanticGate):
    name = "lexicon"

    def __init__(self, lexicon: frozenset) -> None:
        self._lexicon = lexicon

    def evaluate(self, inp: GateInput) -> EvidenceResult:
        found = inp.word in self._lexicon or (inp.root or "") in self._lexicon
        score = 0.85 if found else 0.2
        ew = EvidenceWeight().add(
            source=EvidenceSource.LEXICON,
            score=score,
            weight=1.0,
            note=f"word={inp.word!r} in_lexicon={found}",
        )
        rl = RealityLink(
            scope=ScopeStatus.OK,
            truth=TruthStatus.OK,
            reference=ReferenceStatus.OK if found else ReferenceStatus.AMBIGUOUS,
        )
        return EvidenceResult(evidence=ew, reality=rl, label="lexicon")


def _merge_reality(realities: List[RealityLink]) -> RealityLink:
    def worst_scope(ss):
        order = [ScopeStatus.UNKNOWN, ScopeStatus.BROAD, ScopeStatus.NARROW, ScopeStatus.OK]
        return min(ss, key=lambda s: order.index(s) if s in order else -1)

    def worst_truth(ss):
        order = [TruthStatus.CONTRADICTED, TruthStatus.UNKNOWN, TruthStatus.UNVERIFIED, TruthStatus.OK]
        return min(ss, key=lambda s: order.index(s) if s in order else -1)

    def worst_ref(ss):
        order = [ReferenceStatus.MISSING, ReferenceStatus.UNKNOWN, ReferenceStatus.AMBIGUOUS, ReferenceStatus.OK]
        return min(ss, key=lambda s: order.index(s) if s in order else -1)

    notes: List[str] = []
    for r in realities:
        notes.extend(r.notes)

    return RealityLink(
        scope=worst_scope([r.scope for r in realities]),
        truth=worst_truth([r.truth for r in realities]),
        reference=worst_ref([r.reference for r in realities]),
        notes=notes,
    )


@dataclass
class SemanticGatesWrapper:
    gates: List[SemanticGate] = field(default_factory=list)

    def run(self, inp: GateInput) -> EvidenceResult:
        if not self.gates:
            raise ValueError("SemanticGatesWrapper has no gates registered.")
        results = [g.evaluate(inp) for g in self.gates]
        merged_ew = EvidenceWeight()
        for r in results:
            for item in r.evidence.items:
                merged_ew.items.append(item)
        merged_rl = _merge_reality([r.reality for r in results])
        labels = " | ".join(r.label for r in results if r.label)
        return EvidenceResult(evidence=merged_ew, reality=merged_rl, label=labels)

    def gate_names(self) -> List[str]:
        return [g.name for g in self.gates]
