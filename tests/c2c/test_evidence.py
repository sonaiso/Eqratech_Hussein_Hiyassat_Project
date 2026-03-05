"""Tests for Part 2.5.2 — EvidenceWeight and RealityLink"""
import pytest
from fvafk.c2c import (
    EvidenceWeight, EvidenceSource, EvidenceResult,
    RealityLink, ScopeStatus, TruthStatus, ReferenceStatus,
    WeightedScore, MIN_SCORE,
)

def test_empty_evidence_score_is_zero():
    ew = EvidenceWeight()
    assert ew.composed_score == 0.0

def test_single_item_score():
    ew = EvidenceWeight().add(EvidenceSource.LEXICON, 0.8)
    assert ew.composed_score == pytest.approx(0.8)

def test_weighted_average():
    ew = EvidenceWeight()
    ew.add(EvidenceSource.LEXICON,    0.8, weight=2.0)
    ew.add(EvidenceSource.MORPHOLOGY, 0.4, weight=1.0)
    assert ew.composed_score == pytest.approx(2.0 / 3.0, rel=1e-4)

def test_dominant_source():
    ew = EvidenceWeight()
    ew.add(EvidenceSource.LEXICON,    0.8, weight=1.0)
    ew.add(EvidenceSource.MORPHOLOGY, 0.7, weight=3.0)
    assert ew.dominant_source == EvidenceSource.MORPHOLOGY

def test_score_out_of_range_raises():
    with pytest.raises(ValueError):
        WeightedScore(EvidenceSource.LEXICON, score=1.5)

def test_negative_weight_raises():
    with pytest.raises(ValueError):
        WeightedScore(EvidenceSource.LEXICON, score=0.5, weight=-1.0)

def test_to_dict_keys():
    ew = EvidenceWeight().add(EvidenceSource.SYNTAX, 0.6)
    d = ew.to_dict()
    assert "composed_score" in d
    assert "items" in d
    assert len(d["items"]) == 1

def test_all_ok_when_all_ok():
    rl = RealityLink(scope=ScopeStatus.OK, truth=TruthStatus.OK, reference=ReferenceStatus.OK)
    assert rl.all_ok is True

def test_all_ok_false_when_scope_bad():
    rl = RealityLink(scope=ScopeStatus.NARROW, truth=TruthStatus.OK, reference=ReferenceStatus.OK)
    assert rl.all_ok is False

def test_all_ok_false_when_truth_contradicted():
    rl = RealityLink(scope=ScopeStatus.OK, truth=TruthStatus.CONTRADICTED, reference=ReferenceStatus.OK)
    assert rl.all_ok is False

def test_accepted_when_score_and_reality_ok():
    ew = EvidenceWeight().add(EvidenceSource.LEXICON, 0.9)
    rl = RealityLink(ScopeStatus.OK, TruthStatus.OK, ReferenceStatus.OK)
    assert EvidenceResult(evidence=ew, reality=rl, label="test").accepted is True

def test_rejected_when_score_low():
    ew = EvidenceWeight().add(EvidenceSource.LEXICON, 0.3)
    rl = RealityLink(ScopeStatus.OK, TruthStatus.OK, ReferenceStatus.OK)
    r  = EvidenceResult(evidence=ew, reality=rl)
    assert r.accepted is False
    assert any("score" in reason for reason in r.rejection_reasons)

def test_rejected_when_reference_missing():
    ew = EvidenceWeight().add(EvidenceSource.LEXICON, 0.9)
    rl = RealityLink(ScopeStatus.OK, TruthStatus.OK, ReferenceStatus.MISSING)
    r  = EvidenceResult(evidence=ew, reality=rl)
    assert r.accepted is False
    assert any("reference" in reason for reason in r.rejection_reasons)

def test_min_score_boundary():
    ew_below = EvidenceWeight().add(EvidenceSource.LEXICON, MIN_SCORE - 0.01)
    ew_above = EvidenceWeight().add(EvidenceSource.LEXICON, MIN_SCORE)
    rl = RealityLink(ScopeStatus.OK, TruthStatus.OK, ReferenceStatus.OK)
    assert EvidenceResult(ew_below, rl).accepted is False
    assert EvidenceResult(ew_above, rl).accepted is True
