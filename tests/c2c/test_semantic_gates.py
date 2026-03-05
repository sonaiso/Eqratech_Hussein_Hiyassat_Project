"""Tests for Part 2.5.1 + 2.5.4 + 2.5.5 — Gates, Assurance, Falsifiability"""
import pytest
from fvafk.c2c import (
    GateInput, RootGate, PatternGate, SyntaxGate, LexiconGate,
    SemanticGatesWrapper, EvidenceSource,
    AssuranceMode, accepted_under_mode,
    FalsifiabilityProtocol, DEFAULT_CLAUSES,
    EvidenceWeight, RealityLink, EvidenceResult,
    ScopeStatus, TruthStatus, ReferenceStatus,
)

ROOTS = frozenset({"كتب", "قرأ", "علم", "درس"})
LEXICON = frozenset({"كَتَبَ", "كتب", "قرأ", "الكتاب"})

# ── RootGate ────────────────────────────────────────────────

def test_root_gate_valid_root():
    gate = RootGate(ROOTS)
    inp  = GateInput(word="كَتَبَ", root="كتب")
    r    = gate.evaluate(inp)
    assert r.accepted is True
    assert r.evidence.composed_score >= 0.5

def test_root_gate_invalid_root():
    gate = RootGate(ROOTS)
    inp  = GateInput(word="xyz", root="xyz")
    r    = gate.evaluate(inp)
    assert r.accepted is False

def test_root_gate_empty_root():
    gate = RootGate(ROOTS)
    r    = gate.evaluate(GateInput(word="كَتَبَ", root=None))
    assert r.accepted is False

# ── PatternGate ─────────────────────────────────────────────

def test_pattern_gate_with_pattern():
    gate = PatternGate()
    r    = gate.evaluate(GateInput(word="كَتَبَ", pattern="فَعَلَ"))
    assert r.accepted is True

def test_pattern_gate_no_pattern():
    gate = PatternGate()
    r    = gate.evaluate(GateInput(word="كَتَبَ", pattern=None))
    assert r.accepted is False

def test_pattern_gate_longer_pattern_higher_score():
    gate  = PatternGate()
    short = gate.evaluate(GateInput(word="x", pattern="فع")).evidence.composed_score
    long_ = gate.evaluate(GateInput(word="x", pattern="فَعَلَ")).evidence.composed_score
    assert long_ >= short

# ── SyntaxGate ──────────────────────────────────────────────

def test_syntax_gate_high_conf():
    gate = SyntaxGate()
    r    = gate.evaluate(GateInput(word="كَتَبَ", link_conf=0.9))
    assert r.accepted is True

def test_syntax_gate_low_conf():
    gate = SyntaxGate()
    r    = gate.evaluate(GateInput(word="كَتَبَ", link_conf=0.1))
    assert r.accepted is False

def test_syntax_gate_clamps_over_one():
    gate = SyntaxGate()
    r    = gate.evaluate(GateInput(word="x", link_conf=999.0))
    assert r.evidence.composed_score <= 1.0

# ── LexiconGate ─────────────────────────────────────────────

def test_lexicon_gate_found():
    gate = LexiconGate(LEXICON)
    r    = gate.evaluate(GateInput(word="كَتَبَ", root="كتب"))
    assert r.accepted is True

def test_lexicon_gate_not_found():
    gate = LexiconGate(LEXICON)
    r    = gate.evaluate(GateInput(word="مجهول", root="مجه"))
    assert r.accepted is False

# ── SemanticGatesWrapper ────────────────────────────────────

def test_wrapper_merges_gates():
    wrapper = SemanticGatesWrapper(gates=[
        RootGate(ROOTS),
        PatternGate(),
        SyntaxGate(),
    ])
    inp = GateInput(word="كَتَبَ", root="كتب", pattern="فَعَلَ", link_conf=0.8)
    r   = wrapper.run(inp)
    assert len(r.evidence.items) == 3

def test_wrapper_accepted_all_good():
    wrapper = SemanticGatesWrapper(gates=[RootGate(ROOTS), PatternGate()])
    inp = GateInput(word="كَتَبَ", root="كتب", pattern="فَعَلَ")
    r   = wrapper.run(inp)
    assert r.accepted is True

def test_wrapper_no_gates_raises():
    wrapper = SemanticGatesWrapper(gates=[])
    with pytest.raises(ValueError):
        wrapper.run(GateInput(word="x"))

def test_wrapper_gate_names():
    wrapper = SemanticGatesWrapper(gates=[RootGate(ROOTS), SyntaxGate()])
    assert wrapper.gate_names() == ["root", "syntax"]

# ── AssuranceMode ────────────────────────────────────────────

def _make_result(score: float, all_ok: bool = True) -> EvidenceResult:
    ew = EvidenceWeight().add(EvidenceSource.LEXICON, score)
    scope = ScopeStatus.OK if all_ok else ScopeStatus.NARROW
    rl = RealityLink(scope=scope, truth=TruthStatus.OK, reference=ReferenceStatus.OK)
    return EvidenceResult(evidence=ew, reality=rl)

def test_strict_mode_accepts_high_score():
    r = _make_result(0.8)
    assert accepted_under_mode(r, AssuranceMode.STRICT) is True

def test_strict_mode_rejects_medium_score():
    r = _make_result(0.55)
    assert accepted_under_mode(r, AssuranceMode.STRICT) is False

def test_relaxed_mode_accepts_medium_score():
    r = _make_result(0.55)
    assert accepted_under_mode(r, AssuranceMode.RELAXED) is True

def test_relaxed_mode_rejects_very_low_score():
    r = _make_result(0.2)
    assert accepted_under_mode(r, AssuranceMode.RELAXED) is False

def test_strict_mode_rejects_bad_reality():
    r = _make_result(0.8, all_ok=False)
    assert accepted_under_mode(r, AssuranceMode.STRICT) is False

# ── FalsifiabilityProtocol ───────────────────────────────────

def test_falsifiability_no_trigger_on_good_result():
    r  = _make_result(0.8)
    fp = FalsifiabilityProtocol()
    report = fp.check(r)
    assert report.is_falsified is False
    assert report.triggered_names == []

def test_falsifiability_triggers_low_score():
    r  = _make_result(0.2)
    fp = FalsifiabilityProtocol()
    report = fp.check(r)
    assert report.is_falsified is True
    assert "low_score" in report.triggered_names

def test_falsifiability_report_to_dict():
    r      = _make_result(0.2)
    report = FalsifiabilityProtocol().check(r)
    d      = report.to_dict()
    assert "is_falsified" in d
    assert "triggered" in d
    assert "score" in d
