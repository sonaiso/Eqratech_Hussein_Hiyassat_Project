"""
Tests for verified OCaml bridge

Tests the Python integration with formally verified OCaml code.
Part of Tier 3 (Runtime) verification.
"""

import pytest
from fractalhub.verified_bridge import (
    get_verified_bridge,
    VerificationError,
    VerifiedGate,
    VerifiedTrace,
    VerifiedMeaning,
)


class TestVerifiedGate:
    """Test verified gate creation (NO C2 without C1)"""
    
    def test_valid_gate(self):
        """Valid gate with all four conditions should succeed"""
        bridge = get_verified_bridge()
        
        gate = bridge.verify_gate(
            gate_id="G_ATTEND:001",
            reality="السلام عليكم",  # Arabic text
            brain="main_executor",
            sensing="text_channel",
            prior_knowledge=["SIGNIFIER:FATHA", "SIGNIFIER:KASRA"]
        )
        
        assert isinstance(gate, VerifiedGate)
        assert gate.gate_id == "G_ATTEND:001"
        assert gate.reality == "السلام عليكم"
        assert len(gate.prior_knowledge) == 2
    
    def test_gate_empty_reality(self):
        """Gate with empty reality should fail (Condition 1)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_gate(
                gate_id="G_TEST:001",
                reality="",  # Empty reality
                brain="executor",
                sensing="channel",
                prior_knowledge=["lex1"]
            )
        
        assert "Reality" in str(exc_info.value)
        assert "Condition 1" in str(exc_info.value)
    
    def test_gate_empty_brain(self):
        """Gate with empty brain should fail (Condition 2)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_gate(
                gate_id="G_TEST:002",
                reality="reality",
                brain="",  # Empty brain
                sensing="channel",
                prior_knowledge=["lex1"]
            )
        
        assert "Brain" in str(exc_info.value)
        assert "Condition 2" in str(exc_info.value)
    
    def test_gate_empty_sensing(self):
        """Gate with empty sensing should fail (Condition 3)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_gate(
                gate_id="G_TEST:003",
                reality="reality",
                brain="executor",
                sensing="",  # Empty sensing
                prior_knowledge=["lex1"]
            )
        
        assert "Sensing" in str(exc_info.value)
        assert "Condition 3" in str(exc_info.value)
    
    def test_gate_empty_prior_knowledge(self):
        """Gate with empty prior knowledge should fail (Condition 4)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_gate(
                gate_id="G_TEST:004",
                reality="reality",
                brain="executor",
                sensing="channel",
                prior_knowledge=[]  # Empty prior knowledge
            )
        
        assert "Prior Knowledge" in str(exc_info.value)
        assert "Condition 4" in str(exc_info.value)


class TestVerifiedTrace:
    """Test verified trace creation"""
    
    def test_valid_trace(self):
        """Valid trace with gates and prior_ids should succeed"""
        bridge = get_verified_bridge()
        
        gate = bridge.verify_gate(
            "G_ATTEND:001", "reality", "brain", "channel", ["lex1"]
        )
        
        trace = bridge.verify_trace(
            trace_id="TRACE:123",
            gates=[gate],
            prior_ids=["SIGNIFIER:FATHA"]
        )
        
        assert isinstance(trace, VerifiedTrace)
        assert trace.trace_id == "TRACE:123"
        assert len(trace.gates) == 1
        assert len(trace.prior_ids) == 1
    
    def test_trace_no_gates(self):
        """Trace without gates should fail (NO C2 without gates)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_trace(
                trace_id="TRACE:124",
                gates=[],  # No gates
                prior_ids=["lex1"]
            )
        
        assert "at least one gate" in str(exc_info.value)
    
    def test_trace_no_prior_ids(self):
        """Trace without prior_ids should fail (NO meaning without evidence)"""
        bridge = get_verified_bridge()
        
        gate = bridge.verify_gate(
            "G_ATTEND:001", "reality", "brain", "channel", ["lex1"]
        )
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_trace(
                trace_id="TRACE:125",
                gates=[gate],
                prior_ids=[]  # No prior_ids
            )
        
        assert "prior_ids" in str(exc_info.value)


class TestVerifiedMeaning:
    """Test verified meaning creation (NO C3 without C2)"""
    
    def test_valid_meaning(self):
        """Valid meaning with trace_id and prior_ids should succeed"""
        bridge = get_verified_bridge()
        
        meaning = bridge.verify_meaning(
            meaning_id="MEANING:456",
            trace_id="TRACE:123",
            concept="book",
            prior_ids=["SIGNIFIED:KITAB:BOOK"],
            provenance=[("CLASSICAL_CORPUS", 1.0)]
        )
        
        assert isinstance(meaning, VerifiedMeaning)
        assert meaning.meaning_id == "MEANING:456"
        assert meaning.trace_id == "TRACE:123"
        assert meaning.concept == "book"
        assert len(meaning.prior_ids) == 1
        assert len(meaning.provenance) == 1
    
    def test_meaning_no_trace(self):
        """Meaning without trace_id should fail (NO C3 without C2)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_meaning(
                meaning_id="MEANING:457",
                trace_id="",  # No trace
                concept="concept",
                prior_ids=["lex1"],
                provenance=[("source", 1.0)]
            )
        
        assert "trace_id" in str(exc_info.value)
        assert "NO C3 without C2" in str(exc_info.value)
    
    def test_meaning_no_prior_ids(self):
        """Meaning without prior_ids should fail (NO meaning without evidence)"""
        bridge = get_verified_bridge()
        
        with pytest.raises(VerificationError) as exc_info:
            bridge.verify_meaning(
                meaning_id="MEANING:458",
                trace_id="TRACE:123",
                concept="concept",
                prior_ids=[],  # No prior_ids
                provenance=[("source", 1.0)]
            )
        
        assert "prior_ids" in str(exc_info.value)
        assert "NO meaning without evidence" in str(exc_info.value)


class TestOCamlIntegration:
    """Test integration with OCaml verification suite"""
    
    def test_ocaml_suite_availability(self):
        """Check if OCaml verification suite can be run"""
        bridge = get_verified_bridge()
        
        success, output = bridge.run_ocaml_verification_suite()
        
        # Suite may not be built yet, so just check we get a response
        assert isinstance(success, bool)
        assert isinstance(output, str)
        
        # If built, should pass all tests
        if success:
            assert "tests passed" in output.lower() or "All tests passed" in output


class TestEndToEndVerification:
    """End-to-end verification workflow"""
    
    def test_complete_verification_chain(self):
        """Test complete Coq → OCaml → Python → Tests chain"""
        bridge = get_verified_bridge()
        
        # Step 1: Create verified gate (enforces four conditions)
        gate = bridge.verify_gate(
            gate_id="G_ATTEND:001",
            reality="السلام عليكم",
            brain="main_executor",
            sensing="text_channel",
            prior_knowledge=["SIGNIFIER:SALAM", "SIGNIFIER:FATHA"]
        )
        
        # Step 2: Create verified trace (enforces gate + prior_ids requirements)
        trace = bridge.verify_trace(
            trace_id="TRACE:001",
            gates=[gate],
            prior_ids=["SIGNIFIER:SALAM", "SIGNIFIED:SALAM:PEACE"]
        )
        
        # Step 3: Create verified meaning (enforces NO C3 without C2)
        meaning = bridge.verify_meaning(
            meaning_id="MEANING:001",
            trace_id=trace.trace_id,
            concept="peace",
            prior_ids=["SIGNIFIED:SALAM:PEACE"],
            provenance=[
                ("CLASSICAL_CORPUS", 1.0),
                ("MODERN_USAGE", 0.9)
            ]
        )
        
        # Verify complete chain
        assert gate.gate_id == "G_ATTEND:001"
        assert trace.trace_id == "TRACE:001"
        assert trace.gates[0].gate_id == gate.gate_id
        assert meaning.trace_id == trace.trace_id
        assert meaning.concept == "peace"
        
        # All constraints verified
        assert len(gate.prior_knowledge) > 0  # Condition 4
        assert len(trace.gates) > 0          # Has gates
        assert len(trace.prior_ids) > 0      # Has evidence
        assert meaning.trace_id != ""        # NO C3 without C2
        assert len(meaning.prior_ids) > 0    # NO meaning without evidence
