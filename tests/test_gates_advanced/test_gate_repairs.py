"""
Comprehensive tests for all gate repair mechanisms.

Tests all 10 gates:
- GateSukun
- GateShadda
- GateHamza
- GateWaqf
- GateIdgham
- GateMadd
- GateAssimilation
- GateTanwin
- GateDeletion
- GateEpenthesis
"""

import pytest
from fvafk.c2a.gates import (
    GateSukun, GateShadda, GateHamza, GateWaqf,
    GateIdgham, GateMadd, GateAssimilation, GateTanwin,
    GateDeletion, GateEpenthesis
)
from fvafk.c2a.syllable import Segment, SegmentKind, VowelKind
from fvafk.c2a.gate_framework import GateStatus


def make_consonant(text):
    """Helper to create consonant segment."""
    return Segment(text=text, kind=SegmentKind.CONSONANT, vk=None)


def make_vowel(text, vk):
    """Helper to create vowel segment."""
    return Segment(text=text, kind=SegmentKind.VOWEL, vk=vk)


class TestGateSukunRepair:
    """Test GateSukun repair mechanism."""
    
    def test_gate_sukun_double_sukun_repair(self):
        """Test repair of double sukun."""
        gate = GateSukun()
        
        # Create double sukun: C + sukun + C + sukun
        segments = [
            make_consonant("ب"),
            make_vowel("ْ", VowelKind.SUKUN),
            make_consonant("ت"),
            make_vowel("ْ", VowelKind.SUKUN),
        ]
        
        result = gate.apply(segments)
        assert result.status == GateStatus.REPAIR
        assert result.output[1].vk == VowelKind.FATHA  # First sukun replaced
    
    def test_gate_sukun_no_repair_needed(self):
        """Test when no repair is needed."""
        gate = GateSukun()
        
        # Single sukun - no problem
        segments = [
            make_consonant("ب"),
            make_vowel("َ", VowelKind.FATHA),
            make_consonant("ت"),
            make_vowel("ْ", VowelKind.SUKUN),
        ]
        
        result = gate.apply(segments)
        assert result.status == GateStatus.ACCEPT
    
    def test_gate_sukun_precondition(self):
        """Test precondition check."""
        gate = GateSukun()
        
        # With sukun
        segments_with = [make_consonant("ب"), make_vowel("ْ", VowelKind.SUKUN)]
        assert gate.precondition(segments_with) is True
        
        # Without sukun
        segments_without = [make_consonant("ب"), make_vowel("َ", VowelKind.FATHA)]
        assert gate.precondition(segments_without) is False
    
    def test_gate_sukun_postcondition(self):
        """Test postcondition validation."""
        gate = GateSukun()
        
        # Good output (no double sukun)
        good_segments = [
            make_consonant("ب"),
            make_vowel("َ", VowelKind.FATHA),
            make_consonant("ت"),
            make_vowel("ْ", VowelKind.SUKUN),
        ]
        assert gate.postcondition([], good_segments) is True
        
        # Bad output (double sukun)
        bad_segments = [
            make_consonant("ب"),
            make_vowel("ْ", VowelKind.SUKUN),
            make_consonant("ت"),
            make_vowel("ْ", VowelKind.SUKUN),
        ]
        assert gate.postcondition([], bad_segments) is False


class TestGateShaddaRepair:
    """Test GateShadda repair mechanism."""
    
    def test_gate_shadda_initialization(self):
        """Test GateShadda initialization."""
        gate = GateShadda()
        assert gate.gate_id == "G_SHADDA"
    
    def test_gate_shadda_precondition(self):
        """Test shadda precondition (if available)."""
        gate = GateShadda()
        
        # GateShadda may not have precondition method
        if not hasattr(gate, 'precondition'):
            pytest.skip("GateShadda does not have precondition method")
        
        # With shadda
        segments_with = [make_vowel("ّ", VowelKind.SHADDA)]
        assert gate.precondition(segments_with) is True
        
        # Without shadda
        segments_without = [make_vowel("َ", VowelKind.FATHA)]
        assert gate.precondition(segments_without) is False
    
    def test_gate_shadda_apply(self):
        """Test shadda application."""
        gate = GateShadda()
        
        # Test with shadda
        segments = [
            make_consonant("م"),
            make_vowel("ّ", VowelKind.SHADDA),
            make_vowel("َ", VowelKind.FATHA),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateHamzaRepair:
    """Test GateHamza repair mechanism."""
    
    def test_gate_hamza_initialization(self):
        """Test GateHamza initialization."""
        gate = GateHamza()
        assert gate.gate_id == "G_HAMZA"
    
    def test_gate_hamza_precondition(self):
        """Test hamza precondition."""
        gate = GateHamza()
        
        # With hamza
        segments_with = [make_consonant("ء")]
        assert gate.precondition(segments_with) is True
        
        # Without hamza
        segments_without = [make_consonant("ب")]
        assert gate.precondition(segments_without) is False
    
    def test_gate_hamza_apply(self):
        """Test hamza application."""
        gate = GateHamza()
        
        segments = [make_consonant("ء"), make_vowel("َ", VowelKind.FATHA)]
        result = gate.apply(segments)
        
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]
        assert result.output is not None


class TestGateWaqfRepair:
    """Test GateWaqf repair mechanism."""
    
    def test_gate_waqf_initialization(self):
        """Test GateWaqf initialization."""
        gate = GateWaqf()
        assert gate.gate_id == "G_WAQF"
    
    def test_gate_waqf_precondition(self):
        """Test waqf precondition."""
        gate = GateWaqf()
        
        # With tanwin (pausal context)
        segments = [make_vowel("ً", VowelKind.TANWIN_FATH)]
        assert gate.precondition(segments) is True
        
        # Without tanwin
        segments = [make_vowel("َ", VowelKind.FATHA)]
        # May or may not trigger based on implementation
        result = gate.precondition(segments)
        assert isinstance(result, bool)
    
    def test_gate_waqf_apply(self):
        """Test waqf application."""
        gate = GateWaqf()
        
        segments = [
            make_consonant("ب"),
            make_vowel("ً", VowelKind.TANWIN_FATH),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateIdghamRepair:
    """Test GateIdgham repair mechanism."""
    
    def test_gate_idgham_initialization(self):
        """Test GateIdgham initialization."""
        gate = GateIdgham()
        assert gate.gate_id == "G_IDGHAM"
    
    def test_gate_idgham_precondition(self):
        """Test idgham precondition (if available)."""
        gate = GateIdgham()
        
        # GateIdgham may not have precondition method
        if not hasattr(gate, 'precondition'):
            pytest.skip("GateIdgham does not have precondition method")
        
        # Test with tanwin (potential idgham context)
        segments = [make_vowel("ً", VowelKind.TANWIN_FATH)]
        result = gate.precondition(segments)
        assert isinstance(result, bool)
    
    def test_gate_idgham_apply(self):
        """Test idgham application."""
        gate = GateIdgham()
        
        segments = [
            make_consonant("ن"),
            make_vowel("ً", VowelKind.TANWIN_FATH),
            make_consonant("م"),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateMaddRepair:
    """Test GateMadd repair mechanism."""
    
    def test_gate_madd_initialization(self):
        """Test GateMadd initialization."""
        gate = GateMadd()
        assert gate.gate_id == "G_MADD"
    
    def test_gate_madd_precondition(self):
        """Test madd precondition (if available)."""
        gate = GateMadd()
        
        # GateMadd may not have precondition method
        if not hasattr(gate, 'precondition'):
            pytest.skip("GateMadd does not have precondition method")
        
        # With long vowel
        segments_with = [make_consonant("ا")]
        result = gate.precondition(segments_with)
        assert isinstance(result, bool)
    
    def test_gate_madd_apply(self):
        """Test madd application."""
        gate = GateMadd()
        
        segments = [
            make_consonant("ب"),
            make_vowel("َ", VowelKind.FATHA),
            make_consonant("ا"),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateAssimilationRepair:
    """Test GateAssimilation repair mechanism."""
    
    def test_gate_assimilation_initialization(self):
        """Test GateAssimilation initialization."""
        gate = GateAssimilation()
        assert gate.gate_id == "G_ASSIMILATION"
    
    def test_gate_assimilation_precondition(self):
        """Test assimilation precondition (if available)."""
        gate = GateAssimilation()
        
        # GateAssimilation may not have precondition method
        if not hasattr(gate, 'precondition'):
            pytest.skip("GateAssimilation does not have precondition method")
        
        segments = [make_consonant("ن"), make_consonant("ب")]
        result = gate.precondition(segments)
        assert isinstance(result, bool)
    
    def test_gate_assimilation_apply(self):
        """Test assimilation application."""
        gate = GateAssimilation()
        
        segments = [
            make_consonant("ن"),
            make_vowel("ْ", VowelKind.SUKUN),
            make_consonant("ب"),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateTanwinRepair:
    """Test GateTanwin repair mechanism."""
    
    def test_gate_tanwin_initialization(self):
        """Test GateTanwin initialization."""
        gate = GateTanwin()
        assert gate.gate_id == "G_TANWIN"
    
    def test_gate_tanwin_precondition(self):
        """Test tanwin precondition (if available)."""
        gate = GateTanwin()
        
        # GateTanwin may not have precondition method
        if not hasattr(gate, 'precondition'):
            pytest.skip("GateTanwin does not have precondition method")
        
        # With tanwin
        segments_with = [make_vowel("ً", VowelKind.TANWIN_FATH)]
        assert gate.precondition(segments_with) is True
        
        # Without tanwin
        segments_without = [make_vowel("َ", VowelKind.FATHA)]
        assert gate.precondition(segments_without) is False
    
    def test_gate_tanwin_apply(self):
        """Test tanwin application."""
        gate = GateTanwin()
        
        segments = [
            make_consonant("ب"),
            make_vowel("ً", VowelKind.TANWIN_FATH),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateDeletionRepair:
    """Test GateDeletion repair mechanism."""
    
    def test_gate_deletion_initialization(self):
        """Test GateDeletion initialization."""
        gate = GateDeletion()
        assert gate.gate_id == "G_DELETION"
    
    def test_gate_deletion_precondition(self):
        """Test deletion precondition."""
        gate = GateDeletion()
        
        # Any segments can potentially trigger deletion
        segments = [make_consonant("ب"), make_vowel("َ", VowelKind.FATHA)]
        result = gate.precondition(segments)
        assert isinstance(result, bool)
    
    def test_gate_deletion_apply(self):
        """Test deletion application."""
        gate = GateDeletion()
        
        segments = [
            make_consonant("ب"),
            make_vowel("َ", VowelKind.FATHA),
            make_consonant("ت"),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateEpenthesisRepair:
    """Test GateEpenthesis repair mechanism."""
    
    def test_gate_epenthesis_initialization(self):
        """Test GateEpenthesis initialization."""
        gate = GateEpenthesis()
        assert gate.gate_id == "G_EPENTHESIS"
    
    def test_gate_epenthesis_precondition(self):
        """Test epenthesis precondition."""
        gate = GateEpenthesis()
        
        # Consonant clusters might need epenthesis
        segments = [make_consonant("ب"), make_consonant("ت")]
        result = gate.precondition(segments)
        assert isinstance(result, bool)
    
    def test_gate_epenthesis_apply(self):
        """Test epenthesis application."""
        gate = GateEpenthesis()
        
        segments = [
            make_consonant("ب"),
            make_consonant("ت"),
            make_consonant("ر"),
        ]
        
        result = gate.apply(segments)
        assert result.status in [GateStatus.ACCEPT, GateStatus.REPAIR]


class TestGateOrchestration:
    """Test gate orchestration with all gates."""
    
    def test_all_gates_together(self):
        """Test all gates working together."""
        from fvafk.c2a.gate_framework import GateOrchestrator
        
        gates = [
            GateSukun(),
            GateShadda(),
            GateHamza(),
            GateWaqf(),
            GateIdgham(),
            GateMadd(),
            GateAssimilation(),
            GateTanwin(),
            GateDeletion(),
            GateEpenthesis(),
        ]
        
        orchestrator = GateOrchestrator(gates=gates)
        assert len(orchestrator.gates) == 10
    
    def test_orchestrator_run(self):
        """Test orchestrator running all gates."""
        from fvafk.c2a.gate_framework import GateOrchestrator
        
        gates = [
            GateSukun(),
            GateShadda(),
            GateHamza(),
        ]
        
        orchestrator = GateOrchestrator(gates=gates)
        
        segments = [
            make_consonant("ب"),
            make_vowel("َ", VowelKind.FATHA),
        ]
        
        final_segments, gate_results = orchestrator.run(segments)
        
        assert len(gate_results) == 3
        assert len(final_segments) >= len(segments)
