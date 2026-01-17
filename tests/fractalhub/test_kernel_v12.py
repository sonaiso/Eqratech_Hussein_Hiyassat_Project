"""
Tests for Consciousness Kernel v1.2

Tests:
- Record version metadata
- TraceEntry enhanced schema
- TraceManager validation
- Executor gate execution with evidence
- Entity provenance tracking
- Reasoner evidence requirements
"""

import pytest
from fractalhub.kernel import Record, TraceEntry, TraceManager, Executor, Entity, Reasoner


class TestRecord:
    """Test Record with version metadata."""
    
    def test_record_creation(self):
        """Test basic record creation."""
        record = Record(
            record_id="TEST_001",
            record_type="test",
            data={"key": "value"}
        )
        
        assert record.record_id == "TEST_001"
        assert record.record_type == "test"
        assert record.kernel_version == "1.2"
        assert record.architecture_version == "locked_v1"
        assert record.created_at_iso is not None
        assert "T" in record.created_at_iso  # ISO 8601 format
    
    def test_record_to_dict(self):
        """Test record serialization."""
        record = Record(
            record_id="TEST_002",
            record_type="test"
        )
        
        result = record.to_dict()
        
        assert result["record_id"] == "TEST_002"
        assert result["kernel_version"] == "1.2"
        assert result["architecture_version"] == "locked_v1"
        assert "created_at_iso" in result


class TestTraceEntry:
    """Test TraceEntry with v1.2 enhancements."""
    
    def test_trace_entry_creation(self):
        """Test basic trace entry creation."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            outputs=["OUTPUT_1"],
            prior_ids=["PRIOR_1"],
        )
        
        assert trace.gate_id == "G_TEST"
        assert trace.inputs == ["INPUT_1"]
        assert trace.outputs == ["OUTPUT_1"]
        assert trace.prior_ids == ["PRIOR_1"]
        assert trace.kernel_version == "1.2"
    
    def test_trace_four_conditions(self):
        """Test four conditions verification."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=["PRIOR_1"],
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        assert trace.is_valid()
        assert trace.four_conditions_verified["reality"]
        assert trace.four_conditions_verified["prior"]
    
    def test_trace_invalid_without_conditions(self):
        """Test trace is invalid without four conditions."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=["PRIOR_1"],
            four_conditions_verified={
                "reality": False,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        assert not trace.is_valid()
    
    def test_trace_invalid_without_evidence(self):
        """Test trace is invalid without evidence (prior_ids)."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=[],  # No evidence
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        assert not trace.is_valid()
    
    def test_trace_latency_tracking(self):
        """Test gate latency tracking."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=["PRIOR_1"],
            gate_latency_ms=42.5,
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        assert trace.gate_latency_ms == 42.5
    
    def test_trace_evidence_strength(self):
        """Test epistemic evidence strength."""
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=["PRIOR_1"],
            evidence_strength=0.7,  # ZANN
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        assert trace.evidence_strength == 0.7


class TestTraceManager:
    """Test TraceManager."""
    
    def test_trace_manager_creation(self):
        """Test trace manager creation."""
        manager = TraceManager()
        
        assert len(manager.traces) == 0
        assert len(manager.trace_index) == 0
    
    def test_add_valid_trace(self):
        """Test adding valid trace."""
        manager = TraceManager()
        
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            outputs=["OUTPUT_1"],
            prior_ids=["PRIOR_1"],
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        trace_id = manager.add_trace(trace)
        
        assert trace_id is not None
        assert len(manager.traces) == 1
        assert manager.get_trace(trace_id) == trace
    
    def test_reject_invalid_trace(self):
        """Test rejecting invalid trace."""
        manager = TraceManager()
        
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=[],  # No evidence - invalid
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        
        with pytest.raises(ValueError, match="Invalid trace"):
            manager.add_trace(trace)
    
    def test_verify_no_hallucination(self):
        """Test architecture lock verification."""
        manager = TraceManager()
        
        # Add valid traces
        for i in range(3):
            trace = TraceEntry(
                gate_id=f"G_TEST_{i}",
                inputs=[f"INPUT_{i}"],
                prior_ids=[f"PRIOR_{i}"],
                four_conditions_verified={
                    "reality": True,
                    "brain": True,
                    "sensing": True,
                    "prior": True,
                }
            )
            manager.add_trace(trace)
        
        assert manager.verify_no_hallucination()
    
    def test_get_statistics(self):
        """Test trace statistics."""
        manager = TraceManager()
        
        trace = TraceEntry(
            gate_id="G_TEST",
            inputs=["INPUT_1"],
            prior_ids=["PRIOR_1"],
            gate_latency_ms=10.0,
            evidence_strength=1.0,
            four_conditions_verified={
                "reality": True,
                "brain": True,
                "sensing": True,
                "prior": True,
            }
        )
        manager.add_trace(trace)
        
        stats = manager.get_statistics()
        
        assert stats["total_traces"] == 1
        assert stats["valid_traces"] == 1
        assert stats["avg_latency_ms"] == 10.0
        assert stats["avg_evidence_strength"] == 1.0
        assert stats["architecture_locked"]


class TestExecutor:
    """Test Executor gate execution."""
    
    def test_executor_creation(self):
        """Test executor creation."""
        executor = Executor()
        
        assert executor.dictionary is not None
        assert executor.trace_manager is not None
    
    def test_execute_gate_basic(self):
        """Test basic gate execution."""
        dictionary = {
            "gates": {
                "G_TEST": {
                    "gate_id": "G_TEST",
                    "status": "active",
                    "inputs": ["input"],
                    "outputs": ["output"],
                    "ruleset_ids": ["RULESET_1"],
                    "evidence_required": True,
                }
            }
        }
        
        executor = Executor(dictionary=dictionary)
        
        result = executor.execute_gate(
            gate_id="G_TEST",
            inputs=["INPUT_1"]
        )
        
        assert "outputs" in result
        assert "trace_id" in result
        assert "gate_latency_ms" in result
        assert result["trace_id"].startswith("TRACE:")
    
    def test_execute_gate_missing(self):
        """Test execution of missing gate."""
        executor = Executor(dictionary={"gates": {}})
        
        with pytest.raises(ValueError, match="Gate not found"):
            executor.execute_gate(gate_id="G_MISSING", inputs=["INPUT_1"])
    
    def test_execute_gate_without_evidence(self):
        """Test execution fails without evidence."""
        dictionary = {
            "gates": {
                "G_TEST": {
                    "gate_id": "G_TEST",
                    "status": "active",
                    "inputs": ["input"],
                    "outputs": ["output"],
                    "ruleset_ids": [],  # No evidence
                    "evidence_required": True,
                }
            }
        }
        
        executor = Executor(dictionary=dictionary)
        
        with pytest.raises(ValueError, match="requires evidence"):
            executor.execute_gate(gate_id="G_TEST", inputs=["INPUT_1"])


class TestEntity:
    """Test Entity with provenance."""
    
    def test_entity_creation(self):
        """Test basic entity creation."""
        entity = Entity(
            entity_id="E_001",
            signifier_link="U:DIACRITIC:FATHA",
            meaning={"semantic": "short_a_vowel"},
            provenance={
                "source_type": "grammar_book",
                "confidence": "yaqin",
                "attestation_count": 100,
            },
            created_by_trace_id="TRACE_123"
        )
        
        assert entity.entity_id == "E_001"
        assert entity.signifier_link == "U:DIACRITIC:FATHA"
        assert entity.get_confidence() == 1.0  # yaqin
        assert entity.has_corpus_attestation()
    
    def test_entity_requires_signifier(self):
        """Test entity requires signifier link."""
        with pytest.raises(ValueError, match="no signifier_link"):
            Entity(
                entity_id="E_BAD",
                signifier_link="",  # Empty!
                meaning={"semantic": "test"},
                created_by_trace_id="TRACE_123"
            )
    
    def test_entity_requires_trace(self):
        """Test entity requires trace pointer."""
        with pytest.raises(ValueError, match="no trace pointer"):
            Entity(
                entity_id="E_BAD",
                signifier_link="U:TEST",
                meaning={"semantic": "test"},
                created_by_trace_id=None  # Missing!
            )
    
    def test_entity_confidence_levels(self):
        """Test epistemic confidence levels."""
        # YAQIN
        entity_yaqin = Entity(
            entity_id="E_Y",
            signifier_link="U:TEST",
            meaning={},
            provenance={"confidence": "yaqin"},
            created_by_trace_id="TRACE_1"
        )
        assert entity_yaqin.get_confidence() == 1.0
        
        # ZANN
        entity_zann = Entity(
            entity_id="E_Z",
            signifier_link="U:TEST",
            meaning={},
            provenance={"confidence": "zann"},
            created_by_trace_id="TRACE_2"
        )
        assert entity_zann.get_confidence() == 0.7
        
        # SHAKK
        entity_shakk = Entity(
            entity_id="E_S",
            signifier_link="U:TEST",
            meaning={},
            provenance={"confidence": "shakk"},
            created_by_trace_id="TRACE_3"
        )
        assert entity_shakk.get_confidence() == 0.4


class TestReasoner:
    """Test Reasoner with evidence requirements."""
    
    def test_reasoner_creation(self):
        """Test reasoner creation."""
        reasoner = Reasoner()
        
        assert reasoner.trace_manager is not None
    
    def test_reason_with_evidence(self):
        """Test reasoning with evidence."""
        reasoner = Reasoner()
        
        premises = [
            {
                "id": "P1",
                "content": "All humans are mortal",
                "prior_ids": ["AXIOM_1"]
            },
            {
                "id": "P2",
                "content": "Socrates is human",
                "prior_ids": ["FACT_1"]
            }
        ]
        
        result = reasoner.reason(premises, mode="deductive")
        
        assert "conclusion" in result
        assert "evidence_chain" in result
        assert "epistemic_strength" in result
        assert "trace_id" in result
        assert result["reasoning_mode"] == "deductive"
        assert result["epistemic_strength"] == 1.0  # Deductive certainty
    
    def test_reason_without_premises(self):
        """Test reasoning fails without premises."""
        reasoner = Reasoner()
        
        with pytest.raises(ValueError, match="Cannot reason without premises"):
            reasoner.reason([], mode="deductive")
    
    def test_reason_without_evidence(self):
        """Test reasoning fails without evidence."""
        reasoner = Reasoner()
        
        premises = [
            {
                "id": "P1",
                "content": "Test",
                "prior_ids": []  # No evidence!
            }
        ]
        
        with pytest.raises(ValueError, match="Cannot reason without evidence"):
            reasoner.reason(premises, mode="deductive")
    
    def test_reason_invalid_mode(self):
        """Test reasoning fails with invalid mode."""
        reasoner = Reasoner()
        
        premises = [
            {"id": "P1", "prior_ids": ["PRIOR_1"]}
        ]
        
        with pytest.raises(ValueError, match="Invalid reasoning mode"):
            reasoner.reason(premises, mode="invalid_mode")
    
    def test_reason_epistemic_strength(self):
        """Test epistemic strength by mode."""
        reasoner = Reasoner()
        
        premises = [{"id": "P1", "prior_ids": ["PRIOR_1"]}]
        
        # Deductive: certainty
        result_ded = reasoner.reason(premises, mode="deductive")
        assert result_ded["epistemic_strength"] == 1.0
        
        # Inductive: probability
        result_ind = reasoner.reason(premises, mode="inductive")
        assert result_ind["epistemic_strength"] == 0.7
        
        # Abductive: probability
        result_abd = reasoner.reason(premises, mode="abductive")
        assert result_abd["epistemic_strength"] == 0.7
        
        # Inferential: doubt
        result_inf = reasoner.reason(premises, mode="inferential")
        assert result_inf["epistemic_strength"] == 0.4
