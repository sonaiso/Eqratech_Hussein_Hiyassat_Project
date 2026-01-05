"""
Tests for Graph and Invariants (Phase 4)

Tests complete graph implementation and invariant checking:
- SignifierGraph (C1) tests
- SignifiedGraph (C3) tests  
- Conservation laws tests
- Symmetry rules tests
- Linguistic invariants tests
"""

import pytest
from fractalhub.kernel.graph import (
    SignifierGraph, SignifierNodeType, SignifierEdgeType,
    SignifiedGraph, SignifiedNodeType, SignifiedEdgeType
)
from fractalhub.kernel.invariants import (
    ConservationRule, ConservationType, ConservationChecker,
    SymmetryRule, SymmetryType, SymmetryChecker,
    InvariantManager, LinguisticInvariants
)


# ============================================================================
# SIGNIFIER GRAPH TESTS
# ============================================================================

class TestSignifierGraph:
    """Tests for SignifierGraph (C1 layer)"""
    
    def test_create_empty_graph(self):
        """Test creating empty signifier graph"""
        graph = SignifierGraph()
        assert len(graph.nodes) == 0
        assert len(graph.edges) == 0
    
    def test_add_phoneme_node(self):
        """Test adding phoneme node"""
        graph = SignifierGraph()
        node = graph.add_node(
            "U:PHONEME:001",
            SignifierNodeType.PHONEME,
            "ك",
            {"voiced": False, "place": "velar"}
        )
        
        assert node.node_id == "U:PHONEME:001"
        assert node.node_type == SignifierNodeType.PHONEME
        assert node.text == "ك"
        assert node.features["voiced"] is False
    
    def test_add_diacritic_node(self):
        """Test adding diacritic node"""
        graph = SignifierGraph()
        node = graph.add_node(
            "U:DIAC:FATHA",
            SignifierNodeType.DIACRITIC,
            "َ",
            {"vowel": "a"}
        )
        
        assert node.node_type == SignifierNodeType.DIACRITIC
        assert node.text == "َ"
    
    def test_add_edge(self):
        """Test adding edge between nodes"""
        graph = SignifierGraph()
        graph.add_node("N1", SignifierNodeType.TOKEN, "ك")
        graph.add_node("N2", SignifierNodeType.TOKEN, "ت")
        
        edge = graph.add_edge(
            "E1",
            SignifierEdgeType.NEXT,
            "N1",
            "N2"
        )
        
        assert edge.edge_id == "E1"
        assert edge.edge_type == SignifierEdgeType.NEXT
        assert edge.src == "N1"
        assert edge.dst == "N2"
    
    def test_get_neighbors(self):
        """Test getting neighbor nodes"""
        graph = SignifierGraph()
        graph.add_node("N1", SignifierNodeType.TOKEN, "ك")
        graph.add_node("N2", SignifierNodeType.TOKEN, "ت")
        graph.add_node("N3", SignifierNodeType.TOKEN, "ب")
        
        graph.add_edge("E1", SignifierEdgeType.NEXT, "N1", "N2")
        graph.add_edge("E2", SignifierEdgeType.NEXT, "N2", "N3")
        
        neighbors = graph.get_neighbors("N1")
        assert "N2" in neighbors
        assert "N3" not in neighbors
    
    def test_find_path(self):
        """Test finding path between nodes"""
        graph = SignifierGraph()
        graph.add_node("N1", SignifierNodeType.TOKEN, "ك")
        graph.add_node("N2", SignifierNodeType.TOKEN, "ت")
        graph.add_node("N3", SignifierNodeType.TOKEN, "ب")
        
        graph.add_edge("E1", SignifierEdgeType.NEXT, "N1", "N2")
        graph.add_edge("E2", SignifierEdgeType.NEXT, "N2", "N3")
        
        path = graph.find_path("N1", "N3")
        assert path == ["N1", "N2", "N3"]
    
    def test_to_dict(self):
        """Test serialization to dict"""
        graph = SignifierGraph()
        graph.add_node("N1", SignifierNodeType.TOKEN, "ك", {"test": True})
        graph.add_edge("E1", SignifierEdgeType.NEXT, "N1", "N1")
        
        data = graph.to_dict()
        assert 'nodes' in data
        assert 'edges' in data
        assert len(data['nodes']) == 1
        assert len(data['edges']) == 1


# ============================================================================
# SIGNIFIED GRAPH TESTS
# ============================================================================

class TestSignifiedGraph:
    """Tests for SignifiedGraph (C3 layer)"""
    
    def test_create_empty_graph(self):
        """Test creating empty signified graph"""
        graph = SignifiedGraph()
        assert len(graph.nodes) == 0
        assert len(graph.edges) == 0
        assert len(graph.provenance) == 0
    
    def test_add_entity_node(self):
        """Test adding entity node with provenance"""
        graph = SignifiedGraph()
        node = graph.add_node(
            "ENT:001",
            SignifiedNodeType.ENTITY,
            {"name": "الطالب", "type": "person"},
            generated_by="G:EXTRACT_ENTITY"
        )
        
        assert node.node_id == "ENT:001"
        assert node.node_type == SignifiedNodeType.ENTITY
        assert graph.get_provenance("ENT:001") == "G:EXTRACT_ENTITY"
    
    def test_add_event_node(self):
        """Test adding event node"""
        graph = SignifiedGraph()
        node = graph.add_node(
            "EVT:001",
            SignifiedNodeType.EVENT,
            {"verb": "كتب", "tense": "past"},
            generated_by="G:EXTRACT_EVENT"
        )
        
        assert node.node_type == SignifiedNodeType.EVENT
        assert node.features["tense"] == "past"
    
    def test_add_semantic_relation(self):
        """Test adding semantic relation edge"""
        graph = SignifiedGraph()
        graph.add_node("ENT:001", SignifiedNodeType.ENTITY, generated_by="G:1")
        graph.add_node("EVT:001", SignifiedNodeType.EVENT, generated_by="G:2")
        
        edge = graph.add_edge(
            "REL:001",
            SignifiedEdgeType.AGENT_OF,
            "ENT:001",
            "EVT:001",
            {"role": "agent"},
            generated_by="G:ROLE_ASSIGN"
        )
        
        assert edge.edge_type == SignifiedEdgeType.AGENT_OF
        assert graph.get_provenance("REL:001") == "G:ROLE_ASSIGN"
    
    def test_get_nodes_by_type(self):
        """Test filtering nodes by type"""
        graph = SignifiedGraph()
        graph.add_node("ENT:001", SignifiedNodeType.ENTITY, generated_by="G:1")
        graph.add_node("ENT:002", SignifiedNodeType.ENTITY, generated_by="G:1")
        graph.add_node("EVT:001", SignifiedNodeType.EVENT, generated_by="G:2")
        
        entities = graph.get_nodes_by_type(SignifiedNodeType.ENTITY)
        assert len(entities) == 2
        
        events = graph.get_nodes_by_type(SignifiedNodeType.EVENT)
        assert len(events) == 1
    
    def test_get_relations(self):
        """Test getting all relations for a node"""
        graph = SignifiedGraph()
        graph.add_node("ENT:001", SignifiedNodeType.ENTITY, generated_by="G:1")
        graph.add_node("EVT:001", SignifiedNodeType.EVENT, generated_by="G:2")
        graph.add_node("EVT:002", SignifiedNodeType.EVENT, generated_by="G:2")
        
        graph.add_edge("REL:001", SignifiedEdgeType.AGENT_OF, "ENT:001", "EVT:001", generated_by="G:3")
        graph.add_edge("REL:002", SignifiedEdgeType.AGENT_OF, "ENT:001", "EVT:002", generated_by="G:3")
        
        relations = graph.get_relations("ENT:001")
        assert len(relations) == 2
        assert all(r['relation'] == 'AGENT_OF' for r in relations)
    
    def test_verify_provenance(self):
        """Test verifying all elements have provenance"""
        graph = SignifiedGraph()
        graph.add_node("ENT:001", SignifiedNodeType.ENTITY, generated_by="G:1")
        graph.add_node("EVT:001", SignifiedNodeType.EVENT, generated_by="G:2")
        graph.add_edge("REL:001", SignifiedEdgeType.AGENT_OF, "ENT:001", "EVT:001", generated_by="G:3")
        
        assert graph.verify_provenance() is True
    
    def test_missing_provenance_fails(self):
        """Test that missing provenance is detected"""
        graph = SignifiedGraph()
        graph.add_node("ENT:001", SignifiedNodeType.ENTITY)  # No generated_by
        
        assert graph.verify_provenance() is False


# ============================================================================
# CONSERVATION TESTS
# ============================================================================

class TestConservation:
    """Tests for conservation laws"""
    
    def test_create_conservation_rule(self):
        """Test creating conservation rule"""
        rule = ConservationRule(
            rule_id="CONS:TEST",
            conservation_type=ConservationType.TEMPORAL,
            description="Test rule",
            property_name="tense"
        )
        
        assert rule.rule_id == "CONS:TEST"
        assert rule.conservation_type == ConservationType.TEMPORAL
    
    def test_conservation_check_passes(self):
        """Test conservation check passes"""
        rule = ConservationRule(
            rule_id="CONS:TEMPORAL",
            conservation_type=ConservationType.TEMPORAL,
            description="Temporal consistency",
            property_name="tense"
        )
        
        before = {"tense": "past", "subject": "الطالب"}
        after = {"tense": "past", "subject": "الطالب", "object": "الدرس"}
        
        assert rule.check(before, after) is True
    
    def test_conservation_check_fails(self):
        """Test conservation check fails"""
        rule = ConservationRule(
            rule_id="CONS:TEMPORAL",
            conservation_type=ConservationType.TEMPORAL,
            description="Temporal consistency",
            property_name="tense"
        )
        
        before = {"tense": "past"}
        after = {"tense": "present"}  # Tense changed!
        
        assert rule.check(before, after) is False
    
    def test_conservation_checker(self):
        """Test conservation checker"""
        checker = ConservationChecker()
        
        before = {"temporal_marker": "past", "referent_id": "ENT:001"}
        after = {"temporal_marker": "past", "referent_id": "ENT:002"}  # Referent changed
        
        violations = checker.check_transformation(before, after, "2026-01-05")
        
        # Temporal should pass, referential should fail
        assert len(violations) > 0
        assert any(v.rule_id == "CONS:REFERENTIAL" for v in violations)
    
    def test_add_custom_conservation_rule(self):
        """Test adding custom conservation rule"""
        checker = ConservationChecker()
        
        custom_rule = ConservationRule(
            rule_id="CONS:CUSTOM",
            conservation_type=ConservationType.QUANTITATIVE,
            description="Custom rule",
            property_name="quantity"
        )
        
        checker.add_rule(custom_rule)
        assert "CONS:CUSTOM" in checker.rules


# ============================================================================
# SYMMETRY TESTS
# ============================================================================

class TestSymmetry:
    """Tests for symmetry rules"""
    
    def test_create_symmetry_rule(self):
        """Test creating symmetry rule"""
        rule = SymmetryRule(
            rule_id="SYM:TEST",
            symmetry_type=SymmetryType.LOGICAL,
            description="Test symmetry",
            left_pattern="P",
            right_pattern="Q"
        )
        
        assert rule.rule_id == "SYM:TEST"
        assert rule.bidirectional is True
    
    def test_symmetry_applies(self):
        """Test checking if symmetry applies"""
        rule = SymmetryRule(
            rule_id="SYM:DOUBLE_NEG",
            symmetry_type=SymmetryType.LOGICAL,
            description="Double negation",
            left_pattern="double_negation",
            right_pattern="positive"
        )
        
        structure = {"pattern": "double_negation"}
        assert rule.applies(structure) is True
    
    def test_symmetry_transform(self):
        """Test applying symmetry transformation"""
        rule = SymmetryRule(
            rule_id="SYM:DOUBLE_NEG",
            symmetry_type=SymmetryType.LOGICAL,
            description="Double negation",
            left_pattern="double_negation",
            right_pattern="positive"
        )
        
        structure = {"pattern": "double_negation", "prop": "P"}
        result = rule.transform(structure)
        
        assert result["pattern"] == "positive"
        assert result["prop"] == "P"
    
    def test_symmetry_checker(self):
        """Test symmetry checker"""
        checker = SymmetryChecker()
        
        structure = {"pattern": "double_negation"}
        applicable = checker.find_applicable_rules(structure)
        
        assert len(applicable) > 0
        assert any(r.rule_id == "SYM:DOUBLE_NEG" for r in applicable)
    
    def test_apply_symmetry(self):
        """Test applying specific symmetry"""
        checker = SymmetryChecker()
        
        structure = {"pattern": "double_negation", "value": "test"}
        result = checker.apply_symmetry(structure, "SYM:DOUBLE_NEG")
        
        assert result is not None
        assert result["pattern"] == "positive"


# ============================================================================
# INVARIANT MANAGER TESTS
# ============================================================================

class TestInvariantManager:
    """Tests for invariant manager"""
    
    def test_create_manager(self):
        """Test creating invariant manager"""
        manager = InvariantManager()
        assert manager.conservation is not None
        assert manager.symmetry is not None
    
    def test_check_valid_transformation(self):
        """Test checking valid transformation"""
        manager = InvariantManager()
        
        before = {"temporal_marker": "past", "referent_id": "ENT:001", "predicate_structure": "simple"}
        after = {"temporal_marker": "past", "referent_id": "ENT:001", "predicate_structure": "simple", "object": "new"}
        
        result = manager.check_transformation(before, after)
        
        assert result.passed is True
        assert len(result.violations) == 0
    
    def test_check_invalid_transformation(self):
        """Test checking invalid transformation"""
        manager = InvariantManager()
        
        before = {"temporal_marker": "past"}
        after = {"temporal_marker": "future"}  # Temporal violation
        
        result = manager.check_transformation(before, after)
        
        assert result.passed is False
        assert len(result.violations) > 0
    
    def test_add_custom_rules(self):
        """Test adding custom conservation and symmetry rules"""
        manager = InvariantManager()
        
        cons_rule = ConservationRule(
            rule_id="CONS:CUSTOM",
            conservation_type=ConservationType.SCOPE,
            description="Custom conservation",
            property_name="scope_level"
        )
        
        sym_rule = SymmetryRule(
            rule_id="SYM:CUSTOM",
            symmetry_type=SymmetryType.STRUCTURAL,
            description="Custom symmetry",
            left_pattern="A",
            right_pattern="B"
        )
        
        manager.add_conservation_rule(cons_rule)
        manager.add_symmetry_rule(sym_rule)
        
        assert "CONS:CUSTOM" in manager.conservation.rules
        assert "SYM:CUSTOM" in manager.symmetry.rules
    
    def test_clear_violations(self):
        """Test clearing violation history"""
        manager = InvariantManager()
        
        before = {"temporal_marker": "past"}
        after = {"temporal_marker": "future"}
        
        manager.check_transformation(before, after)
        assert len(manager.get_all_violations()) > 0
        
        manager.clear_violations()
        assert len(manager.get_all_violations()) == 0


# ============================================================================
# LINGUISTIC INVARIANTS TESTS
# ============================================================================

class TestLinguisticInvariants:
    """Tests for Arabic linguistic invariants"""
    
    def test_agreement_valid(self):
        """Test valid gender/number agreement"""
        structure = {
            "subject": {"gender": "masculine", "number": "singular"},
            "predicate": {"gender": "masculine", "number": "singular"}
        }
        
        assert LinguisticInvariants.check_agreement(structure) is True
    
    def test_agreement_invalid(self):
        """Test invalid gender agreement"""
        structure = {
            "subject": {"gender": "masculine", "number": "singular"},
            "predicate": {"gender": "feminine", "number": "singular"}
        }
        
        assert LinguisticInvariants.check_agreement(structure) is False
    
    def test_scope_consistency_valid(self):
        """Test valid scope nesting"""
        structure = {
            "scopes": [
                {"start": 0, "end": 10, "type": "quantifier"},
                {"start": 2, "end": 8, "type": "negation"}
            ]
        }
        
        assert LinguisticInvariants.check_scope_consistency(structure) is True
    
    def test_scope_consistency_invalid(self):
        """Test invalid scope nesting"""
        structure = {
            "scopes": [
                {"start": 0, "end": 8, "type": "quantifier"},
                {"start": 2, "end": 10, "type": "negation"}  # Improper nesting
            ]
        }
        
        assert LinguisticInvariants.check_scope_consistency(structure) is False


# ============================================================================
# INTEGRATION TESTS
# ============================================================================

class TestGraphInvariantsIntegration:
    """Integration tests for graphs with invariants"""
    
    def test_signified_graph_with_invariants(self):
        """Test signified graph with invariant checking"""
        graph = SignifiedGraph()
        manager = InvariantManager()
        
        # Add entity
        graph.add_node(
            "ENT:STUDENT",
            SignifiedNodeType.ENTITY,
            {
                "name": "الطالب", 
                "temporal_marker": "past",
                "referent_id": "ENT:STUDENT",
                "predicate_structure": "simple"
            },
            generated_by="G:EXTRACT"
        )
        
        # Add event
        graph.add_node(
            "EVT:WRITE",
            SignifiedNodeType.EVENT,
            {
                "verb": "كتب", 
                "temporal_marker": "past",
                "referent_id": "ENT:STUDENT",  # Same referent
                "predicate_structure": "simple"  # Same structure
            },
            generated_by="G:EXTRACT"
        )
        
        # Check invariants hold
        entity = graph.nodes["ENT:STUDENT"].features
        event = graph.nodes["EVT:WRITE"].features
        
        result = manager.check_transformation(entity, event)
        assert result.passed is True  # All properties conserved
    
    def test_complete_example(self):
        """Test complete example: كتب الطالب الدرس"""
        # Create signifier graph (C1)
        sig_graph = SignifierGraph()
        sig_graph.add_node("T1", SignifierNodeType.TOKEN, "كتب")
        sig_graph.add_node("T2", SignifierNodeType.TOKEN, "الطالب")
        sig_graph.add_node("T3", SignifierNodeType.TOKEN, "الدرس")
        
        sig_graph.add_edge("E1", SignifierEdgeType.NEXT, "T1", "T2")
        sig_graph.add_edge("E2", SignifierEdgeType.NEXT, "T2", "T3")
        
        # Create signified graph (C3)
        sig2_graph = SignifiedGraph()
        sig2_graph.add_node("EVT:WRITE", SignifiedNodeType.EVENT, 
                           {"verb": "كتب", "tense": "past"}, "G:EXTRACT")
        sig2_graph.add_node("ENT:STUDENT", SignifiedNodeType.ENTITY,
                           {"name": "الطالب"}, "G:EXTRACT")
        sig2_graph.add_node("ENT:LESSON", SignifiedNodeType.ENTITY,
                           {"name": "الدرس"}, "G:EXTRACT")
        
        sig2_graph.add_edge("R1", SignifiedEdgeType.AGENT_OF, 
                           "ENT:STUDENT", "EVT:WRITE", generated_by="G:ROLE")
        sig2_graph.add_edge("R2", SignifiedEdgeType.PATIENT_OF,
                           "ENT:LESSON", "EVT:WRITE", generated_by="G:ROLE")
        
        # Verify structure
        assert len(sig_graph.nodes) == 3
        assert len(sig2_graph.nodes) == 3
        assert sig2_graph.verify_provenance() is True
        
        # Check relations
        student_relations = sig2_graph.get_relations("ENT:STUDENT")
        assert len(student_relations) == 1
        assert student_relations[0]['relation'] == 'AGENT_OF'


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
