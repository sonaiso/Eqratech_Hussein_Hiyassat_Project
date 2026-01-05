"""
Graph: Signifier and Signified graphs

Two separate graph structures:
- SignifierGraph (C1): Form/phonemes/diacritics/boundaries
- SignifiedGraph (C3): Entities/events/roles/relations

Strict separation maintained - linked only via C2 gates.
"""

from typing import List, Dict, Any, Optional
from dataclasses import dataclass, field
from enum import Enum


# ============================================================================
# SIGNIFIER GRAPH (C1)
# ============================================================================

class SignifierNodeType(Enum):
    """Node types in signifier graph"""
    PHONEME = "phoneme"
    DIACRITIC = "diacritic"
    TOKEN = "token"
    BOUNDARY = "boundary"


class SignifierEdgeType(Enum):
    """Edge types in signifier graph"""
    NEXT = "NEXT"
    PREV = "PREV"
    ATTACH_DIAC = "ATTACH_DIAC"
    MORPH_SEG = "MORPH_SEG"
    WORD_BOUND = "WORD_BOUND"


@dataclass
class SignifierNode:
    """Node in signifier graph"""
    node_id: str
    node_type: SignifierNodeType
    text: str
    features: Dict[str, Any] = field(default_factory=dict)


@dataclass
class SignifierEdge:
    """Edge in signifier graph"""
    edge_id: str
    edge_type: SignifierEdgeType
    src: str  # source node_id
    dst: str  # destination node_id


class SignifierGraph:
    """
    Signifier Graph (الدال).
    
    Represents FORM only:
    - Phonemes, diacritics, tokens, boundaries
    - Sequential relationships
    - Morphological segmentation
    
    FORBIDDEN:
    - No semantic roles (agent/patient/cause...)
    - No meaning (literal/metaphor...)
    - These are generated in C3 via C2 gates
    """
    
    def __init__(self):
        """Initialize empty graph"""
        self.nodes: Dict[str, SignifierNode] = {}
        self.edges: Dict[str, SignifierEdge] = {}
    
    def add_node(self, node_id: str, node_type: SignifierNodeType, 
                 text: str, features: Dict[str, Any] = None) -> SignifierNode:
        """
        Add node to graph.
        
        Args:
            node_id: Unique node ID
            node_type: Type of node
            text: Text content
            features: Optional features
            
        Returns:
            Created node
        """
        node = SignifierNode(
            node_id=node_id,
            node_type=node_type,
            text=text,
            features=features or {}
        )
        self.nodes[node_id] = node
        return node
    
    def add_edge(self, edge_id: str, edge_type: SignifierEdgeType,
                 src: str, dst: str) -> SignifierEdge:
        """
        Add edge to graph.
        
        Args:
            edge_id: Unique edge ID
            edge_type: Type of edge
            src: Source node ID
            dst: Destination node ID
            
        Returns:
            Created edge
        """
        edge = SignifierEdge(
            edge_id=edge_id,
            edge_type=edge_type,
            src=src,
            dst=dst
        )
        self.edges[edge_id] = edge
        return edge
    
    def get_neighbors(self, node_id: str, edge_type: SignifierEdgeType = None) -> List[str]:
        """
        Get neighbor nodes.
        
        Args:
            node_id: Node to get neighbors for
            edge_type: Optional edge type filter
            
        Returns:
            List of neighbor node IDs
        """
        neighbors = []
        for edge in self.edges.values():
            if edge.src == node_id:
                if edge_type is None or edge.edge_type == edge_type:
                    neighbors.append(edge.dst)
        return neighbors
    
    def find_path(self, start: str, end: str) -> Optional[List[str]]:
        """
        Find path between two nodes.
        
        Args:
            start: Start node ID
            end: End node ID
            
        Returns:
            List of node IDs forming path, or None if no path
        """
        if start not in self.nodes or end not in self.nodes:
            return None
        
        # BFS
        from collections import deque
        queue = deque([(start, [start])])
        visited = {start}
        
        while queue:
            node, path = queue.popleft()
            
            if node == end:
                return path
            
            for neighbor in self.get_neighbors(node):
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        
        return None
    
    def to_dict(self) -> dict:
        """Serialize to dictionary"""
        return {
            'nodes': [
                {
                    'id': n.node_id,
                    'type': n.node_type.value,
                    'text': n.text,
                    'features': n.features
                }
                for n in self.nodes.values()
            ],
            'edges': [
                {
                    'id': e.edge_id,
                    'type': e.edge_type.value,
                    'src': e.src,
                    'dst': e.dst
                }
                for e in self.edges.values()
            ]
        }


# ============================================================================
# SIGNIFIED GRAPH (C3)
# ============================================================================

class SignifiedNodeType(Enum):
    """Node types in signified graph"""
    ENTITY = "Entity"
    EVENT = "Event"
    ROLE = "Role"
    TIME = "Time"
    SCOPE = "Scope"
    CASE = "Case"
    SPEECH_ACT = "SpeechAct"
    VALUE_STATE = "ValueState"
    SELF_STATE = "SelfState"


class SignifiedEdgeType(Enum):
    """Edge types in signified graph"""
    REFERS_TO = "REFERS_TO"
    AGENT_OF = "AGENT_OF"
    PATIENT_OF = "PATIENT_OF"
    CAUSES = "CAUSES"
    IMPLIES = "IMPLIES"
    RESTRICTS = "RESTRICTS"
    INCLUDES = "INCLUDES"
    PREDICATES = "PREDICATES"
    TEMPORAL = "TEMPORAL"


@dataclass
class SignifiedNode:
    """Node in signified graph"""
    node_id: str
    node_type: SignifiedNodeType
    features: Dict[str, Any] = field(default_factory=dict)


@dataclass
class SignifiedEdge:
    """Edge in signified graph"""
    edge_id: str
    edge_type: SignifiedEdgeType
    src: str
    dst: str
    properties: Dict[str, Any] = field(default_factory=dict)


class SignifiedGraph:
    """
    Signified Graph (المدلول).
    
    Represents MEANING:
    - Entities, events, roles
    - Semantic relations
    - Time, scope, case
    - Speech acts, values, self-state
    
    All nodes/edges must be generated via C2 gates with evidence.
    """
    
    def __init__(self):
        """Initialize empty graph"""
        self.nodes: Dict[str, SignifiedNode] = {}
        self.edges: Dict[str, SignifiedEdge] = {}
        
        # Track which C2 gate generated each element
        self.provenance: Dict[str, str] = {}  # element_id -> gate_id
    
    def add_node(self, node_id: str, node_type: SignifiedNodeType,
                 features: Dict[str, Any] = None,
                 generated_by: str = None) -> SignifiedNode:
        """
        Add node to graph.
        
        Args:
            node_id: Unique node ID
            node_type: Type of node
            features: Node features
            generated_by: Gate ID that generated this node
            
        Returns:
            Created node
        """
        node = SignifiedNode(
            node_id=node_id,
            node_type=node_type,
            features=features or {}
        )
        self.nodes[node_id] = node
        
        if generated_by:
            self.provenance[node_id] = generated_by
        
        return node
    
    def add_edge(self, edge_id: str, edge_type: SignifiedEdgeType,
                 src: str, dst: str, properties: Dict[str, Any] = None,
                 generated_by: str = None) -> SignifiedEdge:
        """
        Add edge to graph.
        
        Args:
            edge_id: Unique edge ID
            edge_type: Type of edge
            src: Source node ID
            dst: Destination node ID
            properties: Edge properties
            generated_by: Gate ID that generated this edge
            
        Returns:
            Created edge
        """
        edge = SignifiedEdge(
            edge_id=edge_id,
            edge_type=edge_type,
            src=src,
            dst=dst,
            properties=properties or {}
        )
        self.edges[edge_id] = edge
        
        if generated_by:
            self.provenance[edge_id] = generated_by
        
        return edge
    
    def get_provenance(self, element_id: str) -> Optional[str]:
        """
        Get gate that generated an element.
        
        Args:
            element_id: Node or edge ID
            
        Returns:
            Gate ID or None
        """
        return self.provenance.get(element_id)
    
    def get_nodes_by_type(self, node_type: SignifiedNodeType) -> List[SignifiedNode]:
        """
        Get all nodes of a specific type.
        
        Args:
            node_type: Type to filter by
            
        Returns:
            List of matching nodes
        """
        return [n for n in self.nodes.values() if n.node_type == node_type]
    
    def get_edges_by_type(self, edge_type: SignifiedEdgeType) -> List[SignifiedEdge]:
        """
        Get all edges of a specific type.
        
        Args:
            edge_type: Type to filter by
            
        Returns:
            List of matching edges
        """
        return [e for e in self.edges.values() if e.edge_type == edge_type]
    
    def get_relations(self, node_id: str, relation_type: SignifiedEdgeType = None) -> List[Dict[str, Any]]:
        """
        Get all relations for a node.
        
        Args:
            node_id: Node to get relations for
            relation_type: Optional relation type filter
            
        Returns:
            List of relations with target nodes
        """
        relations = []
        for edge in self.edges.values():
            if edge.src == node_id:
                if relation_type is None or edge.edge_type == relation_type:
                    target = self.nodes.get(edge.dst)
                    if target:
                        relations.append({
                            'edge_id': edge.edge_id,
                            'relation': edge.edge_type.value,
                            'target_id': edge.dst,
                            'target_type': target.node_type.value,
                            'target_features': target.features,
                            'properties': edge.properties
                        })
        return relations
    
    def verify_provenance(self) -> bool:
        """
        Verify all elements have provenance.
        
        Returns:
            True if all elements have provenance
        """
        all_elements = set(self.nodes.keys()) | set(self.edges.keys())
        return all(elem_id in self.provenance for elem_id in all_elements)
    
    def to_dict(self) -> dict:
        """Serialize to dictionary"""
        return {
            'nodes': [
                {
                    'id': n.node_id,
                    'type': n.node_type.value,
                    'features': n.features
                }
                for n in self.nodes.values()
            ],
            'edges': [
                {
                    'id': e.edge_id,
                    'type': e.edge_type.value,
                    'src': e.src,
                    'dst': e.dst,
                    'properties': e.properties
                }
                for e in self.edges.values()
            ],
            'provenance': self.provenance
        }
