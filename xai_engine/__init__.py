"""
XAI Engine - Explainable AI with Strict Epistemological Constraints

This engine implements a 6-layer architecture for generating judgments 
(not predictions) with full explanation traces.

Architecture:
    C0 (Reality) → C1 (Form) → C2 (Trace/Measurement) → C3 (Meaning/Judgment)
    
Layers:
    1. Form Layer (الدال) - Shape without meaning
    2. Semantic Layer (المدلول) - Meaning candidates
    3. Relational Layer (النِّسب) - Relations enabling judgment
    4. Measurement Layer (الإعراب) - Operator-based measurement
    5. Judgment Layer (الحكم) - Final propositions/directives
    6. Explanation Layer (التفسير) - Why-chains for every decision

Global Constraints:
    - No conclusion without measurement
    - No generalization without scope
    - No judgment without relation
    - No explanation without trace
    - No jump between layers
    - Domain isolation maintained

Version: 1.0
Architecture: locked_v1 (anti-hallucination)
Compatible with: FractalHub Consciousness Kernel v1.2
"""

__version__ = "1.0.0"
__architecture__ = "locked_v1"

from .core.engine import XAIEngine
from .core.pipeline import XAIPipeline
from .core.domain import Domain, DomainType
from .ctegate import (
    TextualCertaintyGate,
    GateLevel,
    GateCondition,
    GateResult,
    ConditionViolation,
    evaluate_textual_certainty,
)
from .ctegate_domains import (
    DomainSpecificGate,
    DomainCondition,
    DomainViolation,
    evaluate_with_domain,
)

__all__ = [
    "XAIEngine",
    "XAIPipeline", 
    "Domain",
    "DomainType",
    # CTE Gate components
    "TextualCertaintyGate",
    "GateLevel",
    "GateCondition",
    "GateResult",
    "ConditionViolation",
    "evaluate_textual_certainty",
    # Domain-specific CTE Gate
    "DomainSpecificGate",
    "DomainCondition",
    "DomainViolation",
    "evaluate_with_domain",
]
