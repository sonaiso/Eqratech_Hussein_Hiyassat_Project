"""
Constraint Validator: Checks grammatical constraints on a SyntacticGraph.

Implements 5 constraints:
1. SubjectVerbAgreement: subject and verb must agree in gender and number
2. IsnadiUniqueness: each predicate should have at most one isnadi subject
3. IdafaChain: an iDafa chain should not exceed 5 levels deep
4. HaalAccusative: a Haal must be accusative (mansub)
5. AmiilSign: every governed word must have an identifiable amil (governor)

Author: Hussein Hiyassat
Date: 2025-02-27
Version: 1.0
"""

from dataclasses import dataclass, field
from typing import List
import sys
sys.path.insert(0, 'src')

from fvafk.c2b.word_form import Case
from .syntactic_parser import SyntacticGraph


@dataclass
class ConstraintViolation:
    """Represents a single constraint violation in a SyntacticGraph."""
    constraint_name: str
    token_indices: List[int] = field(default_factory=list)
    severity: str = "warning"  # "error" or "warning"
    message: str = ""


class ConstraintValidator:
    """
    Validates a SyntacticGraph against a set of grammatical constraints.
    """

    def validate(self, graph: SyntacticGraph) -> List[ConstraintViolation]:
        """
        Run all constraints against the graph.

        Args:
            graph: SyntacticGraph to validate

        Returns:
            List of ConstraintViolation instances (empty = well-formed)
        """
        violations: List[ConstraintViolation] = []
        violations.extend(self._check_subject_verb_agreement(graph))
        violations.extend(self._check_isnadi_uniqueness(graph))
        violations.extend(self._check_idafa_chain(graph))
        violations.extend(self._check_haal_accusative(graph))
        violations.extend(self._check_amiil_sign(graph))
        return violations

    # ------------------------------------------------------------------
    # Constraint 1: SubjectVerbAgreement
    # ------------------------------------------------------------------
    def _check_subject_verb_agreement(
        self, graph: SyntacticGraph
    ) -> List[ConstraintViolation]:
        """Subject and verb must agree in gender and number."""
        violations = []
        tokens = graph.tokens

        for link in graph.isnadi_links:
            if link.head_id >= len(tokens) or link.dependent_id >= len(tokens):
                continue
            head = tokens[link.head_id]
            dep = tokens[link.dependent_id]

            # Only check verb-subject pairs
            if not (head.is_verb or dep.is_verb):
                continue

            verb = head if head.is_verb else dep
            subject = dep if head.is_verb else head

            if not subject.agrees_with(verb, ['gender', 'number']):
                violations.append(ConstraintViolation(
                    constraint_name="SubjectVerbAgreement",
                    token_indices=[link.head_id, link.dependent_id],
                    severity="error",
                    message=(
                        f"Subject '{subject.surface}' and verb '{verb.surface}' "
                        f"disagree in gender/number"
                    ),
                ))
        return violations

    # ------------------------------------------------------------------
    # Constraint 2: IsnadiUniqueness
    # ------------------------------------------------------------------
    def _check_isnadi_uniqueness(
        self, graph: SyntacticGraph
    ) -> List[ConstraintViolation]:
        """Each predicate should have at most one isnadi subject link."""
        violations = []
        dep_counts: dict = {}
        for link in graph.isnadi_links:
            dep_counts[link.dependent_id] = dep_counts.get(link.dependent_id, 0) + 1

        for dep_id, count in dep_counts.items():
            if count > 1:
                violations.append(ConstraintViolation(
                    constraint_name="IsnadiUniqueness",
                    token_indices=[dep_id],
                    severity="warning",
                    message=(
                        f"Token at index {dep_id} has {count} isnadi links "
                        f"(expected at most 1)"
                    ),
                ))
        return violations

    # ------------------------------------------------------------------
    # Constraint 3: IdafaChain
    # ------------------------------------------------------------------
    def _check_idafa_chain(
        self, graph: SyntacticGraph
    ) -> List[ConstraintViolation]:
        """An iDafa chain should not exceed 5 levels deep."""
        violations = []
        # Build adjacency: head_idx → [dep_idx, ...]
        idafa_children: dict = {}
        for tl in graph.tadmini_links:
            if tl.link_type == "IDAFA":
                idafa_children.setdefault(tl.head_idx, []).append(tl.dep_idx)

        def _depth(node: int, visited: set) -> int:
            if node in visited:
                return 0
            visited.add(node)
            children = idafa_children.get(node, [])
            if not children:
                return 0
            return 1 + max(_depth(c, visited) for c in children)

        for head_idx in idafa_children:
            depth = _depth(head_idx, set())
            if depth > 5:
                violations.append(ConstraintViolation(
                    constraint_name="IdafaChain",
                    token_indices=[head_idx],
                    severity="warning",
                    message=(
                        f"iDafa chain starting at index {head_idx} "
                        f"is {depth} levels deep (maximum 5)"
                    ),
                ))
        return violations

    # ------------------------------------------------------------------
    # Constraint 4: HaalAccusative
    # ------------------------------------------------------------------
    def _check_haal_accusative(
        self, graph: SyntacticGraph
    ) -> List[ConstraintViolation]:
        """A Haal must be accusative (mansub)."""
        violations = []
        tokens = graph.tokens

        for tq in graph.taqyidi_links:
            if tq.link_type != "HAAL":
                continue
            if tq.dep_idx >= len(tokens):
                continue
            dep = tokens[tq.dep_idx]
            if dep.case != Case.ACCUSATIVE and dep.case.value != "unknown":
                violations.append(ConstraintViolation(
                    constraint_name="HaalAccusative",
                    token_indices=[tq.dep_idx],
                    severity="error",
                    message=(
                        f"Haal '{dep.surface}' is not accusative "
                        f"(found case: {dep.case.value})"
                    ),
                ))
        return violations

    # ------------------------------------------------------------------
    # Constraint 5: AmiilSign
    # ------------------------------------------------------------------
    def _check_amiil_sign(
        self, graph: SyntacticGraph
    ) -> List[ConstraintViolation]:
        """Every governed word (non-nominative) should have an identifiable governor."""
        violations = []
        tokens = graph.tokens

        # Collect all dependent indices across all link types
        governed_ids: set = set()
        for link in graph.isnadi_links:
            governed_ids.add(link.dependent_id)
        for tl in graph.tadmini_links:
            governed_ids.add(tl.dep_idx)
        for tq in graph.taqyidi_links:
            governed_ids.add(tq.dep_idx)

        # Check each non-nominative noun/adjective
        for i, token in enumerate(tokens):
            if token.case in (Case.ACCUSATIVE, Case.GENITIVE):
                if i not in governed_ids:
                    violations.append(ConstraintViolation(
                        constraint_name="AmiilSign",
                        token_indices=[i],
                        severity="warning",
                        message=(
                            f"Token '{token.surface}' (case={token.case.value}) "
                            f"has no identifiable governor (amil)"
                        ),
                    ))
        return violations
