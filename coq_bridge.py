"""
Python Bridge for Coq Verification

This module provides an interface between Python NLP engines
and the Coq formal verification kernel.

Usage:
    from coq_bridge import verify_construct, ConstructCertificate
    
    cert = ConstructCertificate(
        word="كَتَبَ",
        phonemes=[...],
        c2_spec={"kind": "VERB", "voice": "ACTIVE", "valency": "V1"},
        roles=[...]
    )
    
    is_valid = verify_construct(cert)
"""

import json
import subprocess
import tempfile
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Any
from pathlib import Path


@dataclass
class Phoneme:
    """Represents an Arabic phoneme (consonant + vowel)"""
    consonant: str
    haraka: str


@dataclass
class C2Spec:
    """Syntactic specification for C2 (core operator)"""
    kind: str  # "VERB", "COPULA", "PARTICLE"
    voice: str  # "ACTIVE", "PASSIVE"
    valency: str  # "V0", "V1", "V2"


@dataclass
class RoleFilling:
    """Semantic role and whether it's filled"""
    role: str
    filled: bool


@dataclass
class ConstructCertificate:
    """
    Certificate for a linguistic construct.
    This is what Python engines generate and Coq verifies.
    """
    word: str
    phonemes: List[Phoneme]
    c2_spec: C2Spec
    roles: List[RoleFilling]
    syllables: Optional[List[Dict[str, Any]]] = None
    metadata: Optional[Dict[str, Any]] = None
    
    def to_json(self) -> str:
        """Convert certificate to JSON"""
        return json.dumps(asdict(self), indent=2, ensure_ascii=False)
    
    @classmethod
    def from_json(cls, json_str: str) -> 'ConstructCertificate':
        """Create certificate from JSON"""
        data = json.loads(json_str)
        data['phonemes'] = [Phoneme(**p) for p in data['phonemes']]
        data['c2_spec'] = C2Spec(**data['c2_spec'])
        data['roles'] = [RoleFilling(**r) for r in data['roles']]
        return cls(**data)


class CoqVerifier:
    """
    Interface to Coq verification kernel.
    
    Currently uses JSON certificates and external Coq process.
    Future: Could use extracted OCaml code for efficiency.
    """
    
    def __init__(self, coq_dir: Optional[Path] = None):
        if coq_dir is None:
            # Default to coq/ directory relative to this file
            self.coq_dir = Path(__file__).parent.parent / "coq"
        else:
            self.coq_dir = Path(coq_dir)
        
        self.theories_dir = self.coq_dir / "theories" / "ArabicKernel"
    
    def verify_construct(self, cert: ConstructCertificate) -> tuple[bool, str]:
        """
        Verify a linguistic construct against Coq kernel.
        
        Returns:
            (is_valid, message)
        """
        # For now, we do basic validation in Python
        # Future: Generate Coq proof term and check with coqc
        
        errors = []
        
        # Check 1: No consonant without vowel
        for p in cert.phonemes:
            if not p.haraka or p.haraka == "":
                errors.append(f"Consonant {p.consonant} has no vowel")
        
        # Check 2: Roles must be licensed by C2Spec
        licensed_roles = self._get_licensed_roles(cert.c2_spec)
        for role in cert.roles:
            if role.filled and role.role not in licensed_roles:
                errors.append(f"Role {role.role} not licensed by {cert.c2_spec.kind}")
        
        # Check 3: Agent required for active verbs
        if cert.c2_spec.kind == "VERB" and cert.c2_spec.voice == "ACTIVE":
            has_agent = any(r.role == "AGENT" and r.filled for r in cert.roles)
            if not has_agent:
                errors.append("Active verb requires AGENT role")
        
        if errors:
            return False, "; ".join(errors)
        else:
            return True, "All invariants satisfied"
    
    def _get_licensed_roles(self, spec: C2Spec) -> List[str]:
        """Get licensed roles for a C2Spec (mirrors SlotsTable.v)"""
        if spec.kind == "VERB":
            if spec.voice == "ACTIVE":
                if spec.valency == "V0":
                    return ["AGENT", "TIME"]
                elif spec.valency == "V1":
                    return ["AGENT", "PATIENT", "TIME"]
                elif spec.valency == "V2":
                    return ["AGENT", "THEME", "BENEFICIARY", "TIME"]
            else:  # PASSIVE
                if spec.valency == "V0":
                    return ["TIME"]
                elif spec.valency == "V1":
                    return ["PATIENT", "TIME"]
                elif spec.valency == "V2":
                    return ["THEME", "BENEFICIARY", "TIME"]
        elif spec.kind == "COPULA":
            return ["AGENT", "STATE", "TIME"]
        elif spec.kind == "PARTICLE":
            return ["ASSERTION_FORCE", "MODALITY", "NEGATION_SCOPE"]
        
        return []
    
    def verify_with_coq(self, cert: ConstructCertificate) -> tuple[bool, str]:
        """
        Verify using actual Coq kernel (requires Coq installed).
        This generates a Coq proof term and checks it.
        """
        # TODO: Implement actual Coq verification
        # For now, fall back to Python verification
        return self.verify_construct(cert)


# Convenience function
def verify_construct(cert: ConstructCertificate) -> tuple[bool, str]:
    """Verify a construct certificate"""
    verifier = CoqVerifier()
    return verifier.verify_construct(cert)


# Example usage
if __name__ == "__main__":
    # Example: Verify the word "كَتَبَ" (kataba - he wrote)
    cert = ConstructCertificate(
        word="كَتَبَ",
        phonemes=[
            Phoneme(consonant="ك", haraka="َ"),
            Phoneme(consonant="ت", haraka="َ"),
            Phoneme(consonant="ب", haraka="َ"),
        ],
        c2_spec=C2Spec(
            kind="VERB",
            voice="ACTIVE",
            valency="V1"
        ),
        roles=[
            RoleFilling(role="AGENT", filled=True),
            RoleFilling(role="PATIENT", filled=False),
            RoleFilling(role="TIME", filled=True),
        ]
    )
    
    is_valid, message = verify_construct(cert)
    print(f"Valid: {is_valid}")
    print(f"Message: {message}")
    print(f"\nCertificate JSON:\n{cert.to_json()}")
