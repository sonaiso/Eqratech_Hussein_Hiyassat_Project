# Arabic Kernel - Coq Formalization

## Overview

This directory contains the formal verification layer for the Eqratech Arabic Diana Project. The Coq formalization provides mathematical proofs for the core linguistic invariants of Arabic based on the fractal C1-C2-C3 pattern.

## Architecture

The formalization is structured into several modules:

### 1. FractalCore.v
**Core formalization of the Arabic fractal pattern**

- Defines basic phonetic types (Consonant, Vowel, Phoneme)
- Implements the fractal cell pattern: C1-C2-C3
- Establishes syllable structure (CV, CVC, CVV, CVVC)
- Defines morphological layer (Root, Pattern, Word)
- Specifies syntactic layer (Voice, Valency, C2Spec)
- Declares fundamental invariants:
  - No consonant without vowel
  - No complex onset (CC)
  - OCP (Obligatory Contour Principle)
  - Role must have slot from C2

### 2. Roles.v
**Semantic role system**

- Defines semantic roles (AGENT, PATIENT, THEME, etc.)
- Distinguishes core vs. adjunct roles
- Implements role licensing constraints
- Provides soundness theorems

### 3. SlotsTable.v
**Non-lexical baseline for role slots**

- Maps C2Spec to available role slots
- Defines particle families (14 types)
- Implements SlotsOf function for verbs, copulas, and particles
- Provides extensible framework for new constructions

### 4. Policy.v
**Tactic policy enforcement**

- Defines allowed tactics for kernel proofs
- Lists forbidden tactics (auto, admit, Admitted, etc.)
- Provides policy enforcement mechanisms
- Ensures kernel remains small and trustworthy
- See "Tactic Policy" section below for details

### 5. All.v
**Main export module**

## Building

### Prerequisites

- Coq 8.15 or later
- Make

### Build Instructions

```bash
cd coq
make
```

The build process includes:
1. **Tactic policy check**: Verifies only allowed tactics are used
2. **Coq compilation**: Compiles all .v files

Or using Coq directly:

```bash
cd coq
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

### Check Tactic Policy Only

```bash
cd coq
python3 check_coq_tactics.py --dir theories
```

Options:
- `--strict`: Treat warnings as errors
- `--list-allowed`: Show allowed/forbidden tactics

## Tactic Policy

To keep the kernel **small and trustworthy**, we restrict the tactics used in proofs.

### Allowed Tactics

Only these tactics may be used in kernel proofs:
- `exact`, `apply`, `intro/intros`
- `split`, `left`, `right`, `exists`
- `reflexivity`, `simpl`, `unfold`
- `induction`, `destruct`, `rewrite`, `assumption`

### Forbidden Tactics

These tactics are **strictly forbidden**:
- `admit`, `Admitted` - **UNSOUND**, never use
- `auto`, `tauto` - Too opaque, unclear what they prove
- `omega`, `lia`, `ring`, `field` - External decision procedures

### Rationale

**Why restrict tactics?**
1. **Transparency**: All proofs should be human-reviewable
2. **Trust**: Small kernel = fewer bugs = more confidence
3. **Auditability**: Easy to verify correctness by inspection
4. **Soundness**: No "magic" tactics that could hide errors

### Enforcement

The policy is enforced by:
1. **Static check**: `check_coq_tactics.py` runs during build
2. **CI integration**: Build fails if forbidden tactics detected
3. **Code review**: All proofs reviewed for compliance

See `theories/ArabicKernel/Policy.v` for detailed policy definition.

## Integration with Python Engines

The Coq kernel serves as a **verifier** for the Python-based NLP engines:

1. **Python engines** act as **elaborators**: they analyze text and generate proposals
2. **Coq kernel** acts as **verifier**: it checks that proposals satisfy all invariants
3. Only verified outputs are accepted as correct

### Verification Workflow

```
Python Engine → JSON Certificate → Coq Verification → Accept/Reject
```

Example JSON certificate:
```json
{
  "construct": "كَتَبَ",
  "phonemes": [...],
  "syllables": [...],
  "c2_spec": {"kind": "VERB", "voice": "ACTIVE", "valency": "V1"},
  "roles": [{"role": "AGENT", "filled": true}, ...]
}
```

## Fractal Principle

The core principle formalized here is that Arabic linguistic structure follows a fractal pattern at every level:

1. **Phonology**: Consonant needs vowel (no bare consonant)
2. **Syllable**: C2 (nucleus) constrained by C1 (onset) and C3 (coda)
3. **Morphology**: Pattern (C2) applied to Root (C1) with inflection (C3)
4. **Syntax**: Verb (C2) with Agent (C1) and Patient (C3)
5. **Semantics**: Role (C2) licensed by Slot (from C2Spec)

**Main Theorem (to be proven)**:
```coq
Theorem Fractal_Arabic_Soundness :
  forall construct : ValidConstruct,
  (* All invariants are satisfied *)
  well_formed_phonetic ∧
  no_complex_onset ∧
  ocp_satisfied ∧
  roles_sound.
```

## Current Status

- ✅ Core types defined
- ✅ Fractal pattern formalized
- ✅ Role system implemented
- ✅ SlotsTable baseline created
- ⏳ Main theorems stated (proofs in progress)
- ⏳ Integration with Python engines (planned)
- ⏳ CI verification pipeline (planned)

## Future Work

1. **Complete proofs**: Prove all stated theorems
2. **Python bridge**: Create JSON schema and verification interface
3. **CI integration**: Add Coq verification to GitHub Actions
4. **Expand coverage**: Add more linguistic phenomena
5. **Extraction**: Extract verified code to OCaml/Haskell

## References

- **De Bruijn Criterion**: Used for ensuring soundness of the kernel
- **Curry-Howard Correspondence**: Proofs as programs
- **Arabic Linguistic Theory**: Traditional Arabic grammar (النحو العربي)

## License

Same as parent project - Eqratech Arabic Diana Project

---
Last updated: 2025-12-25
