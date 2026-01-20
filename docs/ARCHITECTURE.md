# FractalHub Architecture

## Overview

FractalHub implements a **locked architecture** that prevents AI hallucinations through strict provenance tracking and layer separation. The architecture is based on Al-Nabhani's Theory of Thinking.

## Core Principles

### 1. Locked Architecture Constraints

The system enforces four immutable constraints:

1. **NO C3 without C2 trace**
   - No meaning (C3) can exist without a documented gate passage (C2)
   - Every concept must trace back through processing chain
   
2. **NO C2 without C1 four conditions**
   - All gates must verify Al-Nabhani's Four Conditions of Mind:
     - **Reality**: The form stream being processed
     - **Brain**: The executor/processor
     - **Sensing**: The channel/modality
     - **Prior Knowledge**: Evidence from dictionary (lexicon_ids/ruleset_ids)
   
3. **NO meaning without prior_ids evidence**
   - Every meaning must reference dictionary entries
   - Hallucination prevention through provenance tracking
   
4. **Strict layer separation**
   - C1 (Signifier): Form only - meaning forbidden
   - C3 (Signified): Meaning only - form forbidden
   - Connection ONLY through C2 gates

### 2. Why This Prevents Hallucinations

Traditional AI systems can generate plausible but false information because they don't require:
- **Evidence**: Dictionary references (prior_ids)
- **Documentation**: Trace of how meaning was derived
- **Separation**: Clear distinction between form and meaning

FractalHub prevents this by:
- **Enforcing evidence**: All meanings must reference dictionary
- **Requiring traces**: All meanings must document processing path
- **Separating layers**: Form and meaning kept strictly apart

## Layer Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ C3: Signified Layer (Meaning)                               │
│                                                              │
│ - Entities, events, roles, relations                        │
│ - MUST have provenance from dictionary                      │
│ - MUST have trace_id documenting creation                   │
│ - NO form data allowed                                      │
│                                                              │
│ Example: SIGNIFIED:KITAB:BOOK                               │
│   concept_en: "book"                                        │
│   semantic_features: ["physical_object", "information"]    │
│   provenance: [CLASSICAL_CORPUS]                            │
└───────────────────────┬─────────────────────────────────────┘
                        │
                        │ Connection ONLY through C2 Gates
                        │
┌───────────────────────▼─────────────────────────────────────┐
│ C2: Gate & Trace Layer                                      │
│                                                              │
│ Core Gates:                                                 │
│ - G_ATTEND: Attention mechanism                             │
│ - G_CODEC_VERIFY: Form verification                         │
│ - G_SPEECH_ACT: Speech act recognition                      │
│ - G_MEMORY_READ: Memory retrieval                           │
│ - G_MEMORY_WRITE: Memory storage                            │
│                                                              │
│ Each gate requires Four Conditions:                         │
│ - Reality (form_stream)                                     │
│ - Brain (executor)                                          │
│ - Sensing (channel)                                         │
│ - Prior Knowledge (lexicon_ids/ruleset_ids)                 │
│                                                              │
│ Trace Schema:                                               │
│ - gate_chain: List of gates activated                       │
│ - prior_ids: Dictionary evidence                            │
│ - evidence_strength: Epistemic confidence (0.0-1.0)         │
│ - gate_latency: Execution time per gate                     │
│ - invariant_checks: Constraint validation results           │
└───────────────────────┬─────────────────────────────────────┘
                        │
                        │ Four Conditions enforced
                        │
┌───────────────────────▼─────────────────────────────────────┐
│ C1: Signifier Layer (Form)                                  │
│                                                              │
│ - Phonemes, diacritics, tokens                              │
│ - FormCodec: 100% reversible text ⇄ numbers                 │
│ - NO meaning allowed                                        │
│ - NO semantic features                                      │
│                                                              │
│ Example: SIGNIFIER:KITAB                                    │
│   form: "كتاب"                                              │
│   phonetic: "/kitaːb/"                                      │
│   features: ["noun", "masculine"]  ← structural only        │
└───────────────────────┬─────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────┐
│ C0: Phonological Layer                                      │
│                                                              │
│ - Segments (consonants, vowels)                             │
│ - Syllable structures: CV, CVC, CVV, CVVC, CVCC             │
│ - Phonotactic constraints                                   │
│ - OCP violation detection                                   │
│ - Maximal onset principle                                   │
└─────────────────────────────────────────────────────────────┘
```

## Component Details

### Kernel Components

#### 1. Version System (`fractalhub/kernel/version.py`)

Provides version metadata for all records:
- kernel_version: "1.2"
- api_version: "1.2.0"
- compatibility tracking
- ISO timestamps

#### 2. Trace System (`fractalhub/kernel/trace.py`)

Enhanced trace schema with:
- **gate_chain**: Ordered list of gates
- **prior_ids**: Dictionary evidence (lexicon_ids, ruleset_ids)
- **evidence_strength**: Epistemic confidence (0.0-1.0)
- **gate_latency**: Execution time per gate
- **invariant_checks_report**: Constraint validation results
- **resource_usage**: Memory and CPU tracking

#### 3. Gate System (`fractalhub/kernel/gates.py`)

Five core gates implementing Four Conditions:
- **G_ATTEND**: Focus on relevant form elements
- **G_CODEC_VERIFY**: Verify form encoding integrity
- **G_SPEECH_ACT**: Identify speech act type
- **G_MEMORY_READ**: Retrieve prior knowledge
- **G_MEMORY_WRITE**: Store new knowledge

Each gate requires:
```python
FourConditions(
    reality="form_stream",      # Required
    brain="processor_id",       # Required
    sensing="channel",          # Required
    prior_knowledge={...}       # Required (from dictionary)
)
```

#### 4. FormCodec (`fractalhub/kernel/codec.py`)

100% reversible text encoding:
- Text → numbers with SHA-256 checksum
- Perfect Arabic text handling
- Batch encoding support
- Reversibility verification

#### 5. MeaningCodec (`fractalhub/kernel/codec.py`)

Meaning creation with provenance:
- **Requires trace_id** (NO C3 without C2)
- **Requires prior_ids** (NO meaning without evidence)
- Full provenance tracking
- Layer enforcement (C3 only)

### Dictionary Components

#### 1. Dictionary Structure

Bilingual YAML with:
- **Provenance sources**: 4 sources with reliability scores
- **Lexicon entries**: Signifiers (C1) and Signifieds (C3)
- **Rulesets**: Phonological, morphological, syntactic rules
- **Gates**: Gate definitions with four conditions
- **Evidence**: Epistemic strengths and reasoning modes
- **Invariants**: Conservation laws and symmetry rules

#### 2. Dictionary Loader (`fractalhub/dictionary/__init__.py`)

Provides access to:
- Lexicon entries by ID
- Rulesets by layer
- Provenance sources
- Gate definitions
- prior_ids validation

#### 3. Dictionary Validator (`fractalhub/dictionary/validator.py`)

Validates:
- Schema compliance
- Provenance completeness
- Entry type separation
- Cross-reference integrity
- DRY principle

## Data Flow

### Example: Processing "كتاب" (book)

```python
# 1. Encode form (C1)
codec = FormCodec()
encoded, checksum = codec.encode("كتاب")

# 2. Create trace with dictionary evidence (C2)
trace = Trace()
trace.add_gate("G_ATTEND:001")
trace.add_gate("G_CODEC_VERIFY:001")
trace.add_prior_id("lexicon_ids", "SIGNIFIER:KITAB")
trace.add_prior_id("lexicon_ids", "SIGNIFIED:KITAB:BOOK")

# 3. Validate trace (requires gates + prior_ids)
is_valid, errors = trace.validate()

# 4. Create meaning with provenance (C3)
meaning_codec = MeaningCodec()
book_entry = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")

meaning = meaning_codec.encode_meaning(
    concept=book_entry['concept_en'],
    trace_id=trace.trace_id,              # C2 requirement
    prior_ids=trace.prior_ids,            # Evidence requirement
    provenance=book_entry['provenance']   # Source tracking
)

# Result: Fully documented meaning with complete provenance chain
```

## Invariants

### Conservation Laws

Six conservation laws ensure logical consistency:

1. **Temporal Conservation**: Events maintain temporal order
2. **Referential Conservation**: References are resolvable
3. **Causal Conservation**: Causes precede effects
4. **Predicative Conservation**: Predicates match arguments
5. **Quantitative Conservation**: Quantities are preserved
6. **Scope Conservation**: Scope boundaries maintained

### Symmetry Rules

Four symmetry rules ensure structural consistency:

1. **Logical Symmetry**: Logical operations preserve truth
2. **Structural Symmetry**: Structure preserved under transformation
3. **Semantic Symmetry**: Meaning preserved under paraphrase
4. **Pragmatic Symmetry**: Communicative intent preserved

## Extensions

### Adding New Layers

To add a new layer:
1. Define layer constraints
2. Create gate requirements
3. Document provenance tracking
4. Add tests for constraints
5. Update architecture documentation

### Adding New Gates

To add a new gate:
1. Define Four Conditions requirements
2. Specify input/output types
3. Document processing logic
4. Add to dictionary gate definitions
5. Create comprehensive tests

### Adding Dictionary Entries

To add dictionary entries:
1. Determine entry type (signifier vs signified)
2. Add provenance sources
3. Link related entries
4. Validate with validator
5. Add tests
