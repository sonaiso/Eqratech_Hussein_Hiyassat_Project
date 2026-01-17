# FractalHub: Consciousness Kernel v1.2

> A locked architecture preventing hallucination through evidence-based reasoning and strict layer separation

[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Python](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[![Version](https://img.shields.io/badge/version-1.2.0-green.svg)](CHANGELOG.md)

## 🎯 Quick Start

```python
from fractalhub.kernel import Record, TraceManager, Executor
from fractalhub.data import load_dictionary

# Load the dictionary
dictionary = load_dictionary(version="v02")

# Create an executor with trace management
trace_manager = TraceManager()
executor = Executor(dictionary=dictionary.data, trace_manager=trace_manager)

# Execute a gate with full tracing
result = executor.execute_gate(
    gate_id="G_C1_CODEC_VERIFY",
    inputs=["raw_text_input"]
)

# Verify locked architecture (no hallucination)
assert trace_manager.verify_no_hallucination()
print(f"✅ Architecture locked: {trace_manager.get_statistics()}")
```

## 📚 Overview

FractalHub implements a **consciousness kernel** for Arabic NLP that prevents hallucination through:

- **Four Conditions Verification**: Every cognitive operation requires Reality/Brain/Sensing/Prior
- **Evidence Chains**: No meaning without prior_ids (lexicon_ids/ruleset_ids)
- **Strict Layer Separation**: C0 (Phonology) → C1 (Signifier) → C2 (Trace) → C3 (Signified)
- **Full Provenance**: All entities track their origin with epistemic confidence levels

### Core Problems Solved

1. **Hallucination Prevention**: Cannot generate meaning without evidence
2. **Traceability**: Every output has a complete audit trail
3. **Cognitive Accountability**: Four conditions ensure grounded reasoning
4. **Quality Control**: Epistemic levels (YAQIN/ZANN/SHAKK) track confidence

## 🏗️ Architecture

### Locked Architecture Rules

```
Rule 1: NO C3 (meaning) WITHOUT C2 trace
Rule 2: NO C2 gate activation WITHOUT C1 four conditions:
        - Reality (form_stream exists)
        - Brain (executor present)
        - Sensing (channel verified)
        - Prior Knowledge (lexicon_ids/ruleset_ids recorded)
Rule 3: NO meaning generation WITHOUT evidence prior_ids
Rule 4: STRICT SEPARATION between signifier and signified layers
```

### Pipeline Flow

```
C0: Phonological Layer
├── Segments (consonants, vowels)
├── Syllable structure (CV, CVC, CVV, CVVC, CVCC)
└── Phonotactic constraints (OCP, gemination)
    ↓
C1: Signifier Layer (Form Only - NO MEANING)
├── Text/diacritics/tokens
├── FormCodec (100% reversible)
└── Four conditions verification
    ↓
C2: Trace Layer (Evidence & Gates)
├── Gate chain (G_ATTEND, G_CODEC_VERIFY, G_SPEECH_ACT, etc.)
├── Prior_ids tracking (lexicon_ids, ruleset_ids)
├── Four conditions logged
└── Invariants enforcement
    ↓
C3: Signified Layer (Meaning with Provenance)
├── Entities (nouns, verbs, concepts)
├── Relations (semantic roles)
├── Provenance (source, confidence, attestation)
└── NO orphaned meaning (all linked to C1)
```

### Four Conditions of Cognition

Based on Al-Nabahani's framework, every cognitive operation verifies:

1. **Reality (الواقع)**: form_stream data present
2. **Brain (الدماغ)**: executor/processor active  
3. **Sensing (الحس)**: channel/modality validated
4. **Prior Knowledge (المعلومات السابقة)**: lexicon_ids/ruleset_ids logged

## 🔒 Why This Prevents Hallucination

### Traditional NLP Problem
```python
# Traditional approach - can generate ANY text
model.generate("Once upon a time...")  # No grounding, no trace
```

### FractalHub Solution
```python
# FractalHub - evidence required
try:
    executor.execute_gate(
        gate_id="G_C3_REFERENCE",
        inputs=["derived_form"],
        # NO prior_ids provided!
    )
except ValueError as e:
    print("❌ Blocked: requires evidence")  # Cannot proceed without evidence

# With evidence - works
result = executor.execute_gate(
    gate_id="G_C3_REFERENCE", 
    inputs=["derived_form"],
    prior_ids=["CORPUS:ENTRY_123"]  # Evidence provided
)
print("✅ Trace created:", result["trace_id"])
```

### Key Mechanisms

1. **No Floating Meanings**: All C3 entities must link to C1 signifiers
2. **Evidence Chains**: `prior_ids` required for semantic operations
3. **Trace Validation**: TraceManager rejects invalid traces
4. **Four Conditions**: Gates fail if conditions not met

## 📖 Dictionary Structure

### Units (Signifier-Only)

```yaml
U:DIACRITIC:FATHA:
  lexicon_id: "U:DIACRITIC:FATHA"
  type: "signifier_only"  # NO MEANING
  layer: "C1"
  form:
    arabic: "َ"
    unicode: "U+064E"
    ipa: "a"
  provenance:
    source_type: "grammar_book"
    confidence: "yaqin"  # 1.0 certainty
    references: ["Sibawayh", "Al-Kitab"]
```

### Gates (with Evidence)

```yaml
G_C1_CODEC_VERIFY:
  gate_id: "G_C1_CODEC_VERIFY"
  layer: "C1"
  four_conditions:
    reality: "form_stream present"
    brain: "codec executor active"
    sensing: "text channel verified"
    prior: "lexicon_ids for codepoints"
  ruleset_ids:  # Evidence!
    - "RULESET:UTF8_VALIDATION"
    - "RULESET:ARABIC_SCRIPT_RANGE"
```

## 💡 Examples

### Example 1: Creating an Entity with Provenance

```python
from fractalhub.kernel import Entity

# This works - has signifier link and trace
entity = Entity(
    entity_id="E_FATHA_MEANING",
    signifier_link="U:DIACRITIC:FATHA",  # Points to C1
    meaning={"semantic": "short_a_vowel", "function": "case_marker"},
    provenance={
        "source_type": "grammar_book",
        "confidence": "yaqin",
        "attestation_count": 1000,
    },
    created_by_trace_id="TRACE:G_C3_REFERENCE:123456"  # Trace pointer
)

print(f"Confidence: {entity.get_confidence()}")  # 1.0
print(f"Has attestation: {entity.has_corpus_attestation()}")  # True

# This fails - no signifier link
try:
    bad_entity = Entity(
        entity_id="E_BAD",
        signifier_link="",  # ❌ Empty!
        meaning={"test": "orphaned"},
        created_by_trace_id="TRACE_123"
    )
except ValueError as e:
    print(f"❌ Blocked: {e}")  # "NO MEANING WITHOUT FORM"
```

### Example 2: Evidence-Based Reasoning

```python
from fractalhub.kernel import Reasoner

reasoner = Reasoner()

# Premises MUST have prior_ids (evidence)
premises = [
    {
        "id": "P1",
        "content": "All humans are mortal",
        "prior_ids": ["AXIOM:MORTALITY"]  # Evidence
    },
    {
        "id": "P2",
        "content": "Socrates is human",
        "prior_ids": ["FACT:SOCRATES"]  # Evidence
    }
]

result = reasoner.reason(premises, mode="deductive")

print(f"Conclusion: {result['conclusion']}")
print(f"Evidence chain: {result['evidence_chain']}")
print(f"Epistemic strength: {result['epistemic_strength']}")  # 1.0 (deductive)
print(f"Trace ID: {result['trace_id']}")  # Full audit trail

# This fails - no evidence
try:
    bad_premises = [{"id": "P1", "prior_ids": []}]  # ❌ Empty!
    reasoner.reason(bad_premises, mode="deductive")
except ValueError as e:
    print(f"❌ Blocked: {e}")  # "Cannot reason without evidence"
```

### Example 3: Dictionary Loading

```python
from fractalhub.data import load_dictionary

# Load v02 (current)
dict_v02 = load_dictionary(version="v02")

# Get a unit
fatha = dict_v02.get_unit("U:DIACRITIC:FATHA")
print(f"Form: {fatha['form']['arabic']}")
print(f"Confidence: {fatha['provenance']['confidence']}")

# Get a gate
gate = dict_v02.get_gate("G_C1_CODEC_VERIFY")
print(f"Ruleset IDs: {gate['ruleset_ids']}")
print(f"Four conditions: {gate['four_conditions']}")

# Check metadata
meta = dict_v02.get_meta()
print(f"Dictionary version: {meta['dict_version']}")
print(f"Backward compatible: {meta['compatibility']['v01_supported']}")
```

## 🧪 Testing

### Run Dictionary Validation

```bash
python scripts/validate_dictionary.py fractalhub/data/fractalhub_dictionary_v02.yaml
```

Expected output:
```
Validating dictionary: fractalhub/data/fractalhub_dictionary_v02.yaml
============================================================
✅ Validation passed! No errors or warnings.
```

### Run Tests

```bash
# Run all tests
pytest tests/fractalhub/

# Run specific test module
pytest tests/fractalhub/test_kernel_v12.py -v

# Run with coverage
pytest tests/fractalhub/ --cov=fractalhub --cov-report=html
```

## 📊 Key Capabilities

### Kernel v1.2 Features

- ✅ Version metadata on all records (kernel_version, architecture_version, created_at_iso)
- ✅ Enhanced trace schema (gate_latency_ms, evidence_strength, invariant_checks, four_conditions_verified)
- ✅ Executor with evidence logging (lexicon_ids/ruleset_ids tracked)
- ✅ Entity provenance tracking (source_type, confidence, attestation_count)
- ✅ Evidence-based reasoning (NO reasoning without prior_ids)

### Dictionary v02 Features

- ✅ Bilingual structure (Arabic/English)
- ✅ Provenance schema for all entries
- ✅ Signifier-only vs signified entity types
- ✅ Ruleset_ids mapping for gates
- ✅ Epistemic evidence levels (YAQIN/ZANN/SHAKK)
- ✅ Repair operations schema
- ✅ Prosody markers and phonological atoms

### Epistemic Levels

| Level | Certainty | Description | Requirements |
|-------|-----------|-------------|--------------|
| YAQIN (اليقين) | 1.0 | Absolute certainty | Corpus attestation, multiple sources, expert consensus |
| ZANN (الظن) | 0.7 | Strong probability | Single source, rule-derived, analogical reasoning |
| SHAKK (الشك) | 0.4 | Weak probability | Inference only, no direct evidence |

## ❓ FAQ

**Q: Why can't I create meaning without a signifier link?**  
A: Rule 4 of locked architecture: NO orphaned meaning. All C3 entities must trace back to C1 forms.

**Q: What happens if I don't provide prior_ids?**  
A: Operations fail with `ValueError: Cannot reason without evidence`. This prevents hallucination.

**Q: Can I use v01 dictionary?**  
A: Yes! v02 maintains full backward compatibility. Use `load_dictionary(version="v01")`.

**Q: How do I add new units to the dictionary?**  
A: Edit `fractalhub/data/fractalhub_dictionary_v02.yaml` following the schema, then run `scripts/validate_dictionary.py`.

**Q: What's the difference between signifier_only and signified_entity?**  
A: `signifier_only` = form with NO meaning (C1 layer: phonemes, diacritics). `signified_entity` = form + meaning + provenance (C3 layer: nouns, verbs).

## 🔧 Troubleshooting

### Import Error: "No module named 'fractalhub'"

```bash
# Install the package
pip install -e .

# Or add to PYTHONPATH
export PYTHONPATH=.:$PYTHONPATH
```

### Validation Error: "Missing provenance"

For v02 dictionary entries, provenance is required. Add:

```yaml
provenance:
  source_type: "grammar_book"  # or corpus, expert_validation, derived
  confidence: "yaqin"  # or zann, shakk
  attestation_count: 100
  references: ["Source1", "Source2"]
```

### Test Collection Error

Use the test runner script:

```bash
python scripts/run_tests.py tests/fractalhub/ -v
```

## 🤝 Contributing

### Adding New Gates

1. Edit `fractalhub/data/fractalhub_dictionary_v02.yaml`
2. Add gate definition with:
   - `gate_id` (format: G_LAYER_NAME)
   - `four_conditions` (reality/brain/sensing/prior)
   - `ruleset_ids` (evidence)
   - Bilingual descriptions
3. Run validation: `python scripts/validate_dictionary.py ...`
4. Add tests in `tests/fractalhub/`

### Code Style

- Follow PEP 8
- Use type hints
- Document with docstrings
- Maintain <80 char line length where reasonable

## 📝 License

MIT License - see LICENSE file

## 📞 Contact

For questions or issues, please open a GitHub issue.

---

**Last Updated**: 2026-01-17  
**Version**: 1.2.0  
**Architecture**: locked_v1 (anti-hallucination)
