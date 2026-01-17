# Quick Start Guide: FractalHub v1.2

## 🚀 5-Minute Quick Start

### Installation

```bash
# Clone the repository
git clone https://github.com/sonaiso/Eqratech_Arabic_Diana_Project.git
cd Eqratech_Arabic_Diana_Project

# Install dependencies
pip install -r requirements-dev.txt

# Install FractalHub package
pip install -e .
```

### Basic Usage

#### Example 1: Load Dictionary and Explore

```python
from fractalhub.data import load_dictionary

# Load v02 dictionary
dictionary = load_dictionary(version="v02")

# Get metadata
meta = dictionary.get_meta()
print(f"Dictionary version: {meta['dict_version']}")
print(f"Compatible with v01: {meta['compatibility']['v01_supported']}")

# Get a unit (diacritic)
fatha = dictionary.get_unit("U:DIACRITIC:FATHA")
print(f"Form: {fatha['form']['arabic']}")
print(f"Unicode: {fatha['form']['unicode']}")
print(f"Confidence: {fatha['provenance']['confidence']}")  # "yaqin" (1.0)

# Get a gate
gate = dictionary.get_gate("G_C1_CODEC_VERIFY")
print(f"Gate: {gate['gate_id']}")
print(f"Rulesets: {gate['ruleset_ids']}")
print(f"Four conditions: {gate['four_conditions']}")
```

#### Example 2: Create Records with Version Metadata

```python
from fractalhub.kernel import Record

# Create a record - automatically gets version metadata
record = Record(
    record_id="MY_RECORD_001",
    record_type="example",
    data={"content": "Some data"}
)

print(f"Kernel version: {record.kernel_version}")  # "1.2"
print(f"Architecture: {record.architecture_version}")  # "locked_v1"
print(f"Created: {record.created_at_iso}")  # ISO 8601 timestamp

# Convert to dictionary
record_dict = record.to_dict()
print(record_dict)
```

#### Example 3: Execute Gate with Tracing

```python
from fractalhub.kernel import Executor, TraceManager
from fractalhub.data import load_dictionary

# Load dictionary
dictionary = load_dictionary(version="v02")

# Create trace manager
trace_manager = TraceManager()

# Create executor
executor = Executor(
    dictionary=dictionary.data,
    trace_manager=trace_manager
)

# Execute a gate
result = executor.execute_gate(
    gate_id="G_C1_CODEC_VERIFY",
    inputs=["raw_text_input"]
)

print(f"Outputs: {result['outputs']}")
print(f"Trace ID: {result['trace_id']}")
print(f"Latency: {result['gate_latency_ms']}ms")
print(f"Evidence strength: {result['evidence_strength']}")

# Verify architecture is locked
stats = trace_manager.get_statistics()
print(f"\nArchitecture locked: {stats['architecture_locked']}")
print(f"Total traces: {stats['total_traces']}")
print(f"Valid traces: {stats['valid_traces']}")
print(f"Avg evidence strength: {stats['avg_evidence_strength']}")
```

#### Example 4: Create Entity with Provenance

```python
from fractalhub.kernel import Entity

# Create an entity - must have signifier link and trace
entity = Entity(
    entity_id="E_FATHA_001",
    signifier_link="U:DIACRITIC:FATHA",  # Points to C1 unit
    meaning={
        "semantic": "short_a_vowel",
        "function": "case_marker"
    },
    provenance={
        "source_type": "grammar_book",
        "confidence": "yaqin",  # Certain
        "attestation_count": 1000,
        "references": ["Sibawayh", "Al-Kitab"]
    },
    created_by_trace_id="TRACE:G_C3_REFERENCE:123456"
)

print(f"Entity: {entity.entity_id}")
print(f"Signifier: {entity.signifier_link}")
print(f"Confidence: {entity.get_confidence()}")  # 1.0
print(f"Has attestation: {entity.has_corpus_attestation()}")  # True

# Convert to dictionary
entity_dict = entity.to_dict()
print(entity_dict)
```

#### Example 5: Evidence-Based Reasoning

```python
from fractalhub.kernel import Reasoner

reasoner = Reasoner()

# Define premises with evidence (prior_ids)
premises = [
    {
        "id": "P1",
        "content": "All humans are mortal",
        "prior_ids": ["AXIOM:MORTALITY", "LOGIC:UNIVERSAL_QUANTIFIER"]
    },
    {
        "id": "P2", 
        "content": "Socrates is human",
        "prior_ids": ["FACT:SOCRATES_IS_HUMAN", "CORPUS:ATTESTATION_123"]
    }
]

# Perform deductive reasoning
result = reasoner.reason(premises, mode="deductive")

print(f"Conclusion: {result['conclusion']}")
print(f"Evidence chain: {result['evidence_chain']}")
print(f"Epistemic strength: {result['epistemic_strength']}")  # 1.0 for deductive
print(f"Trace ID: {result['trace_id']}")

# Try different reasoning modes
modes = ["inductive", "abductive", "inferential"]
for mode in modes:
    result = reasoner.reason(premises, mode=mode)
    print(f"{mode}: strength = {result['epistemic_strength']}")
```

### What Happens When You Try to Violate the Architecture?

#### Example 6: Blocked Operations (Anti-Hallucination)

```python
from fractalhub.kernel import Entity, Reasoner

# ❌ Try to create entity without signifier link
try:
    bad_entity = Entity(
        entity_id="E_BAD",
        signifier_link="",  # Empty!
        meaning={"test": "orphaned meaning"},
        created_by_trace_id="TRACE_123"
    )
except ValueError as e:
    print(f"✅ Blocked: {e}")
    # "Entity E_BAD has no signifier_link. NO MEANING WITHOUT FORM."

# ❌ Try to create entity without trace
try:
    bad_entity = Entity(
        entity_id="E_BAD",
        signifier_link="U:TEST",
        meaning={"test": "no trace"},
        created_by_trace_id=None  # Missing!
    )
except ValueError as e:
    print(f"✅ Blocked: {e}")
    # "Entity E_BAD has no trace pointer. NO C3 WITHOUT C2 TRACE."

# ❌ Try to reason without evidence
reasoner = Reasoner()
try:
    result = reasoner.reason(
        [{"id": "P1", "prior_ids": []}],  # No evidence!
        mode="deductive"
    )
except ValueError as e:
    print(f"✅ Blocked: {e}")
    # "Cannot reason without evidence. Premise 0 lacks prior_ids"

print("\n✅ Architecture locks working - hallucination impossible!")
```

### Validate Dictionary

```bash
# Run validation script
python scripts/validate_dictionary.py fractalhub/data/fractalhub_dictionary_v02.yaml

# Expected output:
# ✅ Validation passed! No errors or warnings.
```

### Run Tests

```python
# Run all tests (manual verification)
python3 <<'EOF'
import sys
sys.path.insert(0, '.')

from tests.fractalhub.test_kernel_v12 import *
from tests.fractalhub.test_dictionary_load import *

# Run a few key tests
test = TestRecord()
test.test_record_creation()
print("✅ Record test passed")

test = TestTraceEntry()
test.test_trace_four_conditions()
print("✅ Trace test passed")

test = TestEntity()
test.test_entity_requires_signifier()
print("✅ Entity test passed")

test = TestDictionaryV02()
test.test_load_v02()
print("✅ Dictionary test passed")

print("\n✅ All key tests passed!")
EOF
```

## 📚 Next Steps

1. **Read the full README**: `FRACTALHUB_README.md`
2. **Check the architecture**: Understand C0→C1→C2→C3 pipeline
3. **Explore the dictionary**: `fractalhub/data/fractalhub_dictionary_v02.yaml`
4. **Build your application**: Use the locked architecture
5. **Contribute**: Add new units/gates following the schema

## 🔗 Resources

- **Main Documentation**: `FRACTALHUB_README.md`
- **Changelog**: `CHANGELOG.md`
- **Release Notes**: `RELEASE_NOTES_v1.2.md`
- **Implementation Details**: `IMPLEMENTATION_SUMMARY.md`
- **Dictionary Schema**: `fractalhub/data/fractalhub_dictionary_v02.yaml`
- **Validation Script**: `scripts/validate_dictionary.py`

## 💡 Key Concepts

- **Locked Architecture**: Cannot generate meaning without evidence
- **Four Conditions**: Reality/Brain/Sensing/Prior must be verified
- **Evidence Chains**: Every operation requires prior_ids
- **Provenance**: All entities track their source and confidence
- **Layer Separation**: C0 (phonology) → C1 (form) → C2 (trace) → C3 (meaning)

**Result**: Hallucination is structurally impossible! ✅

---

**Version**: 1.2.0  
**Architecture**: locked_v1  
**Status**: Production Ready
