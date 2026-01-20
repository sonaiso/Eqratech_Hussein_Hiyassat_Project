# FractalHub: Fractal Consciousness Kernel v1.2

> A consciousness platform implementing Al-Nabhani's Theory of Thinking with complete separation between signifier and signified, preventing hallucinations through locked architecture.

[![Tests](https://img.shields.io/badge/tests-96%20passing-success)]()
[![Version](https://img.shields.io/badge/kernel-v1.2-blue)]()
[![Dictionary](https://img.shields.io/badge/dictionary-v02-blue)]()

---

## 🎯 Quick Start

### Installation

```bash
# Install from source
pip install -e .

# Install with development dependencies
pip install -e ".[dev]"

# Install with web server support
pip install -e ".[web]"

# Install with data processing support
pip install -e ".[data]"
```

### Validate Dictionary

```bash
# Using installed CLI
fractalhub-validate

# Or using script
python scripts/validate_dictionary.py
```

### Run Tests

```bash
# Run all tests
pytest

# Run specific test suite
pytest tests/test_kernel_v12.py -v
```

### Basic Usage

```python
from fractalhub import Trace, FormCodec
from fractalhub.dictionary import get_dictionary

# Create trace with dictionary evidence
trace = Trace()
trace.add_gate("G_ATTEND:001")
trace.add_prior_id("lexicon_ids", "SIGNIFIER:FATHA")

# Validate trace
is_valid, errors = trace.validate()

# Encode/decode Arabic text (100% reversible)
codec = FormCodec()
encoded, checksum = codec.encode("السلام")
decoded = codec.decode(encoded, checksum)
```

---

## 📁 Project Structure

```
Eqratech_Arabic_Diana_Project/
├── fractalhub/              # Main package
│   ├── kernel/             # Core kernel (version, trace, gates, codec)
│   ├── dictionary/         # Dictionary loader and validator
│   ├── data/              # Data files (YAML dictionaries)
│   └── cli.py             # Command-line interface
├── tests/                  # Test suite (96 tests)
├── scripts/                # Utility scripts
├── docs/                   # Documentation
│   └── ARCHITECTURE.md    # Detailed architecture
├── pyproject.toml         # Package configuration
├── setup.py               # Backward-compatible setup
├── LICENSE                # MIT License
├── CONTRIBUTING.md        # Contribution guidelines
└── RELEASE_NOTES.md       # Version history
```

---

## 🏗️ Locked Architecture (Hallucination Prevention)

### Core Invariants

1. **NO C3 without C2 trace** - No meaning without documented gate passage
2. **NO C2 without C1 four conditions** - Gates verify Reality/Brain/Sensing/Prior Knowledge
3. **NO meaning without prior_ids** - Evidence required from dictionary
4. **Strict layer separation** - C1 (form) ↔ C2 (gates) ↔ C3 (meaning)

### Layer Architecture

```
C3: Signified (Meaning)
    ↕ Entities/events with provenance
C2: Gates & Trace
    ↕ Documented passages (G_ATTEND, G_CODEC_VERIFY, etc.)
C1: Signifier (Form)
    ↕ Phonemes/tokens (no meaning)
C0: Phonological
    ↕ Segments/syllables/constraints
```

---

## 📊 Component Status

| Component | Tests | Status |
|-----------|-------|--------|
| Kernel v1.2 | 37 | ✅ |
| Dictionary v02 | 36 | ✅ |
| Integration | 23 | ✅ |
| **TOTAL** | **96** | ✅ |

---

## 📖 Examples

### Example 1: Form Encoding

```python
from fractalhub import FormCodec

codec = FormCodec()
text = "كتاب"
encoded, checksum = codec.encode(text)
decoded = codec.decode(encoded, checksum)
assert decoded == text  # 100% reversible
```

### Example 2: Trace with Dictionary

```python
from fractalhub import Trace
from fractalhub.dictionary import get_dictionary

dictionary = get_dictionary()
trace = Trace()
trace.add_gate("G_SPEECH_ACT:001")
trace.add_prior_id("lexicon_ids", "SIGNIFIER:KITAB")
trace.add_prior_id("ruleset_ids", "SYNTAX:VERB_SUBJECT_AGREEMENT")

is_valid, errors = trace.validate()
```

### Example 3: Meaning with Provenance

```python
from fractalhub import MeaningCodec
from fractalhub.dictionary import get_dictionary

dictionary = get_dictionary()
codec = MeaningCodec()

# Get signified entry with provenance
book = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")

# Create meaning (requires trace and prior_ids)
meaning = codec.encode_meaning(
    concept=book['concept_en'],
    trace_id="C2:TRACE:abc123",
    prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
    provenance=book['provenance']
)
```

---

## ❓ FAQ

**Q: Why locked architecture?**  
A: Prevents hallucinations by requiring documented evidence for all meanings. Every concept must trace back through processing gates to dictionary entries.

**Q: What are the four conditions?**  
A: Al-Nabhani's cognition requirements:
- **Reality**: The form/data being processed
- **Brain**: The executor/processor
- **Sensing**: The channel/modality
- **Prior Knowledge**: Dictionary evidence (lexicon_ids, ruleset_ids)

**Q: How to validate?**  
A:
```bash
# Validate dictionary structure
python scripts/validate_dictionary.py

# Run all tests
pytest tests/ -v
```

---

## 🧪 Testing

```bash
# Run all tests
pytest

# Run specific test file
pytest tests/test_kernel_v12.py -v

# Run with coverage (requires pytest-cov)
pytest --cov=fractalhub --cov-report=html

# Validate dictionary
fractalhub-validate
```

---

## 📄 Documentation

- [ARCHITECTURE.md](docs/ARCHITECTURE.md) - Detailed system architecture
- [CONTRIBUTING.md](CONTRIBUTING.md) - Contribution guidelines
- [RELEASE_NOTES.md](RELEASE_NOTES.md) - Version history
- [LICENSE](LICENSE) - MIT License

---

## 🎯 Key Features

- ✅ **100% reversible form encoding** (FormCodec with checksum)
- ✅ **Locked architecture** preventing hallucinations
- ✅ **Bilingual dictionary** (Arabic/English)
- ✅ **Full provenance tracking** for all meanings
- ✅ **Four Conditions of Mind** enforcement
- ✅ **96 comprehensive tests** (all passing)

---

**Kernel**: v1.2 | **Dictionary**: v02 | **Tests**: 96/96 ✅

Last Updated: 2026-01-17
