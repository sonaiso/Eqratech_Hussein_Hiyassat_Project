A production-ready Arabic NLP system implementing a three-phase computational model for Arabic text processing: encoding (C1), phonological analysis (C2a), and morphological analysis (C2b).

---

## 🎯 Overview

This project implements a comprehensive Arabic language processing pipeline capable of:

- **Text Normalization**: Unicode normalization and orthographic standardization
- **Phonological Processing**: 10 Tajweed-based gates for accurate phonetic analysis
- **Morphological Analysis**: Root extraction and pattern matching for Arabic words
- **High Performance**: Sub-millisecond processing (<0.5ms per word)
- **Production Ready**: 101 comprehensive tests (100% passing)

---

## ✨ Features

### Phase 1 (C1): Text Encoding & Normalization
- Unicode normalization (NFC/NFD)
- Diacritic preservation
- Character encoding standardization
- Orthographic adaptation

### Phase 2 (C2a): Phonological Gates (Tajweed Rules)
1. **GateSukun**: Double sukun repair
2. **GateShadda**: Gemination expansion
3. **GateHamza**: Hamza placement rules
4. **GateWaqf**: Pause and stop rules
5. **GateIdgham**: Assimilation with ghunnah
6. **GateMadd**: Vowel lengthening
7. **GateDeletion**: Alif/hamza deletion
8. **GateEpenthesis**: Vowel insertion

### Phase 3 (C2b): Morphological Analysis
- **Root Extraction**: Trilateral and quadrilateral roots
- **Pattern Matching**: 25+ morphological templates
- **Verb Forms**: Recognition of Forms I-X
- **Weak Roots**: Special handling for و, ي, ء
- **Noun Patterns**: Singular, plural, broken plurals
- **Participles**: Active and passive forms

---

## 🚀 Installation

### Prerequisites
- Python 3.8+
- pip

### Setup

```bash
# Clone the repository
git clone https://github.com/sonaiso/Eqratech_Hussein_Hiyassat_Project.git
cd Eqratech_Hussein_Hiyassat_Project

# Create virtual environment
python3 -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Run tests to verify installation
PYTHONPATH=src pytest tests/ -v
```

---

## 💻 Usage

### Command Line Interface

#### Basic Usage

```bash
# Simple text analysis
python -m fvafk.cli "كَاتِبٌ"

# With morphological analysis
python -m fvafk.cli "كَاتِبٌ" --morphology

# JSON output
python -m fvafk.cli "كَاتِبٌ" --morphology --json

# Verbose output with timing
python -m fvafk.cli "كَاتِبٌ" --morphology --verbose
```

### Python API

```python
import sys
sys.path.insert(0, 'src')

from fvafk.orthography_adapter import OrthographyAdapter
from fvafk.c2b.root_extractor import RootExtractor
from fvafk.c2b.pattern_matcher import PatternMatcher

# Initialize components
adapter = OrthographyAdapter()
extractor = RootExtractor()
matcher = PatternMatcher()

# Analyze word
text = "كَاتِبٌ"
normalized = adapter.normalize(text)
root = extractor.extract(normalized)
pattern = matcher.match(normalized, root)

print(f"Root: {'-'.join(root.letters)}")      # ك-ت-ب
print(f"Pattern: {pattern.name}")              # فَاعِل
print(f"Type: {pattern.pattern_type.name}")   # ACTIVE_PARTICIPLE
```

---

## 📚 Documentation

Comprehensive documentation is available in the `docs/` directory:

- **[Architecture Overview](docs/ARCHITECTURE.md)** - System design and three-phase pipeline (C1→C2a→C2b)
- **[Phonological Gates Reference](docs/PHONOLOGICAL_GATES.md)** - Detailed specifications of all 10 Tajweed-based gates
- **[Morphology Guide](docs/MORPHOLOGY_GUIDE.md)** - Root extraction, pattern matching, and Arabic morphological patterns
- **[API Reference](docs/API_REFERENCE.md)** - Complete API documentation with examples
- **[Tutorial](docs/TUTORIAL.md)** - Step-by-step tutorials and common recipes
- **[Implementation Status](docs/implementation_status.md)** - Current implementation status and roadmap

### Quick Links

- **New to FVAFK?** Start with the [Tutorial](docs/TUTORIAL.md)
- **Want to understand the system?** Read the [Architecture Overview](docs/ARCHITECTURE.md)
- **Looking for specific APIs?** Check the [API Reference](docs/API_REFERENCE.md)
- **Need gate details?** See [Phonological Gates Reference](docs/PHONOLOGICAL_GATES.md)
- **Working with morphology?** Read the [Morphology Guide](docs/MORPHOLOGY_GUIDE.md)
