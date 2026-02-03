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

### Web API

#### Starting the Server

```bash
# Start the FastAPI server
python run_server.py

# With custom host and port
python run_server.py --host 0.0.0.0 --port 8080

# With auto-reload for development
python run_server.py --reload
```

#### API Endpoints

Once the server is running, you can access:

- **Interactive Documentation**: http://localhost:8000/docs
- **Health Check**: http://localhost:8000/
- **Text Analysis**: POST http://localhost:8000/analyze
- **Morphological Analysis**: POST http://localhost:8000/analyze/morphology

Example API usage:

```bash
# Basic analysis
curl -X POST http://localhost:8000/analyze \
  -H "Content-Type: application/json" \
  -d '{"text": "كِتَابٌ"}'

# With morphology
curl -X POST http://localhost:8000/analyze/morphology \
  -H "Content-Type: application/json" \
  -d '{"text": "كَاتِبٌ"}'
```

See [web_app/README.md](web_app/README.md) for complete API documentation.
