# Eqratech_Arabic_Diana_Project
Python_NLP Project with all Arabic tools verbs and names

## Features

### View Today's Activities
You can now view all available Arabic grammar engines through a web interface!

**To start the web server:**
```bash
python run_server.py
```

Then open your browser and navigate to: `http://127.0.0.1:8000/`

**API Endpoint:**
- GET `/api/activities` - Returns JSON data with today's date and all available engines

**What you'll see:**
- Today's date
- Total count of available grammar activities (63 engines)
- List of all Arabic grammar engines with their Arabic names
- Beautiful, responsive interface in both Arabic and English

## Installation

Install dependencies:
```bash
pip install -r requirements.txt
```

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
