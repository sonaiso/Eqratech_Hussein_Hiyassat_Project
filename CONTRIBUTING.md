# Contributing to FractalHub

Thank you for your interest in contributing to FractalHub! This document provides guidelines and instructions for contributing.

## Code of Conduct

Please be respectful and professional in all interactions. We aim to maintain a welcoming and inclusive environment.

## Getting Started

### Development Setup

1. **Clone the repository**
   ```bash
   git clone https://github.com/sonaiso/Eqratech_Arabic_Diana_Project.git
   cd Eqratech_Arabic_Diana_Project
   ```

2. **Create a virtual environment**
   ```bash
   python -m venv .venv
   source .venv/bin/activate  # On Windows: .venv\Scripts\activate
   ```

3. **Install in development mode**
   ```bash
   pip install -e ".[dev]"
   ```

4. **Run tests**
   ```bash
   pytest tests/ -v
   ```

## Project Structure

```
Eqratech_Arabic_Diana_Project/
├── fractalhub/               # Main package
│   ├── kernel/              # Core kernel modules
│   ├── dictionary/          # Dictionary loader and validator
│   ├── data/               # Data files (YAML dictionaries)
│   └── cli.py              # Command-line interface
├── tests/                   # Test suite
├── scripts/                 # Utility scripts
├── docs/                    # Documentation
├── pyproject.toml          # Modern package configuration
├── setup.py                # Backward-compatible setup
├── README.md               # Project documentation
└── RELEASE_NOTES.md        # Version history
```

## Development Workflow

### Making Changes

1. **Create a feature branch**
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**
   - Follow the coding style (see below)
   - Add tests for new functionality
   - Update documentation as needed

3. **Run tests**
   ```bash
   pytest tests/ -v
   ```

4. **Format code**
   ```bash
   black fractalhub/ tests/
   isort fractalhub/ tests/
   ```

5. **Validate dictionary (if changed)**
   ```bash
   python scripts/validate_dictionary.py
   ```

6. **Commit changes**
   ```bash
   git add .
   git commit -m "feat: description of changes"
   ```

### Commit Message Format

Use conventional commits format:
- `feat:` - New features
- `fix:` - Bug fixes
- `docs:` - Documentation changes
- `test:` - Test changes
- `refactor:` - Code refactoring
- `style:` - Code style changes
- `chore:` - Maintenance tasks

Examples:
```
feat(kernel): add new gate type for temporal reasoning
fix(dictionary): correct provenance validation logic
docs: update README with new examples
test: add integration tests for meaning codec
```

## Coding Standards

### Python Style

- **Line length**: 100 characters maximum
- **Formatting**: Use `black` and `isort`
- **Type hints**: Use type hints for all public APIs
- **Docstrings**: Use docstrings with examples for all public functions/classes

Example:
```python
def encode_meaning(
    self,
    concept: str,
    trace_id: str,
    prior_ids: Dict[str, List[str]],
    provenance: List[Dict]
) -> Dict[str, Any]:
    """
    Encode meaning with full provenance.
    
    Args:
        concept: The meaning/concept
        trace_id: Required C2 trace
        prior_ids: Dictionary evidence
        provenance: Source information
        
    Returns:
        Encoded meaning object
        
    Raises:
        ValueError: If trace_id or prior_ids missing
        
    Example:
        >>> codec = MeaningCodec()
        >>> meaning = codec.encode_meaning(
        ...     concept="book",
        ...     trace_id="C2:TRACE:abc123",
        ...     prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
        ...     provenance=[{"source_id": "CLASSICAL_CORPUS", "confidence": 1.0}]
        ... )
    """
```

### Testing

- **Coverage**: Aim for >95% test coverage
- **Test types**: Unit tests, integration tests, property-based tests
- **Naming**: Test files start with `test_`, test functions start with `test_`
- **Organization**: Group related tests in classes

Example:
```python
class TestMeaningCodec:
    """Test MeaningCodec for C3 layer."""
    
    def test_encode_meaning_success(self):
        """Test encoding meaning with provenance."""
        codec = MeaningCodec()
        meaning = codec.encode_meaning(...)
        assert meaning['layer'] == 'C3'
    
    def test_encode_meaning_no_trace(self):
        """Test encoding fails without trace (NO C3 without C2)."""
        with pytest.raises(ValueError) as exc_info:
            codec.encode_meaning(concept="test", trace_id="", ...)
        assert "no meaning without c2 trace" in str(exc_info.value).lower()
```

## Architecture Principles

### Locked Architecture

The FractalHub architecture enforces strict constraints to prevent hallucinations:

1. **NO C3 without C2 trace** - No meaning without documented gate passage
2. **NO C2 without C1 four conditions** - Gates must verify Reality/Brain/Sensing/Prior Knowledge
3. **NO meaning without prior_ids** - Evidence required from dictionary
4. **Strict layer separation** - C1 (form) ↔ C2 (gates) ↔ C3 (meaning)

**These constraints are immutable** - any change that violates them will be rejected.

### Adding New Features

When adding features:

1. **Maintain locked architecture** - Ensure constraints are preserved
2. **Add provenance** - All new dictionary entries need provenance
3. **Document gates** - New gates must document four conditions
4. **Add tests** - Comprehensive tests for all new functionality
5. **Update documentation** - Keep README and RELEASE_NOTES current

## Pull Request Process

1. **Ensure all tests pass**
   ```bash
   pytest tests/ -v
   ```

2. **Validate dictionary**
   ```bash
   python scripts/validate_dictionary.py
   ```

3. **Check code quality**
   ```bash
   black --check fractalhub/ tests/
   isort --check fractalhub/ tests/
   ```

4. **Update documentation**
   - Update README.md if adding user-facing features
   - Update RELEASE_NOTES.md with changes
   - Add/update docstrings

5. **Create pull request**
   - Provide clear description of changes
   - Reference any related issues
   - Include test results
   - List breaking changes (if any)

6. **Code review**
   - Address reviewer comments
   - Make requested changes
   - Keep discussion focused and professional

## Dictionary Contributions

When contributing to the dictionary:

### Adding Lexicon Entries

1. **Signifier entries (C1)** - Form only, no meaning
   ```yaml
   SIGNIFIER:EXAMPLE:
     entry_id: "SIGNIFIER:EXAMPLE"
     entry_type: "signifier"
     layer: "C1"
     form: "مثال"
     form_ar: "مثال"
     form_en: "example"
     features: ["noun", "masculine"]
     phonetic: "/miθaːl/"
     provenance:
       - source_id: "CLASSICAL_CORPUS"
         confidence: 1.0
     status: "active"
   ```

2. **Signified entries (C3)** - Meaning only, no form
   ```yaml
   SIGNIFIED:EXAMPLE:EXAMPLE:
     entry_id: "SIGNIFIED:EXAMPLE:EXAMPLE"
     entry_type: "signified"
     layer: "C3"
     concept_ar: "مثال"
     concept_en: "example"
     semantic_features: ["instance", "illustration"]
     ontology_type: "ENTITY"
     provenance:
       - source_id: "CLASSICAL_CORPUS"
         confidence: 1.0
     linked_signifiers: ["SIGNIFIER:EXAMPLE"]
     status: "active"
   ```

3. **Validate**
   ```bash
   python scripts/validate_dictionary.py
   ```

## Questions?

- Open an issue for questions or discussions
- Check existing issues and documentation first
- Be specific about your question or problem

## License

By contributing, you agree that your contributions will be licensed under the MIT License.
