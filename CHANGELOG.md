# Changelog

All notable changes to the FractalHub Consciousness Kernel will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.2.0] - 2026-01-17

### Added

#### Kernel v1.2
- **Version Metadata**: All records now include `kernel_version`, `architecture_version`, and `created_at_iso`
- **Enhanced TraceEntry Schema**:
  - `gate_latency_ms`: Track gate execution time
  - `evidence_strength`: Epistemic confidence (0.4-1.0)
  - `invariant_checks`: Dictionary of verified invariants
  - `four_conditions_verified`: Reality/Brain/Sensing/Prior checks
- **Executor Enhancements**:
  - Automatic evidence logging (lexicon_ids/ruleset_ids)
  - Four conditions verification before execution
  - Gate definition loading from dictionary
  - Evidence strength calculation
- **Entity Provenance**:
  - Full provenance tracking (source_type, confidence, attestation_count)
  - Signifier link validation (no orphaned meanings)
  - Trace pointer requirement (no C3 without C2)
  - Epistemic confidence methods
- **Evidence-Based Reasoning**:
  - Strict prior_ids requirement for all reasoning
  - Mode-specific epistemic strength (deductive=1.0, inductive/abductive=0.7, inferential=0.4)
  - Evidence chain propagation
  - Full reasoning trace creation

#### Dictionary v02
- **Bilingual Structure**: All entries now have Arabic and English fields
- **Provenance Schema**: Standardized metadata for all entries
  - source_type: corpus|grammar_book|expert_validation|derived
  - confidence: yaqin(1.0)|zann(0.7)|shakk(0.4)
  - attestation_count: corpus frequency
  - references: source citations
- **Lexicon Types**: Clear separation between signifier_only and signified_entity
- **Units Added**:
  - Core diacritics: FATHA, DAMMA, KASRA, SUKUN, SHADDA
  - Tanwin variants: TANWIN_FATH, TANWIN_DAMM, TANWIN_KASR
  - Prosody markers: WASL, WAQF, INTONATION_RISE, INTONATION_FALL
- **Gates Added**:
  - C1 layer: G_C1_CODEC_VERIFY, G_C1_DIACRITIC_ATTACH
  - C2 layer: G_C2_INVARIANTS
  - P layer: G_P1_DOUBLE_SUKUN, G_P2_WASL_BEGIN, G_P3_PROSODY_ASSIGN
  - C3 layer: G_C3_REFERENCE
- **Ruleset IDs**: All gates now reference evidence rulesets
- **Repair Operations**: REPLACE, INSERT_VIRTUAL, DELETE_VIRTUAL with evidence requirements
- **Evidence Levels**: YAQIN, ZANN, SHAKK with requirements
- **Anchor Rules**: NO_MEANING_WITHOUT_EVIDENCE, EVIDENCE_PROPAGATION

#### Tools & Infrastructure
- **Dictionary Loader**: `fractalhub.data.load_dictionary()` with v01/v02 support
- **Validation Script**: `scripts/validate_dictionary.py` with comprehensive checks
  - YAML syntax validation
  - Required fields checking
  - ID format conventions (U:, G_, INV:)
  - Provenance schema validation
  - Bilingual completeness checking
  - Duplicate ID detection
- **Test Suite**: Comprehensive tests for:
  - Kernel v1.2 components (Record, TraceEntry, TraceManager, Executor, Entity, Reasoner)
  - Dictionary loading (v01 and v02)
  - Backward compatibility
  - ID formats and schemas
- **Package Structure**: Proper Python package with setup.py

### Changed
- **Naming Conventions Audit**: Ensured consistency across:
  - Gates: `G_*` format (uppercase with underscore)
  - Units: `U:*` format (colon separator)
  - Invariants: `INV_*` format
  - Layers: C0, C1, C2, C3, P1, P2, P3

### Fixed
- None (initial release of v1.2)

### Security
- **Hallucination Prevention**: Locked architecture enforced through:
  - Four conditions verification
  - Evidence chain requirements
  - Signifier-signified separation
  - Trace validation

### Deprecated
- None

### Removed
- None

## [1.0.0] - 2026-01-01

### Added
- Initial stub v01 dictionary for backward compatibility testing

---

## Migration Guide

### From v01 to v02

No migration required! v02 maintains full backward compatibility with v01.

To use v02:
```python
from fractalhub.data import load_dictionary
dict_v02 = load_dictionary(version="v02")
```

To continue using v01:
```python
dict_v01 = load_dictionary(version="v01")
```

### Breaking Changes

**None**. Version 1.2.0 introduces new features while maintaining full backward compatibility.

---

## Versioning Policy

- **Major version** (X.0.0): Breaking changes to API or architecture
- **Minor version** (1.X.0): New features, backward compatible
- **Patch version** (1.2.X): Bug fixes, backward compatible

Current version: **1.2.0** (Minor release with new features, no breaking changes)
