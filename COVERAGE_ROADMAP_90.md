# خارطة طريق الوصول لتغطية 90% | Roadmap to 90% Coverage

**التاريخ | Date**: 2026-02-04  
**الحالة | Status**: Phase 1 Complete (58% coverage achieved)  
**الهدف | Target**: 90%+ coverage in 2-3 weeks

---

## 📊 Current Progress | التقدم الحالي

### Phase 1: Integration & Edge Cases ✅ COMPLETE
**Duration**: 2 days  
**Coverage**: 46% → 58% (+12%)  
**Tests Added**: 62 tests (100% passing)

#### What Was Done:
1. ✅ Created `tests/test_integration/` directory (36 tests)
   - Pipeline integration tests
   - Engine interaction tests
   - Layer-to-layer data flow validation

2. ✅ Created `tests/edge_cases/` directory (26 tests)
   - Null/empty input handling
   - Unicode edge cases
   - Boundary conditions
   - Concurrent access patterns
   - Error recovery

3. ✅ Validated all engines work together
   - Phonology → Morphology → Syntax → Generation
   - Cross-layer data consistency
   - Parallel processing capability

#### Key Achievements:
- Integration module now 100% covered
- FVAFK gates 85-100% covered
- Morphological components 83-96% covered
- All 564 tests passing (100% pass rate)

---

## 🎯 Remaining Phases | المراحل المتبقية

### Phase 2: Verbose Path Coverage (+15%) [Days 3-9]
**Target**: 58% → 73% coverage  
**Timeline**: 5-7 days  
**Status**: ⏳ Next

#### Tasks:
- [ ] 2.1 Test verbose output in all FVAFK components
  - C1 encoding verbose mode
  - C2a gate verbose output
  - C2b morphology verbose analysis
  
- [ ] 2.2 Test alternative code paths in engines
  - Different input patterns
  - Edge cases in make_df()
  - Metadata generation paths
  
- [ ] 2.3 Test gate repair mechanisms
  - Sukun gate repairs
  - Shadda gate repairs
  - Hamza normalization
  - Idgham assimilation
  
- [ ] 2.4 Test optimization algorithms
  - Vowel space optimization
  - Energy minimization
  - Syllabifier alternatives
  
- [ ] 2.5 Test CSV loading variations
  - Different CSV formats
  - Missing columns
  - Encoding variations
  
- [ ] 2.6 Test reconstruction_utils paths
  - Phoneme map loading
  - Harakat map loading
  - Unicode generation
  - UTF-8 generation

#### Files to Focus On:
```
src/fvafk/cli/main.py                  34% → 80%  (+46%)
src/fvafk/energy_evaluation.py        48% → 75%  (+27%)
src/fvafk/particle_loader.py          61% → 85%  (+24%)
src/fvafk/vowel_space_optimization.py 76% → 90%  (+14%)
src/syntax_theory/generators/         52-58% → 75-85%
src/syntax_theory/minimizers/         62% → 80%
```

**Expected New Tests**: ~40 tests  
**Estimated Time**: 5-7 days

---

### Phase 3: Theory & Generators (+15%) [Days 10-12]
**Target**: 73% → 88% coverage  
**Timeline**: 2-3 days  
**Status**: 📝 Planned

#### Tasks:
- [ ] 3.1 Test theory.phonetic_space components
  - ConsonantSpace
  - VowelSpace
  - FeatureSpace operations
  
- [ ] 3.2 Test theory.minimizers
  - VowelOptimizer
  - SyllableEnergy
  - Optimization algorithms
  
- [ ] 3.3 Test theory.proofs
  - Existence and uniqueness theorems
  - Formal verification
  
- [ ] 3.4 Test FVAFK CLI in detail
  - All command line options
  - JSON output
  - Verbose modes
  - Error messages
  
- [ ] 3.5 Test parameter_learning
  - Feature learning
  - Weight optimization
  
- [ ] 3.6 Test generative_plurals
  - Plural pattern generation
  - Root transformations

#### Files to Focus On:
```
src/theory/phonetic_space/feature_space.py    0% → 80%  (+80%)
src/theory/phonetic_space/projection.py       0% → 80%  (+80%)
src/theory/minimizers/optimizer.py            0% → 75%  (+75%)
src/theory/minimizers/syllable_energy.py      0% → 75%  (+75%)
src/theory/proofs/existence_uniqueness.py     0% → 70%  (+70%)
src/fvafk/generative_plurals.py               0% → 60%  (+60%)
src/fvafk/parameter_learning.py               0% → 60%  (+60%)
src/fvafk/cli/__main__.py                     0% → 80%  (+80%)
```

**Expected New Tests**: ~35 tests  
**Estimated Time**: 2-3 days

**Note**: These components require scipy. Install with:
```bash
pip install scipy hypothesis
```

---

### Phase 4: Final Push (+2%) [Days 13-14]
**Target**: 88% → 90%+ coverage  
**Timeline**: 1-2 days  
**Status**: 🎯 Goal

#### Tasks:
- [ ] 4.1 Run coverage report to identify gaps
  ```bash
  pytest --cov=src --cov-report=html --cov-report=term-missing
  ```
  
- [ ] 4.2 Add targeted tests for uncovered lines
  - Exception handlers
  - Edge cases in conditionals
  - Rarely used code paths
  
- [ ] 4.3 Test generation engines (if refactored)
  - SentenceGenerationEngine
  - EnhancedSentenceGenerationEngine
  - StaticSentenceGenerator
  
- [ ] 4.4 Complete documentation
  - Update README with test instructions
  - Document test patterns
  - Add examples
  
- [ ] 4.5 Final verification
  - All tests passing
  - 90%+ coverage achieved
  - No regressions

**Expected New Tests**: ~15 tests  
**Estimated Time**: 1-2 days

---

## 📈 Coverage Projection

```
Current:  58% ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Phase 2:  73% ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Phase 3:  88% ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Target:   90% ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| Phase | Coverage | Tests | Days | Status |
|-------|----------|-------|------|--------|
| Baseline | 46% | 502 | - | ✅ Done |
| Phase 1 | 58% | 564 | 2 | ✅ Done |
| Phase 2 | 73% | 604 | 5-7 | ⏳ Next |
| Phase 3 | 88% | 639 | 2-3 | 📝 Planned |
| Phase 4 | 90%+ | 654+ | 1-2 | 🎯 Goal |

**Total Time**: 10-14 days (1.5-2 weeks)

---

## 🛠️ Tools & Commands

### Run All Tests
```bash
pytest tests/ -v
```

### Run Specific Test Suite
```bash
pytest tests/test_integration/ -v        # Integration tests
pytest tests/edge_cases/ -v              # Edge case tests
pytest tests/engines/ -v                 # Engine tests
```

### Measure Coverage
```bash
# Terminal output
pytest --cov=src --cov-report=term-missing

# HTML report
pytest --cov=src --cov-report=html
# Then open: htmlcov/index.html

# Both
pytest --cov=src --cov-report=term-missing --cov-report=html
```

### Coverage by Module
```bash
pytest --cov=src/engines --cov-report=term
pytest --cov=src/fvafk --cov-report=term
pytest --cov=src/integration --cov-report=term
pytest --cov=src/syntax_theory --cov-report=term
pytest --cov=src/theory --cov-report=term
```

### Run Specific Test Class
```bash
pytest tests/test_integration/test_pipeline_integration.py::TestArabicNLPPipeline -v
```

### Run with Coverage and Stop on First Failure
```bash
pytest --cov=src --cov-report=term -x
```

---

## 📋 Test Organization

### Current Structure
```
tests/
├── test_integration/        # Integration tests (36 tests)
│   ├── test_pipeline_integration.py
│   └── test_engine_interactions.py
├── edge_cases/              # Edge case tests (26 tests)
│   └── test_error_handling.py
├── engines/                 # Engine unit tests (502 tests)
│   ├── phonology/
│   ├── morphology/
│   ├── lexicon/
│   ├── syntax/
│   ├── rhetoric/
│   └── generation/
├── c2b/                     # C2b morphology tests
│   ├── test_root_extractor.py
│   ├── test_pattern_matcher.py
│   └── test_morpheme_structures.py
├── test_gate_*.py           # Phonological gate tests
├── test_syllable.py         # Syllable tests
├── test_syntax_theory.py    # Syntax theory tests
└── ...                      # Other existing tests
```

### Planned Additions
```
tests/
├── test_integration/        # Add ~10 more tests
├── edge_cases/              # Add ~10 more tests
├── verbose_paths/           # NEW: Phase 2 (~40 tests)
│   ├── test_verbose_output.py
│   ├── test_alternative_paths.py
│   └── test_optimization_paths.py
├── theory/                  # NEW: Phase 3 (~35 tests)
│   ├── test_phonetic_space.py
│   ├── test_minimizers.py
│   ├── test_proofs.py
│   └── test_projections.py
└── cli/                     # NEW: Phase 3 (~10 tests)
    ├── test_cli_commands.py
    └── test_cli_options.py
```

---

## 🎯 Success Criteria

### Phase 1 ✅
- [x] 62 new tests added
- [x] All tests passing (100%)
- [x] Coverage increased by 12%
- [x] Integration infrastructure established

### Phase 2 (Target)
- [ ] 40+ new tests added
- [ ] All tests passing (100%)
- [ ] Coverage increased to 73%
- [ ] Verbose paths covered

### Phase 3 (Target)
- [ ] 35+ new tests added
- [ ] Theory components tested
- [ ] Coverage increased to 88%
- [ ] CLI fully tested

### Phase 4 (Goal)
- [ ] 90%+ coverage achieved
- [ ] 650+ tests total
- [ ] Complete documentation
- [ ] Project rating: 9.0/10+

---

## 💡 Best Practices

### Test Writing Guidelines

1. **Use Descriptive Names**
   ```python
   def test_engine_handles_empty_input_gracefully():
       # Clear what is being tested
   ```

2. **One Assertion Per Test (Mostly)**
   ```python
   def test_pipeline_returns_success():
       result = pipeline.process("كتب")
       assert result['success'] is True
   ```

3. **Use Fixtures for Common Setup**
   ```python
   @pytest.fixture
   def pipeline():
       return ArabicNLPPipeline()
   ```

4. **Skip Unavailable Components**
   ```python
   try:
       from engines.morphology import ActiveParticipleEngine
   except ImportError:
       pytest.skip("Engine not available")
   ```

5. **Test Edge Cases**
   - Empty inputs
   - Null values
   - Very large inputs
   - Unicode variations
   - Concurrent access

6. **Use Parameterized Tests**
   ```python
   @pytest.mark.parametrize("root", ["كتب", "ذهب", "أكل"])
   def test_multiple_roots(root):
       result = pipeline.process(root)
       assert result['success'] is True
   ```

### Coverage Guidelines

1. **Aim for 100% on New Code**
2. **Prioritize Critical Paths**
3. **Don't Skip Error Handlers**
4. **Test Alternative Branches**
5. **Include Performance Tests**

---

## 📊 Current Coverage by Component

### High Coverage (80%+)
- ✅ src/integration: 100%
- ✅ src/fvafk/orthography_adapter: 100%
- ✅ src/fvafk/c2a/gates/gate_tanwin: 100%
- ✅ src/fvafk/c2a/gates/gate_waqf: 97%
- ✅ src/fvafk/c2a/syllable: 98%
- ✅ src/fvafk/c2b/morpheme: 96%
- ✅ src/fvafk/c2b/root_extractor: 96%
- ✅ src/syntax_theory/structures/graph_structure: 92%

### Medium Coverage (50-79%)
- 🟡 src/fvafk/vowel_space_optimization: 76%
- 🟡 src/syntax_theory/proofs/selection_theorem: 77%
- 🟡 src/syntax_theory/operators/operator_signatures: 74%
- 🟡 src/syntax_theory/relations/relation_builder: 69%
- 🟡 src/fvafk/particle_loader: 61%
- 🟡 src/syntax_theory/minimizers/syntactic_energy: 62%

### Low Coverage (0-49%)
- 🔴 src/theory/*: 0% (needs scipy)
- 🔴 src/fvafk/generative_plurals: 0%
- 🔴 src/fvafk/parameter_learning: 0%
- 🔴 src/fvafk/cli/main: 34%
- 🔴 src/fvafk/energy_evaluation: 48%
- 🔴 src/fvafk/c2b/awzan_loader: 39%

---

## 🚀 Getting Started with Phase 2

### Step 1: Set Up Environment
```bash
cd /path/to/Eqratech_Hussein_Hiyassat_Project
pip install pytest pytest-cov scipy hypothesis
```

### Step 2: Create Test Directory
```bash
mkdir -p tests/verbose_paths
touch tests/verbose_paths/__init__.py
```

### Step 3: Start with CLI Tests
```python
# tests/verbose_paths/test_cli_verbose.py
import pytest
from fvafk.cli.main import main

def test_cli_with_verbose_flag():
    # Test CLI verbose mode
    pass

def test_cli_with_json_output():
    # Test JSON output format
    pass
```

### Step 4: Run and Measure
```bash
pytest tests/verbose_paths/ --cov=src/fvafk/cli --cov-report=term-missing
```

### Step 5: Iterate
- Add tests for uncovered lines
- Focus on alternative branches
- Test error conditions
- Measure coverage improvement

---

## 📞 Support & Resources

### Documentation
- [pytest documentation](https://docs.pytest.org/)
- [pytest-cov documentation](https://pytest-cov.readthedocs.io/)
- Project README
- IMPLEMENTATION_ROADMAP.md

### Coverage Reports
- HTML Report: `htmlcov/index.html`
- Terminal: `pytest --cov=src --cov-report=term-missing`
- JSON: `pytest --cov=src --cov-report=json`

### Test Examples
- Look at existing tests in `tests/test_integration/`
- Follow patterns in `tests/edge_cases/`
- Reference engine tests in `tests/engines/`

---

## 🎉 Conclusion

We're on track to reach 90% coverage! With Phase 1 complete (58% achieved), we have:

✅ Solid foundation (integration + edge cases)  
✅ Clear roadmap for remaining phases  
✅ Proven testing patterns  
✅ High confidence in reaching goal

**Next Action**: Begin Phase 2 (Verbose Path Coverage)  
**Timeline**: 10-14 days to completion  
**Confidence**: High ✅

والله الموفق 🚀

---

**Document Version**: 1.0  
**Last Updated**: 2026-02-04  
**Author**: GitHub Copilot Coding Agent  
**Status**: Active Roadmap
