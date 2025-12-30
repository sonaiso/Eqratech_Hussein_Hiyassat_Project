# CI/CD Pipeline Configuration

This directory contains GitHub Actions workflows for automated verification and continuous integration of the Eqratech Arabic Diana Project.

## Workflows

### 1. Coq Kernel Verification (`coq-verification.yml`)

**Purpose**: Verify the mathematical soundness of the Coq formal verification kernel.

**Triggers**:
- Push to `main` or `copilot/update-project-description` branches
- Pull requests to `main`
- Only when Coq files change

**Jobs**:

#### `verify-kernel`
- Installs Coq compiler
- Checks for `Admitted` statements (must be 0)
- Checks for `Axiom` statements (must be 0)
- Verifies tactic policy compliance
- Compiles entire Coq kernel
- Verifies all modules load correctly
- Generates verification report

#### `check-parameters`
- Validates that all `Parameter` declarations are documented
- Counts parameters and warns if excessive

#### `integration-check`
- Tests Python-Coq bridge functionality
- Verifies project structure
- Ensures critical files exist

#### `security-audit`
- Audits kernel for unsafe tactics
- Verifies trust boundary implementation
- Generates security report

**Expected Results**:
- ✅ 0 Admitted statements
- ✅ 0 Axiom statements  
- ✅ 6 Parameters (all documented)
- ✅ 41/41 theorems proven (100%)
- ✅ All safe tactics only

---

### 2. Full Project Integration (`full-integration.yml`)

**Purpose**: Comprehensive integration testing across all project components.

**Triggers**:
- Push to `main` branch
- Pull requests to `main`
- Weekly schedule (Monday 00:00 UTC)

**Jobs**:

#### `documentation-check`
- Validates presence of all documentation files
- Checks for broken links
- Ensures bilingual documentation exists

#### `coq-verification`
- Full kernel verification
- Theorem counting and statistics
- Validates 100% proof coverage

#### `python-integration`
- Tests Python NLP engines
- Validates Python-Coq bridge
- Ensures all engines load correctly

#### `project-metrics`
- Calculates code statistics
- Counts Python files and lines
- Counts Coq files and theorems
- Measures documentation coverage

#### `final-validation`
- Aggregates all test results
- Generates comprehensive integration report
- Declares production readiness status

---

### 3. Python Tests (`python-tests.yml`)

**Purpose**: Test Python NLP engines (existing workflow).

**Triggers**:
- Push/PR to `main`

**Jobs**:
- Runs pytest across Python 3.10, 3.11, 3.12
- Tests Python engine functionality

---

## Status Badges

Add these badges to your README.md:

```markdown
![Coq Verification](https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/actions/workflows/coq-verification.yml/badge.svg)
![Full Integration](https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/actions/workflows/full-integration.yml/badge.svg)
![Python Tests](https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/actions/workflows/python-tests.yml/badge.svg)
```

---

## Artifacts

Each workflow generates artifacts that are retained for analysis:

### Coq Verification Artifacts
- `coq-verification-report.md` (30 days retention)
  - Build status
  - Verification summary
  - Commit and version info

### Integration Artifacts
- `full-integration-report.md` (90 days retention)
  - Comprehensive test results
  - Production readiness status
  - All component validations

---

## Local Testing

Before pushing, you can run these checks locally:

### Coq Verification
```bash
cd coq
python3 check_coq_tactics.py --dir theories/ArabicKernel
make clean && make all
```

### Check for Admitted/Axiom
```bash
grep -r "Admitted\." coq/theories/ArabicKernel/*.v | grep -v "(\*"
grep -r "^Axiom " coq/theories/ArabicKernel/*.v
```

### Python Tests
```bash
pytest -q
```

---

## Failure Scenarios

### If Coq Verification Fails

1. **Admitted found**: Remove all `Admitted` statements and complete proofs
2. **Axiom found**: Convert to `Parameter` with clear documentation
3. **Tactic policy violation**: Use only approved safe tactics
4. **Compilation error**: Fix Coq syntax/type errors

### If Integration Fails

1. **Missing files**: Ensure all critical files are committed
2. **Python bridge error**: Check `coq_bridge.py` functionality
3. **Documentation missing**: Add missing doc files

---

## Continuous Improvement

The CI/CD pipeline enforces:

✅ **Zero-tolerance policy** for `Admitted` and `Axiom`  
✅ **100% proof coverage** requirement  
✅ **Safe tactics only** enforcement  
✅ **Complete documentation** validation  
✅ **Integration testing** across all components  

This ensures the project remains **academically defensible** and **production-ready** at all times.

---

## Maintenance

Weekly scheduled runs ensure:
- No regressions over time
- Documentation stays current
- All integrations remain functional
- Metrics are tracked continuously
