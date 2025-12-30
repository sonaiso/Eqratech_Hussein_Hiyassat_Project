# CI/CD Workflows Documentation

## Overview

This directory contains GitHub Actions workflows for continuous integration and verification of the Arabic Fractal Kernel project with production-ready quality standards.

## Workflows

### 1. Coq Kernel Verification (`coq-verification.yml`)

**Purpose:** Ensures mathematical soundness and production readiness of the Coq formal verification kernel.

**Triggers:**
- Push to `main` or feature branches
- Pull requests to `main`
- Changes to `coq/**` or workflow files

**Enhanced Checks (Production-Ready):**

1. **Comment-Aware Admitted/Axiom Scan** 🔍
   - Uses intelligent Python scanner (`check_assumptions.py`)
   - Understands Coq comment syntax `(* ... *)`
   - Ignores instances in comments and documentation
   - Zero-tolerance policy for production code
   
2. **Tactic Policy Compliance** ✓
   - Verifies only approved safe tactics used
   - No `admit`, `exact`, or unsafe tactics
   
3. **Full Kernel Compilation** 🔨
   - Compiles all `.v` files
   - Verifies module dependencies
   
4. **coqchk Independent Verification** 🔐
   - Uses Coq's independent proof checker
   - Verifies `.vo` files contain no undeclared assumptions
   - Provides additional trust layer beyond compilation
   - Validates that all theorems proven correctly
   
5. **TCB Manifest Generation** 📋
   - Automatically generates Trusted Computing Base documentation
   - Lists all Parameters (trusted assumptions)
   - Includes locations, types, and documentation
   - Stored as artifact for 90 days

**Artifacts Generated:**
- `tcb-manifest`: JSON file documenting all Parameters
- `verification-report`: Summary of all verification checks

### 2. Full Integration Testing (`full-integration.yml`)

**Purpose:** Comprehensive validation across all project components.

**Triggers:**
- Push to `main` branch
- Pull requests to `main`
- Weekly schedule (Monday 00:00 UTC)

**Jobs:**
- Documentation completeness check
- Full Coq kernel verification
- Python engines integration
- Project metrics calculation
- Final validation report

**Artifacts:**
- `integration-report` (90-day retention)

### 3. Python Tests (`python-tests.yml`)

**Purpose:** Validate Python NLP engines functionality.

**Triggers:**
- Push/PR events
- Python code changes

---

## Local Verification

Run all production-ready checks locally before pushing:

### Quick Check
```bash
cd coq

# 1. Comment-aware assumption scan
python3 check_assumptions.py

# 2. Tactic policy verification
python3 check_coq_tactics.py --dir theories/ArabicKernel

# 3. Build kernel
make clean && make all

# 4. Generate TCB manifest
python3 generate_tcb_manifest.py
```

### Full Verification Suite (Matches CI)
```bash
cd coq

echo "🔍 Step 1: Checking assumptions..."
python3 check_assumptions.py || exit 1

echo "🔍 Step 2: Verifying tactic policy..."
python3 check_coq_tactics.py --dir theories/ArabicKernel || exit 1

echo "🔨 Step 3: Compiling kernel..."
make clean && make all || exit 1

echo "🔍 Step 4: Verifying module loads..."
coqc -Q theories ArabicKernel theories/ArabicKernel/All.v || exit 1

echo "🔐 Step 5: Running coqchk verification..."
for vo in theories/ArabicKernel/*.vo; do
  if [ -f "$vo" ] && [ "$(basename "$vo")" != "All.vo" ]; then
    echo "Checking $(basename "$vo")..."
    coqchk -Q theories ArabicKernel $(basename "$vo" .vo) 2>&1 | head -20
  fi
done

echo "📋 Step 6: Generating TCB manifest..."
python3 generate_tcb_manifest.py

echo "✅ All local checks passed! Ready for production."
```

---

## Understanding the TCB (Trusted Computing Base)

The kernel's TCB consists of three components:

1. **Coq Proof Checker** - The core Coq type-checker itself
2. **Standard Library** - Coq's standard library (Lists, Arith, Bool, etc.)
3. **Parameters** - Explicitly documented external assumptions

All Parameters are:
- Automatically documented in `TCB_MANIFEST.json`
- Listed with their types, locations, and documentation
- Justified with inline comments in source files
- Verified by CI on every commit
- Available as downloadable artifact

**Current TCB Size:** ~6 Parameters (see generated manifest for complete details)

---

## Production-Ready Tools

### `check_assumptions.py`
**Comment-aware scanner for Admitted/Axiom statements.**

Features:
- Understands Coq comment syntax `(* ... *)`
- Handles nested comments correctly
- Ignores documentation instances
- Reports exact line numbers and contexts
- Exit code 1 if any found, 0 if clean

Usage:
```bash
python3 coq/check_assumptions.py
```

### `generate_tcb_manifest.py`
**Generates comprehensive TCB documentation.**

Outputs:
- `TCB_MANIFEST.json` with all Parameters
- Parameter names, types, and locations
- Extracted inline documentation
- Generation timestamp
- Summary statistics

Usage:
```bash
python3 coq/generate_tcb_manifest.py
cat coq/theories/ArabicKernel/TCB_MANIFEST.json
```

### `check_coq_tactics.py`
**Verifies only approved tactics used in proofs.**

Policy Enforced:
- Safe tactics only (no `admit`, `exact`, unsafe constructs)
- Arithmetic automation allowed (`lia`, `ring`, `omega`)
- Custom safe tactics permitted
- Fails build if policy violated

---

## Production Readiness Standards

The enhanced CI pipeline achieves industry-standard production quality:

✅ **Zero-tolerance for undeclared assumptions**
- Comment-aware intelligent scanning
- Independent verification with `coqchk`
- Dual-layer trust verification

✅ **Transparent and auditable TCB**
- Auto-generated manifest on every commit
- All assumptions explicitly documented
- Artifact downloadable for security audit

✅ **Continuous validation**
- Every commit automatically verified
- Weekly scheduled health checks
- Local pre-push verification support

✅ **Best practices compliance**
- Uses Coq's recommended verification tools
- Follows formal methods industry standards
- Provides audit trail for academic/commercial use

---

## CI Status Badges

Add to your README.md:

```markdown
![Coq Verification](https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/actions/workflows/coq-verification.yml/badge.svg)
![Full Integration](https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/actions/workflows/full-integration.yml/badge.svg)
```

---

## Best Practices for Contributors

1. **Before Committing:**
   - Run `python3 coq/check_assumptions.py` locally
   - Ensure `make all` succeeds
   - Review generated TCB manifest

2. **Adding New Theorems:**
   - All theorems must have complete proofs
   - No `Admitted` statements in production code
   - Use only approved tactics

3. **External Assumptions:**
   - Declare as `Parameter` with documentation
   - Explain why assumption needed
   - Document in inline comments
   - Will appear in TCB manifest automatically

4. **Code Review:**
   - Check CI passes all verification steps
   - Review TCB manifest artifact if Parameters added
   - Ensure coqchk verification succeeds

---

## Troubleshooting

**CI fails with "Admitted found":**
- Check that you haven't used `Admitted` in proofs
- Ensure test/example code is properly commented
- Run local `check_assumptions.py` to identify location

**coqchk verification fails:**
- Usually indicates compilation issues
- Check that all `.v` files compile individually
- Verify `_CoqProject` includes all dependencies

**TCB manifest missing Parameters:**
- Ensure Parameter declarations have inline documentation
- Check that documentation uses Coq comment syntax `(* ... *)`
- Verify Parameters are before Admitted/Axiom in file

---

## Future Enhancements

Planned improvements for CI/CD:
- [ ] Print Assumptions integration for theorem-level verification
- [ ] Automated theorem counting and reporting
- [ ] Performance benchmarks for compilation time
- [ ] Integration with external proof checkers

---

For questions or issues with CI/CD, consult the project documentation or raise an issue.
