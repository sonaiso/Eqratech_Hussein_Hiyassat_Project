# Dataset Expansion Tools

This directory contains tools for expanding and validating the XAI Engine evaluation datasets.

## Tools Overview

### 1. dataset_generator.py

**Purpose:** Semi-automated generation of domain-specific samples with proper CTE annotations.

**Usage:**
```bash
# Generate 100 physics training samples
python tools/dataset_generator.py --domain physics --count 100 --split train --output datasets/physics/train.jsonl --append

# Generate 50 mathematics validation samples
python tools/dataset_generator.py --domain mathematics --count 50 --split validation --output datasets/mathematics/validation.jsonl --append

# Generate 50 chemistry test samples
python tools/dataset_generator.py --domain chemistry --count 50 --split test --output datasets/chemistry/test.jsonl --append
```

**Features:**
- Template-based generation
- Proper epistemic level distribution (65/20/10/5)
- CTE condition annotation
- Unique ID generation
- Statistics reporting

**Limitations:**
- Generated samples require expert validation
- Limited template variety (expandable)
- Simple content generation (not publication-quality without review)

**Recommendation:** Use as starting point, then have domain experts review and refine each sample.

## Workflow for Dataset Expansion

### Step 1: Generate Initial Samples
```bash
# Generate base samples using templates
python tools/dataset_generator.py --domain physics --count 340 --split train --output datasets/physics/train.jsonl --append
python tools/dataset_generator.py --domain physics --count 73 --split validation --output datasets/physics/validation.jsonl --append
python tools/dataset_generator.py --domain physics --count 73 --split test --output datasets/physics/test.jsonl --append
```

### Step 2: Expert Review
- Domain expert reviews each generated sample
- Validates scientific accuracy
- Checks CTE condition annotations
- Refines language and explanations
- Approves or rejects

### Step 3: Quality Validation
- Run validation scripts (to be created)
- Check for duplicates
- Verify distribution balance
- Measure IAA (inter-annotator agreement)

### Step 4: Iterative Refinement
- Address quality issues
- Fill gaps in coverage
- Balance distributions
- Add edge cases

## Next Steps

**Priority 1:** Create validation tools
- Duplicate detector
- Distribution analyzer
- IAA calculator
- Quality checker

**Priority 2:** Expand templates
- More diverse physics scenarios
- Complex mathematics problems
- Varied chemistry reactions
- Real-world examples

**Priority 3:** Expert annotation interface
- Web-based annotation tool
- Batch processing
- Quality tracking
- Progress monitoring

## References

- Dataset Expansion Plan: `../DATASET_EXPANSION_PLAN.md`
- Dataset README: `../datasets/README.md`
- CTE Gate Domains Guide: `../CTE_GATE_DOMAINS_GUIDE.md`
