#!/usr/bin/env bash
# Regenerate canonical operators catalog with evidence and enrichment from sources.
# Run from repo root. Requires: data/operators_catalog_split_enriched.jsonl (or base CSV), data/quran_i3rab.csv.
set -euo pipefail

rm -f data/operators_catalog_split_enriched.csv.tmp

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

python3 scripts/jsonl_to_operators_csv.py
python3 scripts/build_operator_evidence_from_quran_i3rab.py
PYTHONPATH=src python3 -m fvafk.c2b.read_inputs_for_enrichment_pipeline \
  --src data/operators_catalog_split_project_with_evidence.csv \
  --out data/operators_catalog_split_project_enriched.csv

# Backward compatibility: atomic copy to legacy path (avoid partial write if interrupted)
tmp="data/operators_catalog_split_enriched.csv.tmp"
cp data/operators_catalog_split_project_enriched.csv "$tmp"
mv "$tmp" data/operators_catalog_split_enriched.csv

echo "Done. Canonical: data/operators_catalog_split_project_enriched.csv (copied to data/operators_catalog_split_enriched.csv)"
