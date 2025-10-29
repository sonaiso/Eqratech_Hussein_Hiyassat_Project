# Agent MD Log

## 2025-10-29
- Reminder to run version control commands with the English keyboard layout; PowerShell may prepend the Arabic character `ؤ`, causing `git` to fail.
- Local verification plan:
  1. `git pull`
  2. `python -m venv .venv`
  3. `.venv\Scripts\activate`
  4. `pip install -r requirements-dev.txt`
  5. `pytest -q`
- Pending action: execute the above sequence and confirm tests pass.
- Created `scripts/prepare_quran_dataset.py` to normalize Quran text and generate train/validation/test JSONL files.
- Generated dataset splits under `data/quran/` (train=4988, validation=623, test=625) using `quran-simple-enhanced (2).txt`.
- Added `notebooks/quran_transformer.ipynb` to automate the Colab fine-tuning workflow (clone, install deps, stage dataset, run training, export artifacts).
