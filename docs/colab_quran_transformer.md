# Colab Workflow — Transformer Training on the Quran Dataset

This guide walks through running the Quran transformer training pipeline in Google Colab while keeping all project assets inside `d:\sfg\.github\Eqratech_Arabic_Diana_Project`.

## 1. Prerequisites
- Google Colab Pro/Pro+ account (for longer runtimes and GPU access).
- Quran dataset prepared locally under `data/quran/` with the split files:
  - `train.jsonl`
  - `validation.jsonl`
  - `test.jsonl` *(optional but recommended)*
  Each JSONL row should expose at least `text` and `label` fields.
- GitHub access token (optional) if the repository is private.

## 2. Stage the Dataset
1. Create the directory `data/quran/` inside this repository and drop the split JSONL files there.
2. Commit+push or upload the folder to a private Google Drive directory.
3. (Optional) Compress the folder for faster transfer: `zip -r quran_dataset.zip data/quran`.

## 3. Launch Colab Notebook
Create a new notebook (or reuse `notebooks/quran_transformer.ipynb` when added) with the following prologue cell:

```python
!git clone https://github.com/salemqundil/Eqratech_Arabic_Diana_Project.git
%cd Eqratech_Arabic_Diana_Project

# Install runtime dependencies
!pip install -r requirements.txt
!pip install -r requirements-dev.txt
!pip install transformers datasets accelerate evaluate pyyaml
```

If the dataset is on Google Drive:

```python
from google.colab import drive

drive.mount('/content/drive')
!cp /content/drive/MyDrive/path/to/quran_dataset.zip .
!unzip -q quran_dataset.zip -d data/
```

## 4. Review & Edit Config
Open `configs/transformer_quran_colab.yaml` and adjust paths if necessary:
- `dataset.*_file` should map to `/content/Eqratech_Arabic_Diana_Project/data/quran/*.jsonl`.
- Update `max_length`, batch sizes, epochs, etc., to fit GPU memory.

Example tweak inside the notebook:

```python
from pathlib import Path
import yaml

config_path = Path('configs/transformer_quran_colab.yaml')
config = yaml.safe_load(config_path.read_text(encoding='utf-8'))
config['dataset']['train_file'] = '/content/Eqratech_Arabic_Diana_Project/data/quran/train.jsonl'
config_path.write_text(yaml.safe_dump(config, allow_unicode=True), encoding='utf-8')
```

## 5. Run Training Script
Launch the training job using the provided script:

```python
!python scripts/train_transformer_quran.py --config configs/transformer_quran_colab.yaml
```

Outputs:
- Model checkpoints at `training.output_dir` (default `/content/outputs/quran-transformer`).
- `label_mapping.json` saved in the same directory for inference.
- Evaluation metrics shown in the Colab output and stored in Hugging Face Trainer logs.

## 6. Monitor & Resume
- Enable Colab’s GPU (`Runtime > Change runtime type > GPU`).
- Use `!nvidia-smi` to watch utilization.
- If a run stops, rerun the command with `--resume_from_checkpoint /content/outputs/quran-transformer/checkpoint-XXXX`.

## 7. Persist Artifacts
1. Zip the output directory: `!zip -r outputs_quran.zip /content/outputs/quran-transformer`.
2. Copy to Drive or upload to Cloud Storage:
   ```python
   !cp outputs_quran.zip /content/drive/MyDrive/taqi_artifacts/
   ```
3. Record the run in `docs/agent_md_log.md` and TAQI_MD (hashes, metrics, config SHA).

## 8. Post-Training Checklist
- Push any config/notebook updates back to GitHub (`git commit && git push`).
- Validate the model locally using the generator→tracer CI if applicable.
- Update `docs/cloud_training_workflow.md` and TAQI_MD with metrics (F1, accuracy, energy balance).
- Consider promoting the run to a Release snapshot with “ثبّت الإصدار”.

---
Last updated: 2025-10-29
