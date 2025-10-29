# Cloud Training Workflow

This document captures the recommended end-to-end workflow for running TAQI engines and training jobs on Google Cloud while coordinating with Colab collaborators.

## 1. Project & Budget Guardrails
- Create or reuse a dedicated GCP project for TAQI training.
- Enable billing and set two budget alerts (50% and 80%) so the $300 credit is monitored.
- Restrict IAM roles to project owners and service accounts needed for automation.

## 2. Source of Truth & Versioning
- Continue using GitHub for code. Feature branches feed Pull Requests; merge to `main` only after pipeline checks pass.
- After each stable merge, capture the Live state in TAQI_MD. Use the "Thabbit al-Issdar" release command when you want to freeze a snapshot.

## 3. Storage Layout
- Create a regional Cloud Storage bucket (example `gs://taqi-ai-bucket`).
- Recommended prefixes:
  - `datasets/` for curated corpora and phoneme tables.
  - `checkpoints/` for model weights.
  - `logs/` for training summaries, TensorBoard, and gate metrics.
  - `reports/` for generator→tracer outputs and SHACL results.
- Apply lifecycle rules to expire stale checkpoints and logs older than 30 days unless pinned to a release.

## 4. Local & Colab Development
- Use local `.venv` or Poetry for reproducible installs.
- Maintain Colab notebooks under `notebooks/` with the following prologue cells:
  ```python
  !git clone https://github.com/<org>/Eqratech_Arabic_Diana_Project.git
  %cd Eqratech_Arabic_Diana_Project
  !pip install -r requirements.txt
  from google.colab import drive
  drive.mount('/content/drive')  # if shared Drive assets are needed
  ```
- Encourage collaborators to pull the latest `main` or relevant branch before edits.
- Notebooks should include a "Run All" section that executes generator→tracer validation and exports metrics to the shared bucket.

## 5. Containerization & Automation
- Author a `Dockerfile` that installs runtime dependencies and exposes an entry point for training.
- Use Cloud Build (`cloudbuild.yaml`) to build and push container images to Artifact Registry.
- Define Vertex AI Training specs to launch jobs from the container. Suggested structure:
  ```yaml
  workerPoolSpecs:
    - machineSpec:
        machineType: n1-standard-8
        acceleratorType: NVIDIA_TESLA_L4
        acceleratorCount: 1
      replicaCount: 1
      containerSpec:
        imageUri: <region>-docker.pkg.dev/<project>/taqi/train:latest
        args: ["python", "src/train.py", "--config", "configs/train_vertex.yaml"]
  ```

## 6. Experiment Tracking
- Log hyperparameters, energy balance deltas, gate satisfaction, and validation scores to:
  - Vertex AI Experiments or MLflow (hosted on Compute Engine or managed service).
  - TensorBoard with logdir in `gs://taqi-ai-bucket/logs/<run_id>`.
- Include the TAQI_MD hash and git commit SHA in every run record.

## 7. Cost Control Practices
- Prefer preemptible GPU instances for exploratory runs; fall back to on-demand for long training only when required.
- Automatically stop Compute Engine VMs after jobs finish (`gcloud compute instances stop <name>` in CI).
- Schedule a weekly job to prune unused disks and aged checkpoints from storage.

## 8. Continuous Integration Hooks
- Extend GitHub Actions to:
  - Run lint, type checks, unit tests, and generator→tracer verification.
  - Optionally trigger a small Vertex AI training job on merges to `main` for smoke validation.
  - Upload reports to `reports/` with release tags.

## 9. Release Checklist
- Confirm CI pipeline is green and metrics meet thresholds (GateSatisfaction ≥ 0.95, EnergyBalance Δ ≤ 0.01).
- Archive artifacts from the successful run (`checkpoints/`, `logs/`, `reports/`).
- Update TAQI_MD with run IDs, hashes, and storage pointers.
- Issue the "Thabbit al-Issdar" command to freeze the release version.
- Tag the git commit (e.g., `vYYYY.MM.DD`) and update `CHANGELOG.md`.

## 10. Security & Access Hygiene
- Store secrets (API keys, service account JSON) in Secret Manager; access them via runtime environment variables.
- Avoid mounting full Drive contents unless needed; limit sharing to specific folders.
- Rotate service account keys and audit IAM roles quarterly.

---
Last updated: 2025-10-27
