import argparse
import json
from pathlib import Path
from typing import Dict, List

import datasets
import torch
import yaml
from transformers import (
    AutoModelForSequenceClassification,
    AutoTokenizer,
    DataCollatorWithPadding,
    Trainer,
    TrainingArguments,
)
import evaluate


def load_config(config_path: Path) -> Dict:
    with config_path.open("r", encoding="utf-8") as fh:
        return yaml.safe_load(fh)


def load_dataset(data_cfg: Dict) -> datasets.DatasetDict:
    data_files = {
        "train": data_cfg["train_file"],
        "validation": data_cfg["validation_file"],
    }
    if data_cfg.get("test_file"):
        data_files["test"] = data_cfg["test_file"]
    return datasets.load_dataset("json", data_files=data_files)


def build_label_mapping(dataset: datasets.Dataset, label_column: str) -> Dict[str, int]:
    labels: List[str] = sorted({example[label_column] for example in dataset})
    return {label: idx for idx, label in enumerate(labels)}


def main() -> None:
    parser = argparse.ArgumentParser(description="Fine-tune a transformer on the Quran dataset")
    parser.add_argument("--config", type=Path, required=True, help="Path to YAML config file")
    args = parser.parse_args()

    cfg = load_config(args.config)
    data_cfg = cfg["dataset"]
    training_cfg = cfg["training"]
    model_cfg = cfg["model"]

    raw_datasets = load_dataset(data_cfg)

    tokenizer = AutoTokenizer.from_pretrained(model_cfg["tokenizer_name"], cache_dir=model_cfg.get("cache_dir"))

    text_column = data_cfg["text_column"]
    label_column = data_cfg["label_column"]

    label2id = build_label_mapping(raw_datasets["train"], label_column)
    id2label = {idx: label for label, idx in label2id.items()}

    def preprocess(example: Dict[str, str]) -> Dict[str, List[int]]:
        tokenized = tokenizer(
            example[text_column],
            padding=False,
            truncation=True,
            max_length=data_cfg.get("max_length", 256),
        )
        tokenized["labels"] = label2id[example[label_column]]
        return tokenized

    tokenized_datasets = raw_datasets.map(preprocess, batched=False, remove_columns=raw_datasets["train"].column_names)

    model = AutoModelForSequenceClassification.from_pretrained(
        model_cfg["base_model_name"],
        num_labels=len(label2id),
        id2label=id2label,
        label2id=label2id,
        cache_dir=model_cfg.get("cache_dir"),
    )

    data_collator = DataCollatorWithPadding(tokenizer)

    metric = evaluate.load("f1")

    def compute_metrics(eval_pred):
        preds, labels = eval_pred
        if isinstance(preds, tuple):
            preds = preds[0]
        preds = preds.argmax(axis=-1)
        f1 = metric.compute(predictions=preds, references=labels, average="macro")
        return {"f1": f1["f1"] if isinstance(f1, dict) else f1}

    exclude_keys = {"output_dir", "report_to"}
    training_kwargs = {k: v for k, v in training_cfg.items() if k not in exclude_keys}

    training_args = TrainingArguments(
        output_dir=training_cfg["output_dir"],
        seed=cfg.get("seed", 42),
        report_to=training_cfg.get("report_to", []),
        **training_kwargs,
    )

    trainer = Trainer(
        model=model,
        args=training_args,
        train_dataset=tokenized_datasets.get("train"),
        eval_dataset=tokenized_datasets.get("validation"),
        tokenizer=tokenizer,
        data_collator=data_collator,
        compute_metrics=compute_metrics,
    )

    if torch.cuda.is_available():
        model.cuda()

    trainer.train()

    # Optional evaluation on the test set if provided.
    if tokenized_datasets.get("test"):
        trainer.evaluate(eval_dataset=tokenized_datasets["test"], metric_key_prefix="test")

    # Persist label mapping for downstream inference.
    id_mapping_path = Path(training_cfg["output_dir"]) / "label_mapping.json"
    id_mapping_path.parent.mkdir(parents=True, exist_ok=True)
    with id_mapping_path.open("w", encoding="utf-8") as fh:
        json.dump(id2label, fh, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    main()
