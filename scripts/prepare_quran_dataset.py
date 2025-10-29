"""Utility to normalize Quran text and create train/validation/test JSONL splits."""

import argparse
import json
import random
import unicodedata
from pathlib import Path
from typing import Dict, List

BASMALA = "بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ"


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Path to raw Quran text file")
    parser.add_argument(
        "--output-dir", type=Path, required=True, help="Directory where JSONL splits will be written"
    )
    parser.add_argument("--seed", type=int, default=42, help="Random seed for shuffling the verses")
    parser.add_argument("--train-ratio", type=float, default=0.8, help="Portion of verses used for training")
    parser.add_argument(
        "--validation-ratio", type=float, default=0.1, help="Portion of verses used for validation"
    )
    return parser.parse_args()


def normalize_text(text: str) -> str:
    cleaned = text.replace("<sel>", " ")
    cleaned = " ".join(cleaned.split())  # collapse whitespace
    return unicodedata.normalize("NFC", cleaned)


def load_verses(path: Path) -> List[Dict[str, str]]:
    verses: List[Dict[str, str]] = []
    current_surah = 0
    ayah_index = 0

    with path.open("r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = normalize_text(raw_line.strip())
            if not line:
                continue

            if line.startswith(BASMALA):
                current_surah += 1
                ayah_index = 0

            ayah_index += 1
            verses.append(
                {
                    "surah": current_surah or 1,
                    "ayah": ayah_index,
                    "text": line,
                }
            )

    return verses


def split_dataset(
    verses: List[Dict[str, str]],
    train_ratio: float,
    validation_ratio: float,
    seed: int,
) -> Dict[str, List[Dict[str, str]]]:
    if not 0 < train_ratio < 1:
        raise ValueError("train_ratio must be between 0 and 1")
    if not 0 <= validation_ratio < 1:
        raise ValueError("validation_ratio must be between 0 and 1")
    if train_ratio + validation_ratio >= 1:
        raise ValueError("train_ratio + validation_ratio must be less than 1")

    rng = random.Random(seed)
    shuffled = verses.copy()
    rng.shuffle(shuffled)

    total = len(shuffled)
    train_end = int(total * train_ratio)
    validation_end = train_end + int(total * validation_ratio)

    return {
        "train": shuffled[:train_end],
        "validation": shuffled[train_end:validation_end],
        "test": shuffled[validation_end:],
    }


def write_jsonl(records: List[Dict[str, str]], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False))
            handle.write("\n")


def main() -> None:
    args = parse_arguments()
    verses = load_verses(args.input)
    splits = split_dataset(verses, args.train_ratio, args.validation_ratio, args.seed)

    for split_name, records in splits.items():
        output_path = args.output_dir / f"{split_name}.jsonl"
        write_jsonl(records, output_path)
        print(f"Wrote {len(records)} records to {output_path}")


if __name__ == "__main__":
    main()
