#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Build a new Mishkat gold file whose `word` column is exactly the token form
used in data/quran-simple-clean.txt.

Strategy:
1. Prefer exact word match against data/mishkat_word_root.csv.
2. Fall back to normalized word match for orthographic variants.
3. Keep the Quran token exactly as-is in the output `word` column.
"""

from __future__ import annotations

import csv
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path


def normalize_word(text: str) -> str:
    text = unicodedata.normalize("NFC", (text or "").strip()).replace("ـ", "")
    text = "".join(ch for ch in text if unicodedata.combining(ch) == 0)
    text = text.replace("أ", "ا").replace("إ", "ا").replace("آ", "ا").replace("ٱ", "ا")
    text = text.replace("ى", "ي")
    text = text.replace("ؤ", "و").replace("ئ", "ي")
    text = text.replace("ءا", "ا").replace("ءو", "و").replace("ءي", "ي")
    return text


def load_quran_counts(path: Path) -> Counter[str]:
    counts: Counter[str] = Counter()
    with open(path, encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("|", 2)
            if len(parts) < 3:
                continue
            for token in parts[2].split():
                counts[token] += 1
    return counts


def load_mishkat_maps(path: Path) -> tuple[dict[str, Counter[str]], dict[str, Counter[str]]]:
    exact_map: dict[str, Counter[str]] = defaultdict(Counter)
    norm_map: dict[str, Counter[str]] = defaultdict(Counter)
    with open(path, encoding="utf-8", newline="") as f:
        for row in csv.DictReader(f):
            word = (row.get("word") or "").strip()
            root = (row.get("root") or "").strip()
            count = int((row.get("count") or "1") or "1")
            if not word or not root:
                continue
            exact_map[word][root] += count
            norm_map[normalize_word(word)][root] += count
    return exact_map, norm_map


def pick_root(counter: Counter[str]) -> tuple[str, str]:
    if not counter:
        return "", ""
    ranked = counter.most_common()
    root = ranked[0][0]
    mode = "unique" if len(counter) == 1 else "majority"
    return root, mode


def main() -> int:
    base = Path(__file__).resolve().parent.parent
    quran_path = base / "data" / "quran-simple-clean.txt"
    mishkat_path = base / "data" / "mishkat_word_root.csv"
    output_path = base / "data" / "mishkat_word_root_quran_exact.csv"
    missing_path = base / "data" / "mishkat_word_root_quran_exact_missing.csv"

    quran_counts = load_quran_counts(quran_path)
    exact_map, norm_map = load_mishkat_maps(mishkat_path)

    rows: list[dict[str, str | int]] = []
    missing_rows: list[dict[str, str | int]] = []
    stats = Counter()

    for word in sorted(quran_counts):
        count = quran_counts[word]
        if word in exact_map:
            root, mode = pick_root(exact_map[word])
            rows.append(
                {
                    "root": root,
                    "word": word,
                    "count": count,
                    "match_source": f"exact_{mode}",
                }
            )
            stats["exact"] += 1
            continue

        normalized = normalize_word(word)
        if normalized in norm_map:
            root, mode = pick_root(norm_map[normalized])
            rows.append(
                {
                    "root": root,
                    "word": word,
                    "count": count,
                    "match_source": f"normalized_{mode}",
                }
            )
            stats["normalized"] += 1
            continue

        missing_rows.append({"word": word, "count": count})
        stats["missing"] += 1

    with open(output_path, "w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["root", "word", "count", "match_source"])
        writer.writeheader()
        writer.writerows(rows)

    with open(missing_path, "w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["word", "count"])
        writer.writeheader()
        writer.writerows(missing_rows)

    print(f"Wrote {len(rows)} rows to {output_path}")
    print(f"Wrote {len(missing_rows)} rows to {missing_path}")
    print(
        "Coverage:",
        {
            "exact": stats["exact"],
            "normalized": stats["normalized"],
            "missing": stats["missing"],
            "quran_unique_tokens": len(quran_counts),
        },
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
