# -*- coding: utf-8 -*-
"""
Load `data/quran_i3rab.csv` for verification (tests, tooling).

Word keys use exact diacritized forms as stored in the CSV — do not normalize
Quranic surface strings when looking up.
"""

from __future__ import annotations

import csv
import os
from functools import lru_cache
from typing import Dict, Optional, Tuple

_PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
_DEFAULT_CSV = os.path.join(_PROJECT_ROOT, "data", "quran_i3rab.csv")


def _build_index(csv_path: str) -> Dict[Tuple[int, int, str], str]:
    out: Dict[Tuple[int, int, str], str] = {}
    with open(csv_path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                surah = int((row.get("surah") or "").strip())
                ayah = int((row.get("ayah") or "").strip())
            except (TypeError, ValueError):
                continue
            word = (row.get("word") or "").strip()
            i3rab = (row.get("i3rab") or "").strip()
            if not word:
                continue
            out[(surah, ayah, word)] = i3rab
    return out


@lru_cache(maxsize=1)
def load_quran_gold() -> Dict[Tuple[int, int, str], str]:
    """Load and cache the full (surah, ayah, word) -> iʿrāb text index from `data/quran_i3rab.csv`."""
    if not os.path.isfile(_DEFAULT_CSV):
        raise FileNotFoundError(f"Quranic i3rab CSV not found: {_DEFAULT_CSV}")
    return _build_index(_DEFAULT_CSV)


def lookup_i3rab(surah: int, ayah: int, word: str) -> Optional[str]:
    """
    Return the gold iʿrāb line for an exact word in (surah, ayah), or None.
    `word` must match the CSV token surface exactly (including diacritics).
    """
    idx = load_quran_gold()
    return idx.get((int(surah), int(ayah), (word or "").strip()))
