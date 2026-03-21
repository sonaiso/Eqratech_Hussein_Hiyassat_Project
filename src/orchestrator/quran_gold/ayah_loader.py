# -*- coding: utf-8 -*-
"""
Load full ayah text from a Quran line-oriented file (e.g. `data/quran-uthmani.txt`).

Expected format per line: `surah|ayah|text` (fields separated by `|`).
"""

from __future__ import annotations

import os
from functools import lru_cache
from typing import Dict, Optional, Tuple

_PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
_DEFAULT_TEXT = os.path.join(_PROJECT_ROOT, "data", "quran-uthmani.txt")


def _build_ayah_index(path: str) -> Dict[Tuple[int, int], str]:
    out: Dict[Tuple[int, int], str] = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("|", 2)
            if len(parts) < 3:
                continue
            try:
                surah = int(parts[0].strip())
                ayah = int(parts[1].strip())
            except ValueError:
                continue
            text = parts[2].strip()
            if text:
                out[(surah, ayah)] = text
    return out


@lru_cache(maxsize=4)
def _cached_ayah_index(path: str) -> Dict[Tuple[int, int], str]:
    return _build_ayah_index(path)


def load_ayah_text_index(csv_path: Optional[str] = None) -> Dict[Tuple[int, int], str]:
    """
    Map (surah, ayah) -> full ayah string from the default or given file.
    """
    p = csv_path or _DEFAULT_TEXT
    if not os.path.isfile(p):
        raise FileNotFoundError(f"Quran ayah text file not found: {p}")
    return _cached_ayah_index(p)


def get_ayah_text(surah: int, ayah: int, *, text_path: Optional[str] = None) -> Optional[str]:
    """Return ayah text or None if not in index."""
    idx = load_ayah_text_index(text_path)
    return idx.get((int(surah), int(ayah)))


def default_quran_text_path() -> str:
    return _DEFAULT_TEXT
