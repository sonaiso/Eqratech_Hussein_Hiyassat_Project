# -*- coding: utf-8 -*-
"""
Canonical ayah reconstruction from `data/quran_i3rab.csv` only (Batch 28.7).

Token order = CSV row order within each (surah, ayah). Surfaces are joined with spaces
for pipeline input; this must not read `data/quran-uthmani.txt`.
"""

from __future__ import annotations

from typing import List, Sequence, Tuple

from orchestrator.quran_gold.alignment import normalize_arabic_surface


def gold_rows_for_ayah(
    indexed: Sequence[Tuple[int, Any]],
    surah: int,
    ayah: int,
) -> List[Any]:
    cands = [r for _, r in indexed if r.surah == surah and r.ayah == ayah]
    cands.sort(key=lambda r: r.index_in_ayah)
    return cands


def reconstruct_ayah_text_from_gold_rows(rows: Sequence[Any]) -> str:
    """Single string for `run_pipeline`: words in CSV order, separated by ASCII space."""
    parts = [(r.word or "").strip() for r in rows]
    return " ".join(p for p in parts if p)


def reconstruct_ayah_text_from_indexed(
    indexed: Sequence[Tuple[int, Any]],
    surah: int,
    ayah: int,
) -> str:
    return reconstruct_ayah_text_from_gold_rows(gold_rows_for_ayah(indexed, surah, ayah))


def occurrence_ranks_by_surface(rows: Sequence[Any]) -> List[int]:
    """
    1-based occurrence index among identical normalize_arabic_surface(word) within this ayah,
    in CSV order (for repeated surfaces).
    """
    ranks: List[int] = []
    counts: dict[str, int] = {}
    for r in rows:
        key = normalize_arabic_surface(r.word or "")
        n = counts.get(key, 0) + 1
        counts[key] = n
        ranks.append(n)
    return ranks


def global_row_indices_for_ayah(
    indexed: Sequence[Tuple[int, Any]],
    surah: int,
    ayah: int,
) -> List[int]:
    """Global gold CSV row indices in order for this ayah."""
    cands = [(gi, r) for gi, r in indexed if r.surah == surah and r.ayah == ayah]
    cands.sort(key=lambda t: t[1].index_in_ayah)
    return [gi for gi, _ in cands]


def word_index_to_global_index(
    indexed: Sequence[Tuple[int, Any]],
    surah: int,
    ayah: int,
) -> dict[int, int]:
    """Map ayah-local word index -> global gold row index."""
    m: dict[int, int] = {}
    for gi, r in indexed:
        if r.surah == surah and r.ayah == ayah:
            m[int(r.index_in_ayah)] = gi
    return m
