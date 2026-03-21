# -*- coding: utf-8 -*-
"""
Deterministic gold-word ↔ pipeline-token alignment for Quranic iʿrāb audit.

Uses orthographic normalization only (no semantic guessing). If no unique forward
match exists for a gold word in token order, the position is **ambiguous**.
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass
from enum import Enum
from typing import List, Optional, Sequence, Tuple


class AlignmentStatus(str, Enum):
    ALIGNED = "aligned"
    AMBIGUOUS = "alignment_ambiguous"
    NO_TOKEN = "no_matching_token"


@dataclass(frozen=True)
class AlignmentResult:
    """Per gold word index within an ayah."""

    gold_index: int
    token_index: Optional[int]
    status: AlignmentStatus
    reason: str


def normalize_arabic_surface(s: str) -> str:
    """
    NFC + conservative orthographic unification for matching Quranic tokens
    across Uthmani (ٱ) vs i3rab-CSV surfaces.
    """
    t = unicodedata.normalize("NFC", (s or "").strip())
    # Alef wasla / hamza on alef → plain alef for matching
    t = t.replace("\u0671", "\u0627")  # ٱ → ا
    t = t.replace("\u0622", "\u0627").replace("\u0623", "\u0627").replace("\u0625", "\u0627")
    return t


def align_gold_words_to_tokens(
    gold_words: Sequence[str],
    token_surfaces: Sequence[str],
) -> Tuple[List[AlignmentResult], int, int]:
    """
    Greedy forward alignment: for each gold word in order, take the **smallest**
    token index ≥ cursor where normalized surfaces match.

    Returns (results, aligned_count, ambiguous_count).
    """
    results: List[AlignmentResult] = []
    aligned = 0
    ambiguous = 0
    cursor = 0
    tok_norm = [normalize_arabic_surface(x) for x in token_surfaces]
    gw_norm = [normalize_arabic_surface(x) for x in gold_words]

    for gi, gw in enumerate(gw_norm):
        if not gw:
            results.append(
                AlignmentResult(
                    gold_index=gi,
                    token_index=None,
                    status=AlignmentStatus.AMBIGUOUS,
                    reason="empty_gold_word",
                )
            )
            ambiguous += 1
            continue

        candidates = [j for j in range(cursor, len(tok_norm)) if tok_norm[j] == gw]
        if len(candidates) == 0:
            results.append(
                AlignmentResult(
                    gold_index=gi,
                    token_index=None,
                    status=AlignmentStatus.NO_TOKEN,
                    reason="no_normalized_surface_match",
                )
            )
            ambiguous += 1
            continue
        if len(candidates) > 1:
            results.append(
                AlignmentResult(
                    gold_index=gi,
                    token_index=None,
                    status=AlignmentStatus.AMBIGUOUS,
                    reason="multiple_candidate_tokens_same_surface",
                )
            )
            ambiguous += 1
            cursor = candidates[0] + 1
            continue

        j = candidates[0]
        results.append(
            AlignmentResult(
                gold_index=gi,
                token_index=j,
                status=AlignmentStatus.ALIGNED,
                reason="unique_forward_match",
            )
        )
        aligned += 1
        cursor = j + 1

    return results, aligned, ambiguous
