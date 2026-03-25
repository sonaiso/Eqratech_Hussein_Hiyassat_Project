# -*- coding: utf-8 -*-
"""
CV / cv_advanced for the FVAFK pipeline.

Authoritative ``cv`` / ``cv_advanced`` / ``word_normalized`` come only from
``src/word2cv_authority.py`` (same path as ``scripts/print_word2cv_phonology.py``).
C2a gates must not rewrite these fields (see ``G_WASL`` validation-only policy).
"""

from __future__ import annotations

from typing import Any, Dict, List

from word2cv_authority import compute_authoritative_cv_analysis

from .word2cv_loader import (
    cv_advanced_pattern,
    cv_pattern,
    should_exclude,
    strip_all_marks,
)

# Back-compat: old name used diacritic stripping identical to word-2-cv strip_all_marks
strip_marks = strip_all_marks

# Alias: same implementation as word-2-cv
advanced_cv_pattern = cv_advanced_pattern


def advanced_cv_syllables(word: str) -> str:
    return cv_advanced_pattern(word)


def split_cv_syllables(cv_advanced: str) -> List[str]:
    if not cv_advanced:
        return []

    simplified = "".join("V" if ch in {"a", "o", "i"} else ch for ch in cv_advanced)
    syllables: List[str] = []
    buffer: List[str] = []
    idx = 0
    vowel_seen = False

    def is_cv_at(position: int) -> bool:
        return (
            position + 1 < len(simplified)
            and simplified[position] == "C"
            and simplified[position + 1] == "V"
        )

    while idx < len(simplified):
        buffer.append(cv_advanced[idx])
        if simplified[idx] == "V":
            vowel_seen = True
        if vowel_seen and idx + 1 < len(simplified) and is_cv_at(idx + 1):
            syllables.append("".join(buffer))
            buffer = []
            vowel_seen = False
        idx += 1

    if buffer:
        syllables.append("".join(buffer))

    return syllables


def analyze_text_for_cv(text: str) -> List[Dict[str, str]]:
    """Unique Arabic tokens (first occurrence order) → cv / cv_advanced (authority path)."""
    r = compute_authoritative_cv_analysis(text)
    seen = set()
    results: List[Dict[str, str]] = []
    for w in r["words"]:
        if w.get("excluded"):
            continue
        t = w["word"]
        if t in seen:
            continue
        seen.add(t)
        results.append({"cv": w["cv"], "cv_advanced": w["cv_advanced"]})
    return results


def analyze_text_for_cv_after_phonology(text: str, engine: str = "word2cv") -> Dict[str, Any]:
    """
    Per-token CV for pipeline L6 — identical to ``scripts/print_word2cv_phonology.py``.

    The ``engine`` argument is kept for API compatibility; ``c2a`` and
    ``phonology_v2`` are ignored — they are not CV sources.
    """
    del engine  # word-2-cv only
    return compute_authoritative_cv_analysis(text)
