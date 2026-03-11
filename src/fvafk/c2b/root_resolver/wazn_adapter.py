# -*- coding: utf-8 -*-
"""
WaznAdapter: bridges WaznMatcher with RootResolver.
Builds candidates (stripped, word_no_al if shadda, word_cleaned), evaluates all
matching patterns, then picks the best hit instead of stopping at the first one.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional

from .wazn_matcher import (
    best_hit,
    get_fal_indices,
    load_patterns,
    MatchHit,
    remove_al_and_shadda,
    split_units,
    try_match_pattern_to_word,
)

SHADDA = "\u0651"
DAGGER_ALIF = "\u0670"


def _normalize_wazn_candidate(text: str) -> str:
    return (text or "").replace(DAGGER_ALIF, "ا").strip()


def extract_root_from_hit(word_processed: str, hit: MatchHit) -> Optional[str]:
    """Extract root letters from word_processed using ف ع ل indices from the pattern."""
    units = split_units(word_processed)
    fal_indices = get_fal_indices(hit.pattern)
    if not fal_indices:
        return None
    letters = []
    for i in fal_indices:
        idx = hit.window_start + i
        if idx < len(units):
            letters.append(units[idx].base)
    return "".join(letters) if letters else None


@dataclass
class WaznResult:
    root: str
    wazn: str
    match_type: str
    window_start: int


class WaznAdapter:
    def __init__(self, patterns: List[str]) -> None:
        self._patterns = patterns

    @property
    def patterns_count(self) -> int:
        return len(self._patterns)

    @classmethod
    def load(cls, patterns_csv: str | Path) -> "WaznAdapter":
        path = Path(patterns_csv)
        patterns = load_patterns(str(path))
        return cls(patterns)

    def resolve(self, word: str, stripped: str = "") -> Optional[WaznResult]:
        candidates: List[str] = []
        word_normalized = _normalize_wazn_candidate(word)
        if word_normalized:
            candidates.append(word_normalized)
        if stripped and stripped.strip():
            stripped_normalized = _normalize_wazn_candidate(stripped)
            if stripped_normalized and stripped_normalized not in candidates:
                candidates.append(stripped_normalized)
        if SHADDA in word:
            word_no_al = _normalize_wazn_candidate(re.sub(r"^[وفبكل]?ال", "", word))
            if word_no_al and word_no_al not in candidates:
                candidates.append(word_no_al)
        word_cleaned = _normalize_wazn_candidate(remove_al_and_shadda(word))
        if word_cleaned not in candidates:
            candidates.append(word_cleaned)

        for cand in candidates:
            result = self._try_resolve(cand, word)
            if result:
                return result
        return None

    def _try_resolve(self, word_processed: str, original_word: str) -> Optional[WaznResult]:
        hits_all: List[MatchHit] = []
        for pattern in self._patterns:
            hits = try_match_pattern_to_word(pattern, word_processed)
            if hits:
                hits_all.extend(hits)
        hit = best_hit(hits_all)
        if hit is None:
            return None
        fal_indices = get_fal_indices(hit.pattern)
        if not fal_indices:
            return None
        root = extract_root_from_hit(word_processed, hit)
        if not root:
            return None
        return WaznResult(
            root=root,
            wazn=hit.pattern,
            match_type=hit.reason,
            window_start=hit.window_start,
        )

    def get_pattern_for_word_root(self, word: str, root_str: str) -> Optional[str]:
        """
        Given (word, root), return the pattern (wazn) that matches, if any.
        Used to fill word_wazn when root came from CLI/heuristic and resolver did not return a wazn.
        """
        root_bare = (root_str or "").replace("-", "").strip()
        if not root_bare or len(root_bare) not in (3, 4):
            return None
        word_norm = _normalize_wazn_candidate(word)
        if not word_norm:
            return None
        for pattern in self._patterns:
            hits = try_match_pattern_to_word(pattern, word_norm)
            if not hits:
                continue
            hit = best_hit(hits)
            if hit is None:
                continue
            extracted = extract_root_from_hit(word_norm, hit)
            if not extracted:
                continue
            if extracted.replace("-", "").strip() == root_bare:
                return hit.pattern
        # try without al/sun letters for prefixed words
        word_cleaned = _normalize_wazn_candidate(remove_al_and_shadda(word))
        if word_cleaned != word_norm:
            for pattern in self._patterns:
                hits = try_match_pattern_to_word(pattern, word_cleaned)
                if not hits:
                    continue
                hit = best_hit(hits)
                if hit is None:
                    continue
                extracted = extract_root_from_hit(word_cleaned, hit)
                if not extracted:
                    continue
                if extracted.replace("-", "").strip() == root_bare:
                    return hit.pattern
        return None
