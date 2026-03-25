# -*- coding: utf-8 -*-
"""Load src/word-2-cv.py — single source of truth for CV / cv_advanced (no duplicate logic)."""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import ModuleType
from typing import Any, Dict

_MOD: ModuleType | None = None


def load_word2cv() -> ModuleType:
    global _MOD
    if _MOD is None:
        root = Path(__file__).resolve().parents[2]
        path = root / "word-2-cv.py"
        spec = importlib.util.spec_from_file_location("word_2_cv", path)
        if spec is None or spec.loader is None:
            raise ImportError(f"Cannot load word-2-cv from {path}")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _MOD = mod
    return _MOD


def analyze_token_for_pipeline(token: str) -> Dict[str, Any]:
    return load_word2cv().analyze_token_for_pipeline(token)


# Re-export symbols used by fvafk.c1.cv_pattern and tests
_m = load_word2cv()
FATHA = _m.FATHA
DAMMA = _m.DAMMA
KASRA = _m.KASRA
SUKUN = _m.SUKUN
SHADDA = _m.SHADDA
TANWIN_FATH = _m.TANWIN_FATH
TANWIN_DAMM = _m.TANWIN_DAMM
TANWIN_KASR = _m.TANWIN_KASR
SHORT_VOWELS = _m.SHORT_VOWELS
ALL_MARKS = _m.ALL_MARKS
ALIF = _m.ALIF
WAW = _m.WAW
YA = _m.YA
ALIF_MAQSURA = _m.ALIF_MAQSURA
ALIF_MADDA = _m.ALIF_MADDA
ALIF_WASLA = _m.ALIF_WASLA
cv_pattern = _m.cv_pattern
cv_advanced_pattern = _m.cv_advanced_pattern
cv_pattern_and_advanced = _m.cv_pattern_and_advanced
normalize_word = _m.normalize_word
normalize_initial_hamza = _m.normalize_initial_hamza
normalize_missing_harakat = _m.normalize_missing_harakat
should_exclude = _m.should_exclude
follows_cv_law = _m.follows_cv_law
split_letters_and_marks = _m.split_letters_and_marks
expand_shadda = _m.expand_shadda
strip_all_marks = _m.strip_all_marks
is_arabic_letter = _m.is_arabic_letter
has_any = _m.has_any
