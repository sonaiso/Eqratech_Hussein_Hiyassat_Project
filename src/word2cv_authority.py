# -*- coding: utf-8 -*-
"""
Authoritative CV / cv_advanced from ``src/word-2-cv.py`` only.

Same tokenization and per-token analysis as ``scripts/print_word2cv_phonology.py``:
NFC + ``normalize_word`` on full input, then ``ARABIC_TOKEN_RE`` token loop.

Consumers (FVAFK ``c1.cv_analysis``, L6, debug scripts) must use this module so
``cv`` / ``cv_advanced`` / ``word_normalized`` cannot drift from the reference script.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import ModuleType
from typing import Any, Dict, List

_MOD: ModuleType | None = None


def load_word2cv_module() -> ModuleType:
    global _MOD
    if _MOD is None:
        path = Path(__file__).resolve().parent / "word-2-cv.py"
        spec = importlib.util.spec_from_file_location("word_2_cv_authority", path)
        if spec is None or spec.loader is None:
            raise ImportError(f"Cannot load word-2-cv from {path}")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _MOD = mod
    return _MOD


def compute_authoritative_word_row(token: str) -> Dict[str, Any]:
    """Single Arabic token → same dict shape as ``word-2-cv.analyze_token_for_pipeline`` plus metadata."""
    m = load_word2cv_module()
    row = m.analyze_token_for_pipeline(token)
    out: Dict[str, Any] = {
        "word": m.normalize_word(token),
        "cv": row.get("cv", ""),
        "cv_advanced": row.get("cv_advanced", ""),
        "word_normalized": row.get("word_normalized", ""),
        "word_input": row.get("word_input", ""),
        "excluded": bool(row.get("excluded")),
        "cv_law_ok": row.get("cv_law_ok"),
        "cv_law_reason": row.get("cv_law_reason", ""),
        "cv_authority_source": "word2cv",
    }
    return out


def compute_authoritative_cv_analysis(text: str) -> Dict[str, Any]:
    """
    Full text → ``c1.cv_analysis``-shaped payload (engine + words list).

    Mirrors ``scripts/print_word2cv_phonology.py`` (no fvafk, no gates, no operator empty-slot logic).
    """
    m = load_word2cv_module()
    normalize_word = m.normalize_word
    analyze_token_for_pipeline = m.analyze_token_for_pipeline
    ARABIC_TOKEN_RE = m.ARABIC_TOKEN_RE

    normalized_input = normalize_word(text)
    words_out: List[Dict[str, Any]] = []
    for match in ARABIC_TOKEN_RE.finditer(normalized_input):
        t = normalize_word(match.group(0))
        if not t:
            continue
        row = analyze_token_for_pipeline(t)
        words_out.append(
            {
                "word": t,
                "cv": row.get("cv", ""),
                "cv_advanced": row.get("cv_advanced", ""),
                "word_normalized": row.get("word_normalized", ""),
                "word_input": row.get("word_input", ""),
                "excluded": bool(row.get("excluded")),
                "cv_law_ok": row.get("cv_law_ok"),
                "cv_law_reason": row.get("cv_law_reason", ""),
                "cv_authority_source": "word2cv",
            }
        )

    return {
        "engine": "word2cv",
        "cv_authority_source": "word2cv",
        "total_words_input": len(words_out),
        "total_words_computed": len(words_out),
        "excluded_names": 0,
        "words": words_out,
    }
