"""
Verify CV output: ``src/word-2-cv.py`` (direct) vs FVAFK pipeline (``analyze_text_for_cv_after_phonology``).

Legacy c2a / phonology_v2 comparison was removed — the pipeline uses word-2-cv only.
"""

from __future__ import annotations

import argparse
from typing import Any, Dict, List, Optional, Tuple

from fvafk.c1.cv_pattern import analyze_text_for_cv_after_phonology
from fvafk.c1.word2cv_loader import analyze_token_for_pipeline
from fvafk.c2b.word_boundary import WordBoundaryDetector


def _pipeline_word_cv(token: str) -> Optional[Dict[str, str]]:
    r = analyze_text_for_cv_after_phonology(token)
    words = r.get("words") or []
    if not words:
        return None
    return words[0]


def _direct_word_cv(token: str) -> Optional[Dict[str, str]]:
    row = analyze_token_for_pipeline(token)
    if row.get("excluded"):
        return None
    return {"cv": row["cv"], "cv_advanced": row["cv_advanced"]}


def _format_row(cols: List[str], widths: List[int]) -> str:
    parts = []
    for c, w in zip(cols, widths):
        parts.append(c.ljust(w))
    return " | ".join(parts)


def compare_text(text: str) -> Tuple[List[Dict[str, Any]], List[str]]:
    spans = WordBoundaryDetector().detect(text)
    rows: List[Dict[str, Any]] = []
    excluded: List[str] = []

    for sp in spans:
        tok = sp.token
        direct = _direct_word_cv(tok)
        pipe = _pipeline_word_cv(tok)

        if direct is None and pipe is None:
            excluded.append(tok)
            continue

        rows.append(
            {
                "token": tok,
                "span": (sp.start, sp.end),
                "direct": direct,
                "pipeline": pipe,
                "same": (direct == pipe),
            }
        )

    return rows, excluded


def main() -> int:
    p = argparse.ArgumentParser(
        description="Compare CV: src/word-2-cv.py direct vs FVAFK pipeline (must match)."
    )
    p.add_argument("text", help="Arabic text (diacritized recommended)")
    args = p.parse_args()

    rows, excluded = compare_text(args.text)

    headers = [
        "token",
        "span",
        "direct.cv",
        "direct.cv_adv",
        "pipe.cv",
        "pipe.cv_adv",
        "same?",
    ]
    data_rows: List[List[str]] = []
    for r in rows:
        d = r["direct"] or {}
        pl = r["pipeline"] or {}
        data_rows.append(
            [
                r["token"],
                f"{r['span'][0]}:{r['span'][1]}",
                d.get("cv", ""),
                d.get("cv_advanced", ""),
                pl.get("cv", ""),
                pl.get("cv_advanced", ""),
                "YES" if r["same"] else "NO",
            ]
        )

    widths = [len(h) for h in headers]
    for row in data_rows:
        widths = [max(w, len(cell)) for w, cell in zip(widths, row)]

    print(_format_row(headers, widths))
    print(_format_row(["-" * w for w in widths], widths))
    for row in data_rows:
        print(_format_row(row, widths))

    if excluded:
        print("\nExcluded/ignored tokens (no CV computed):")
        for t in excluded:
            print(f"- {t}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
