# -*- coding: utf-8 -*-
"""
FVAFK runner — invokes the same code path as the CLI (morphology + multi-word).

Returns the full result dict (c1, c2a, c2b, syntax, c2d, rhetoric_signals).
Used by layer adapters to fill transformation_result from existing outputs.
"""

from __future__ import annotations

from typing import Any, Dict

# Key used on pipeline to store the result (internal; not part of Stage 2 contract)
FVAFK_RESULT_KEY = "_fvafk_result"


def run_fvafk_once(text: str) -> Dict[str, Any]:
    """
    Run the FVAFK pipeline (CLI path: morphology + multi-word).
    Returns the same structure as MinimalCLI.run(..., morphology=True, multi_word=True).
    On failure, returns {"success": False, "error": str(e)}; no exception raised.
    """
    try:
        from fvafk.cli.main import MinimalCLI
        cli = MinimalCLI()
        result = cli.run(
            text=text,
            morphology=True,
            multi_word=True,
            phonology_v2=False,
        )
        if not isinstance(result, dict):
            return {"success": False, "error": "CLI did not return a dict"}
        result.setdefault("success", True)
        return result
    except Exception as e:
        return {"success": False, "error": str(e)}
