"""Patch 17: L17 Stage15 — IDAFA wins over competing verbal OBJ (مضاف إليه vs مفعول به)."""

from __future__ import annotations

import unicodedata

import pytest

from orchestrator.pipeline_orchestrator import run_pipeline


def _strip_diacritics(s: str) -> str:
    return "".join(
        ch for ch in unicodedata.normalize("NFD", s) if unicodedata.category(ch) != "Mn"
    )


@pytest.mark.parametrize(
    "ayah_text,token_substr,expected_role",
    [
        (
            "صِرَاطَ الَّذِينَ أَنْعَمْتَ عَلَيْهِمْ غَيْرِ الْمَغْضُوبِ عَلَيْهِمْ وَلَا الضَّالِّينَ",
            "مغضوب",
            "مضاف إليه",
        ),
    ],
)
def test_patch17_idafa_over_verbal_obj(ayah_text: str, token_substr: str, expected_role: str) -> None:
    r = run_pipeline(ayah_text)
    l17 = r["layer_outputs"].get("L17_RULE_BASED_I3RAB") or {}
    rows = (l17.get("transformation_result") or {}).get("token_reasoning") or []
    hit = None
    for row in rows:
        w = str(row.get("surface") or row.get("word") or "")
        if token_substr in w or token_substr in _strip_diacritics(w):
            hit = row
            break
    assert hit is not None, f"no token containing {token_substr!r}"
    assert (hit.get("syntactic_role") or "").strip() == expected_role
