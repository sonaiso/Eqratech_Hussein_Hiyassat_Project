# -*- coding: utf-8 -*-
"""Batch 28.19 — L17 B28_19_NOMINAL_SHORT: مبتدأ/خبر on short nominal inputs via full pipeline."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


def _l17_roles(text: str) -> list[tuple[str, str]]:
    r = run_pipeline(text)
    lo = r.get("layer_outputs") or {}
    s17 = lo.get("L17_RULE_BASED_I3RAB") or {}
    tr = s17.get("transformation_result") or {}
    out: list[tuple[str, str]] = []
    for t in tr.get("token_reasoning") or []:
        out.append(
            (
                (t.get("surface") or "").strip(),
                (t.get("syntactic_role") or "").strip(),
            )
        )
    return out


def test_al_qariah_mubtada():
    roles = _l17_roles("الْقَارِعَةُ")
    assert roles[0][0] == "الْقَارِعَةُ"
    assert roles[0][1] == "مبتدأ"


def test_allahu_samadu_mubtada_khabar():
    roles = _l17_roles("اللَّهُ الصَّمَدُ")
    assert any(s == "اللَّهُ" and r == "مبتدأ" for s, r in roles)
    assert any(s == "الصَّمَدُ" and r == "خبر" for s, r in roles)


def test_ar_rahman_mubtada():
    roles = _l17_roles("الرَّحْمَنُ")
    assert roles[0][0] == "الرَّحْمَنُ"
    assert roles[0][1] == "مبتدأ"
