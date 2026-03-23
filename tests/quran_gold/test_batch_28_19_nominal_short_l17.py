# -*- coding: utf-8 -*-
"""Batch 28.19 — L17 B28_19_NOMINAL_SHORT: short nominal مبتدأ/خبر without Stage15 SUBJ/PRED."""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


def _l17_roles(text: str) -> list[tuple[str, str, str]]:
    r = run_pipeline(text)
    lo = r.get("layer_outputs") or {}
    s17 = lo.get("L17_RULE_BASED_I3RAB") or {}
    tr = s17.get("transformation_result") or {}
    out: list[tuple[str, str, str]] = []
    for t in tr.get("token_reasoning") or []:
        out.append(
            (
                (t.get("surface") or "").strip(),
                (t.get("syntactic_role") or "").strip(),
                (t.get("status") or "").strip(),
            )
        )
    return out


def test_101_1_al_qariah_mubtada():
    roles = _l17_roles("الْقَارِعَةُ")
    assert roles[0][0] == "الْقَارِعَةُ"
    assert roles[0][1] == "مبتدأ"
    assert roles[0][2] == "resolved"


def test_112_2_allahu_samadu_khabar():
    roles = _l17_roles("اللَّهُ الصَّمَدُ")
    assert any(s == "اللَّهُ" and r == "مبتدأ" for s, r, _ in roles)
    assert any(s == "الصَّمَدُ" and r == "خبر" for s, r, _ in roles)


def test_55_1_ar_rahman_mubtada():
    roles = _l17_roles("الرَّحْمَنُ")
    assert roles[0][0] == "الرَّحْمَنُ"
    assert roles[0][1] == "مبتدأ"


def test_wa_ad_duha_skipped_no_false_mubtada():
    """Attached وَال… first noun — rule defers (often معطوف / not bare مبتدأ)."""
    roles = _l17_roles("وَالضُّحَى")
    assert not any("مبتدأ" in r for _, r, _ in roles)


def test_fatiha_1_2_no_regression_hamdu():
    """1:2 — الحمد مبتدأ via Stage15 PRED / B28_14; must stay مبتدأ."""
    text = "الْحَمْدُ لِلَّهِ رَبِّ الْعَالَمِينَ"
    roles = _l17_roles(text)
    hamd = next((r for s, r, _ in roles if "حَمْد" in s), "")
    assert hamd == "مبتدأ"


def test_b28_19_ref_tag_present():
    r = run_pipeline("الرَّحْمَنُ")
    lo = r.get("layer_outputs") or {}
    tr = (lo.get("L17_RULE_BASED_I3RAB") or {}).get("transformation_result") or {}
    toks = tr.get("token_reasoning") or []
    assert any("B28_19_NOMINAL_SHORT" in (t.get("gold_rule_refs") or []) for t in toks)
