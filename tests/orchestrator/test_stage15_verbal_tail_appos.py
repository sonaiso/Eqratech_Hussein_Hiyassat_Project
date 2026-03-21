# -*- coding: utf-8 -*-
"""
Batch 1.3 / 1.5: Stage 15 — verbal-tail APPOS competition; long وَالـ chain repair (L5 verb vs L14 ISM_FAIL).
"""

from __future__ import annotations

from orchestrator.pipeline_orchestrator import run_pipeline


LONG_INNA = (
    "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
    "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
    "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
    "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً "
    "وَأَجْرًا عَظِيمًا"
)


def test_long_inna_tail_no_false_appos():
    r = run_pipeline(LONG_INNA)
    links = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or []
    appos = [l for l in links if l.get("relation") == "APPOS"]
    assert not appos, f"expected no APPOS in verbal tail, got {appos}"


def test_long_inna_sifa_on_waw_conjunct_adjective():
    r = run_pipeline(LONG_INNA)
    links = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or []
    sifa = [l for l in links if l.get("relation") == "SIFA" and l.get("head_id") == "28" and l.get("dependent_id") == "29"]
    assert len(sifa) >= 1
    assert sifa[0].get("rule", "").startswith("Pass_C_sifa_after_appos_suppression")


def test_suppression_logged_in_corrections():
    r = run_pipeline(LONG_INNA)
    ds = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"]
    log = ds.get("corrections_log") or []
    suppressed = [
        e for e in log
        if (e.get("stage15_decision") or {}).get("suppressed") is True
        and "appos" in (e.get("override_reason") or "").lower()
    ]
    assert len(suppressed) >= 1
    reasons = " ".join((e.get("override_reason") or "") for e in suppressed)
    assert "Pass_C_appos_suppressed" in reasons


def test_batch_15_coord_chain_includes_token_13_no_skip():
    """
    L5 may tag وَالْمُتَصَدِّقِينَ (token 13) as 'verb' while L14 = ISM_FAIL; Pass 5b must still
    emit COORD 12→13 and 13→14 (no jump 12→14).
    """
    r = run_pipeline(LONG_INNA)
    links = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or []
    coord_pairs = {(l.get("head_id"), l.get("dependent_id")) for l in links if l.get("relation") == "COORD"}
    assert ("12", "13") in coord_pairs
    assert ("13", "14") in coord_pairs
    assert ("12", "14") not in coord_pairs


def test_batch_12_resume_coord_20_to_23_preserved():
    """After participial object + intensifier; chain resumes to وَالذَّاكِرَاتِ — do not regress."""
    r = run_pipeline(LONG_INNA)
    links = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or []
    coord_pairs = {(l.get("head_id"), l.get("dependent_id")) for l in links if l.get("relation") == "COORD"}
    assert ("20", "23") in coord_pairs


def test_no_obj_spill_onto_aadda_finite_verb():
    """Batch 1.1: finite verb أَعَدَّ (token 24) must not appear as OBJ dependent of a participle."""
    r = run_pipeline(LONG_INNA)
    links = r["layer_outputs"]["DEPENDENCY_SYNTAX_BUILDER"].get("dependency_links") or []
    obj_to_24 = [l for l in links if l.get("relation") == "OBJ" and l.get("dependent_id") == "24"]
    assert not obj_to_24, f"unexpected OBJ treating token 24 as object: {obj_to_24}"
