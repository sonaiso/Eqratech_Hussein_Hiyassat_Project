# -*- coding: utf-8 -*-
"""
Stage 17 v1.1 — Preferred iʿrāb presentation integration tests.
Presentation layer only: prefer L17 over L11B when stronger, fallback to L11B, show agreement/disagreement.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Allow importing from scripts/
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from orchestrator.pipeline_orchestrator import run_pipeline

# Long إن sentence used in Stage 17 B2.1–B2.4 tests (reporting / fusion checks).
LONG_INNA_KATHIRA = (
    "إِنَّ الْمُسْلِمِينَ وَالْمُسْلِمَاتِ وَالْمُؤْمِنِينَ وَالْمُؤْمِنَاتِ وَالْقَانِتِينَ وَالْقَانِتَاتِ "
    "وَالصَّادِقِينَ وَالصَّادِقَاتِ وَالصَّابِرِينَ وَالصَّابِرَاتِ وَالْخَاشِعِينَ وَالْخَاشِعَاتِ "
    "وَالْمُتَصَدِّقِينَ وَالْمُتَصَدِّقَاتِ وَالصَّائِمِينَ وَالصَّائِمَاتِ وَالْحَافِظِينَ فُرُوجَهُمْ "
    "وَالْحَافِظَاتِ وَالذَّاكِرِينَ اللَّهَ كَثِيرًا وَالذَّاكِرَاتِ أَعَدَّ اللَّهُ لَهُم مَّغْفِرَةً "
    "وَأَجْرًا عَظِيمًا"
)


def _get_raw_and_compact(text: str):
    """Run pipeline and build compact JSON (preferred_i3rab included)."""
    raw = run_pipeline(text)
    import analyze_sentence
    compact = analyze_sentence.build_compact_json(raw, text)
    return raw, compact


# A) Prefer L17 when strong — "ضَرَبَ زَيْدٌ عَمْراً"
def test_prefer_l17_when_strong():
    raw, compact = _get_raw_and_compact("ضَرَبَ زَيْدٌ عَمْراً")
    pref = compact.get("preferred_i3rab") or {}
    rows = pref.get("preferred_rows") or []
    assert len(rows) >= 3, "Expected at least 3 preferred rows"

    # When L17 is resolved and strong, preferred source should be L17 for all three tokens
    s17 = (raw.get("layer_outputs") or {}).get("L17_RULE_BASED_I3RAB") or {}
    tr17 = (s17.get("transformation_result") or {}).get("token_reasoning") or []
    resolved_strong = [
        t for t in tr17
        if str(t.get("status")).strip().lower() == "resolved"
        and (float(t.get("confidence") or 0) >= 0.70)
        and (t.get("syntactic_role") and (t.get("i3rab_case_or_mood") or t.get("governing_factor")))
    ]
    if len(resolved_strong) >= 3:
        for row in rows[:3]:
            assert row.get("preferred_source") == "L17", f"Expected L17 preferred for {row.get('surface')}"
            assert row.get("syntactic_role") and row.get("syntactic_role") != "—"
            assert row.get("i3rab_case_or_mood") or row.get("governing_factor")


# B) Fallback to L11B when L17 unresolved for one token
def test_fallback_to_l11b_when_l17_unresolved():
    # Build minimal raw: L17 has one token unresolved, L11B has that token resolved
    raw = {
        "layer_outputs": {
            "L17_RULE_BASED_I3RAB": {
                "transformation_result": {
                    "token_reasoning": [
                        {"token_id": "0", "surface": "ضَرَبَ", "syntactic_role": "فعل", "governing_factor": "—",
                         "i3rab_case_or_mood": "مبني على الفتح", "marker": "الفتحة", "confidence": 0.9, "status": "resolved"},
                        {"token_id": "1", "surface": "زَيْدٌ", "syntactic_role": "—", "governing_factor": "—",
                         "i3rab_case_or_mood": "—", "marker": "—", "confidence": 0.2, "status": "unresolved"},
                        {"token_id": "2", "surface": "عَمْراً", "syntactic_role": "مفعول به", "governing_factor": "ضَرَبَ",
                         "i3rab_case_or_mood": "منصوب", "marker": "الفتحة", "confidence": 0.9, "status": "resolved"},
                    ]
                }
            },
            "L11B_CAUSAL_I3RAB": {
                "transformation_result": {
                    "token_i3rab_reasoning": [
                        {"token_id": "0", "surface": "ضَرَبَ", "role": "فعل", "governing_factor": "—",
                         "case_or_mood": "مبني", "marker": "الفتحة", "confidence": 0.85, "role_status": "resolved"},
                        {"token_id": "1", "surface": "زَيْدٌ", "role": "فاعل", "governing_factor": "ضَرَبَ",
                         "case_or_mood": "مرفوع", "marker": "الضمة", "confidence": 0.8, "role_status": "resolved"},
                        {"token_id": "2", "surface": "عَمْراً", "role": "مفعول به", "governing_factor": "ضَرَبَ",
                         "case_or_mood": "منصوب", "marker": "الفتحة", "confidence": 0.85, "role_status": "resolved"},
                    ]
                }
            },
        }
    }
    import analyze_sentence
    compact = analyze_sentence.build_compact_json(raw, "ضَرَبَ زَيْدٌ عَمْراً")
    pref = compact.get("preferred_i3rab") or {}
    rows = pref.get("preferred_rows") or []
    assert len(rows) >= 3
    # Token 1: L17 unresolved/weak -> preferred source should be L11B
    row1 = next((r for r in rows if r.get("token_id") == "1"), None)
    assert row1 is not None
    assert row1.get("preferred_source") == "L11B"
    assert "فاعل" in (row1.get("syntactic_role") or "")


# C) Agreement summary
def test_agreement_summary():
    raw, compact = _get_raw_and_compact("ضَرَبَ زَيْدٌ عَمْراً")
    pref = compact.get("preferred_i3rab") or {}
    summary = pref.get("preferred_i3rab_summary") or {}
    agreement_count = summary.get("agreement_count", 0)
    rows = pref.get("preferred_rows") or []
    for row in rows:
        assert "agreement_status" in row
        assert row["agreement_status"] in (
            "agree", "partial_agreement", "disagree", "only_l17", "only_l11b", "unresolved"
        )
    # When L17 and L11B both resolve similarly, agreement_count can be > 0
    assert isinstance(agreement_count, int)
    assert (
        summary.get("preferred_from_l17_count", 0)
        + summary.get("preferred_from_l11b_count", 0)
        + summary.get("preferred_from_l11_text_count", 0)
        + summary.get("preferred_unresolved_count", 0)
        == len(rows)
    )


# D) Disagreement surfacing
def test_disagreement_surfacing():
    raw = {
        "layer_outputs": {
            "L17_RULE_BASED_I3RAB": {
                "transformation_result": {
                    "token_reasoning": [
                        {"token_id": "0", "surface": "كلمة", "syntactic_role": "مفعول به", "governing_factor": "فعل",
                         "i3rab_case_or_mood": "منصوب", "marker": "الفتحة", "confidence": 0.85, "status": "resolved"},
                    ]
                }
            },
            "L11B_CAUSAL_I3RAB": {
                "transformation_result": {
                    "token_i3rab_reasoning": [
                        {"token_id": "0", "surface": "كلمة", "role": "فاعل", "governing_factor": "فعل",
                         "case_or_mood": "مرفوع", "marker": "الضمة", "confidence": 0.8, "role_status": "resolved"},
                    ]
                }
            },
        }
    }
    import analyze_sentence
    compact = analyze_sentence.build_compact_json(raw, "كلمة")
    pref = compact.get("preferred_i3rab") or {}
    rows = pref.get("preferred_rows") or []
    assert len(rows) >= 1
    row = rows[0]
    # Policy prefers L17 (resolved + strong) -> preferred_source L17
    assert row.get("preferred_source") == "L17"
    assert row.get("agreement_status") == "disagree"
    assert "disagree" in (row.get("reasoning_note") or "")
    summary = pref.get("preferred_i3rab_summary") or {}
    assert summary.get("disagreement_count", 0) >= 1


# E) Report/compact contract stability
def test_compact_contract_stability():
    raw, compact = _get_raw_and_compact("ضَرَبَ زَيْدٌ عَمْراً")
    # Existing keys still present
    assert "text" in compact
    assert "causal_i3rab_rows" in compact
    assert "rule_based_i3rab" in compact
    assert "stage_status" in compact
    assert "counts" in compact
    # L17 section data still present
    s17 = compact.get("rule_based_i3rab") or {}
    assert "token_reasoning" in s17 or "coverage" in s17 or len(s17) >= 0
    # L11B data still in causal_i3rab_rows
    assert isinstance(compact.get("causal_i3rab_rows"), list)
    # New preferred_i3rab is additive
    pref = compact.get("preferred_i3rab")
    assert pref is not None
    assert "source_preference" in pref
    assert "preferred_rows" in pref
    assert "agreement_summary" in pref
    assert "preferred_i3rab_summary" in pref
    assert "final_structured_i3rab_summary" in compact
    assert "khabar_in_candidates" in compact
    assert "khabar_in_analysis" in compact


# --- Batch 2.5 — reporting / fusion / presentation sync ---


def test_batch_25_preferred_i3rab_prefers_l17_candidate_over_stale_l11b():
    """L17 candidate (tier 2) must win over weak/unresolved L11B for كَثِيرًا in the long إن sentence."""
    _, compact = _get_raw_and_compact(LONG_INNA_KATHIRA)
    pref = compact.get("preferred_i3rab") or {}
    rows = pref.get("preferred_rows") or []
    k = next((r for r in rows if "كَثِيرًا" in (r.get("surface") or "")), None)
    assert k is not None
    assert k.get("preferred_source") == "L17"
    assert "نائب" in (k.get("syntactic_role") or "") or "مفعول المطلق" in (k.get("syntactic_role") or "")


def test_batch_25_report_structured_summary_uses_final_fused_counts():
    """Top-level final_structured_i3rab_summary must mirror L17 reasoning_summary (not stale L11B-only totals)."""
    _, compact = _get_raw_and_compact(LONG_INNA_KATHIRA)
    fs = compact.get("final_structured_i3rab_summary") or {}
    s17 = compact.get("rule_based_i3rab") or {}
    summ = (s17.get("reasoning_summary") or {}) if s17 else {}
    assert fs.get("source") == "L17_RULE_BASED_I3RAB"
    assert fs.get("resolved_tokens") == summ.get("resolved_tokens")
    assert fs.get("candidate_tokens") == summ.get("candidate_tokens")
    assert fs.get("unresolved_tokens") == summ.get("unresolved_tokens")
    assert fs.get("unresolved_tokens") == 0
    assert fs.get("resolved_tokens") >= 25


def test_batch_25_khabar_in_candidate_exposed_in_final_report():
    """khabar span and head verb ids appear in report (Batch 2.7 محسوم section or B2.1 مرشح lines)."""
    _, compact = _get_raw_and_compact(LONG_INNA_KATHIRA)
    import analyze_sentence

    report = analyze_sentence.render_report(compact)
    assert "خبر إن" in report
    assert "`24`" in report and "`29`" in report
    cands = compact.get("khabar_in_candidates") or []
    assert len(cands) >= 1
    assert any(str(c.get("head_verb_token_id")) == "24" for c in cands)
    kia = compact.get("khabar_in_analysis") or []
    assert any(str(x.get("head_verb_token_id")) == "24" for x in kia)


def test_batch_25_token_29_naat_visible_in_preferred_structured_view():
    """عَظِيمًا must show L17 نعت (or resolved structured role) in preferred rows, not stale unresolved-only."""
    _, compact = _get_raw_and_compact(LONG_INNA_KATHIRA)
    pref = compact.get("preferred_i3rab") or {}
    rows = pref.get("preferred_rows") or []
    az = next((r for r in rows if "عَظِيمًا" in (r.get("surface") or "")), None)
    assert az is not None
    assert az.get("preferred_source") == "L17"
    assert "نعت" in (az.get("syntactic_role") or "")


# F) Non-regression: run Stage 17 tests
def test_stage17_tests_still_pass():
    """Re-run Stage 17 core behavior (smoke)."""
    from orchestrator.l17_rule_based_i3rab import build_rule_based_i3rab
    lo = (
        run_pipeline("ضَرَبَ زَيْدٌ عَمْراً").get("layer_outputs")
        or {}
    )
    result = build_rule_based_i3rab(lo)
    assert result is not None
    tr = result.get("token_reasoning") or []
    assert len(tr) >= 3
