# -*- coding: utf-8 -*-
"""
Batch 2.8 — Report presentation cleanup: L17-first, appendix L11/L11B, single headline confidence.
Presentation-only tests on scripts/analyze_sentence.render_report.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from orchestrator.pipeline_orchestrator import run_pipeline

import analyze_sentence

from tests.test_preferred_i3rab_integration import LONG_INNA_KATHIRA


def _report(text: str) -> str:
    raw = run_pipeline(text)
    compact = analyze_sentence.build_compact_json(raw, text)
    return analyze_sentence.render_report(compact)


def test_batch_28_l17_rendered_before_l11_appendix():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    i_l17 = r.find("L17 — الإعراب القواعدي")
    i_l11_app = r.find("للاستئناس فقط")
    assert i_l17 != -1 and i_l11_app != -1
    assert i_l17 < i_l11_app


def test_batch_28_l11_marked_reference_only():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    assert "للاستئناس فقط" in r or "مرجعية" in r
    assert "هذه طبقة سطحية نصية مرجعية" in r


def test_batch_28_single_headline_confidence_not_competing_with_raw_one():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    # Exactly one executive line uses **الثقة النهائية:** in the primary summary
    assert r.count("**الثقة النهائية:**") == 1
    # Avoid misleading "ثقة: 1" headline pattern (raw validation) in user-facing report body
    assert "ثقة: 1" not in r
    assert "ثقة:1" not in r


def test_batch_28_no_duplicate_main_title():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    assert r.count("# تحليل الجملة — النظام المباشر") == 1


def test_batch_28_l11_appendix_after_l17_and_summary():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    i_sum = r.find("## ملخص تنفيذي")
    i_l17 = r.find("## L17 — الإعراب القواعدي")
    i_app = r.find("## ملحق — الطبقات المرجعية")
    assert i_sum < i_l17 < i_app


def test_batch_28_khabar_in_section_near_l17_long_inna():
    r = _report(LONG_INNA_KATHIRA)
    i_l17 = r.find("## L17 — الإعراب القواعدي")
    i_kh = r.find("## خبر إن")
    i_app = r.find("## ملحق — الطبقات المرجعية")
    assert i_l17 != -1 and i_kh != -1
    assert i_l17 < i_kh < i_app
    assert "`24`" in r and "`29`" in r


def test_batch_28_preferred_i3rab_data_unchanged():
    raw = run_pipeline("ضَرَبَ زَيْدٌ عَمْراً")
    compact = analyze_sentence.build_compact_json(raw, "ضَرَبَ زَيْدٌ عَمْراً")
    assert "preferred_i3rab" in compact
    assert "final_structured_i3rab_summary" in compact
    assert (compact.get("preferred_i3rab") or {}).get("preferred_rows")


def test_batch_28_l11b_diagnostic_label_present():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    assert "L11B — الإعراب البنيوي القديم (تشخيصي)" in r


def test_batch_28_appendix_has_preferred_reference_table_when_rows_exist():
    r = _report("ضَرَبَ زَيْدٌ عَمْراً")
    assert "مرجع تفضيل المصدر" in r
