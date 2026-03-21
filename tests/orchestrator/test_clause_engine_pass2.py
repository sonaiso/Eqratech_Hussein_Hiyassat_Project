# -*- coding: utf-8 -*-
"""
Stage 16 CLAUSE_ENGINE — Pass 2: hal (جملة حالية), tamyiz (عدد), sila (صلة موصول).
Additive to Pass 1; does not remove or rewrite conditional clauses.
"""

from __future__ import annotations

import pytest

from orchestrator.clause_engine import build_clause_output
from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.loader import lookup_i3rab

from tests.orchestrator.test_clause_engine import build_mock_lo_for


def _ce_tr(r: dict) -> dict:
    lo = r.get("layer_outputs") or {}
    ce = lo.get("CLAUSE_ENGINE") or {}
    return ce.get("transformation_result") or ce


def test_hal_waw_merged_wehuwa():
    r = run_pipeline("جَاءَ زَيْدٌ وَهُوَ يَبْكِي")
    tr = _ce_tr(r)
    assert tr.get("hal_detected") is True
    hal = next(c for c in tr["clause_analysis"] if c.get("clause_type") == "hal_clause")
    assert hal.get("hal_marker") == "و"
    assert 0.70 <= hal.get("confidence", 0) <= 0.80


def test_tamyiz_number_pipeline():
    r = run_pipeline("اشْتَرَيْتُ عِشْرِينَ كِتَاباً")
    tr = _ce_tr(r)
    assert tr.get("tamyiz_detected") is True
    tam = next(c for c in tr["clause_analysis"] if c.get("clause_type") == "tamyiz_phrase")
    assert tam.get("tamyiz_type") == "adad"
    assert tam.get("tamyiz_noun_token_id") is not None


def test_sila_alladhi():
    r = run_pipeline("جَاءَ الَّذِي يَعْلَمُ")
    tr = _ce_tr(r)
    assert tr.get("sila_detected") is True
    mawsul = next(c for c in tr["clause_analysis"] if c.get("clause_type") == "ism_mawsul")
    sila = next(c for c in tr["clause_analysis"] if c.get("clause_type") == "sila_mawsul")
    assert sila.get("antecedent_token_id") == mawsul.get("start_token_id")
    assert sila.get("i3rab_note") == "لا محل لها من الإعراب"


def test_pass1_conditional_unchanged():
    r = run_pipeline("لَوْ ضُرِبَ الظَّالِمُ لَمَا ظَلَمَ")
    tr = _ce_tr(r)
    assert tr.get("conditional_structure_detected") is True
    assert tr.get("hal_detected") is False
    assert tr.get("tamyiz_detected") is False
    assert tr.get("sila_detected") is False
    ids = [c["clause_id"] for c in tr["clause_analysis"]]
    assert "shart_particle_0" in ids and "feil_shart_0" in ids
    assert "jawab_particle_0" in ids and "jawab_shart_0" in ids


def test_no_false_positives_simple():
    r = run_pipeline("ضَرَبَ زَيْدٌ عَمْرًا")
    tr = _ce_tr(r)
    assert tr.get("hal_detected") is False
    assert tr.get("tamyiz_detected") is False
    assert tr.get("sila_detected") is False


def test_sila_man():
    r = run_pipeline("جَاءَ مَنْ عَلِمَ")
    tr = _ce_tr(r)
    assert tr.get("sila_detected") is True


def test_tamyiz_from_l12_tamyiz_relation():
    lo = build_mock_lo_for("عشرة كتب")
    lo["L12_GENDER_NUMBER"] = {
        "transformation_result": {
            "token_features": [
                {
                    "token_id": "0",
                    "surface": "عشرة",
                    "tamyiz_relation": "1",
                }
            ],
            "agreement_summary": {},
        }
    }
    r = build_clause_output(lo)
    assert r.get("tamyiz_detected") is True
    tam = next(c for c in r["clause_analysis"] if c.get("clause_type") == "tamyiz_phrase")
    assert tam.get("tamyiz_noun_token_id") == "1"
    assert tam.get("rule") == "l12_tamyiz_relation"


def test_hal_inside_conditional_mock():
    lo = build_mock_lo_for("إن جاء زيد رَاكِبًا نجح")
    r = build_clause_output(lo)
    assert r.get("conditional_structure_detected") is True
    assert r.get("hal_detected") is True
    hal = next(c for c in r["clause_analysis"] if c.get("clause_type") == "hal_clause")
    assert hal.get("parent_clause_id") == "feil_shart_0"


def test_output_shape_pass2_fields():
    r = run_pipeline("جَاءَ الَّذِي يَعْلَمُ")
    tr = _ce_tr(r)
    for key in ("hal_detected", "tamyiz_detected", "sila_detected", "clause_analysis", "clause_count"):
        assert key in tr
    sila = next(c for c in tr["clause_analysis"] if c.get("clause_type") == "sila_mawsul")
    assert "antecedent_token_id" in sila and "i3rab_note" in sila


def test_pass1_regressions_import():
    from tests.orchestrator import test_clause_engine as t1

    assert hasattr(t1, "test_double_conditional_lw_lama")


@pytest.mark.skipif(
    lookup_i3rab(12, 16, "يَبْكُونَ") is None,
    reason="Gold row missing in data/quran_i3rab.csv",
)
def test_q12_16_hal_gold():
    g = lookup_i3rab(12, 16, "يَبْكُونَ") or ""
    assert "لِلْفَاعِلِ" in g or "حَالٌ" in g
    r = run_pipeline("وَجَاءُوا أَبَاهُمْ عِشَاءً يَبْكُونَ")
    tr = _ce_tr(r)
    assert tr.get("hal_detected") is True


@pytest.mark.skipif(
    lookup_i3rab(2, 6, "كَفَرُوا") is None,
    reason="Gold row missing in data/quran_i3rab.csv",
)
def test_q2_6_sila_gold():
    assert "صِلَة" in (lookup_i3rab(2, 6, "كَفَرُوا") or "") or "محل" in (lookup_i3rab(2, 6, "كَفَرُوا") or "")
    r = run_pipeline("إِنَّ الَّذِينَ كَفَرُوا")
    tr = _ce_tr(r)
    assert tr.get("sila_detected") is True
