# -*- coding: utf-8 -*-
"""Batch 28.30 — reporting-verb frame (قَالَ / قُلْ family): L14 + Stage 15 narrow guards."""

from __future__ import annotations

from orchestrator.l14_jamid_mushtaq import (
    is_qul_family_amr_surface,
    is_reporting_na_finite_surface,
)
from orchestrator.pipeline_orchestrator import run_pipeline


def test_b28_30_qala_yaa_adam_l14_and_no_false_matrix_subj_links():
    """قَالَ يَاآدَمُ أَنْبِئْهُمْ بِأَسْمَائِهِمْ — vocative + PP must not attach as matrix SUBJ to قَالَ."""
    r = run_pipeline("قَالَ يَاآدَمُ أَنْبِئْهُمْ بِأَسْمَائِهِمْ")
    l14 = ((r.get("layer_outputs") or {}).get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    by_surf = {(x.get("surface") or "").strip(): x for x in (l14.get("token_classifications") or [])}
    assert (by_surf.get("قَالَ") or {}).get("derivational_class") == "VERB"
    assert (by_surf.get("يَاآدَمُ") or {}).get("rule") == "B28_30_fused_yaa_nida_munada"
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    for l in links:
        if l.get("head_id") == "0" and l.get("relation") == "SUBJ":
            raise AssertionError(f"unexpected matrix SUBJ from قَالَ: {l}")


def test_b28_30_qul_family_amr_surface_helper():
    assert is_qul_family_amr_surface("قُلْ")
    assert is_qul_family_amr_surface("أَقُلْ")
    assert is_qul_family_amr_surface("وَقُلْ")
    assert is_qul_family_amr_surface("قُولُوا")
    assert not is_qul_family_amr_surface("قَالَ")
    assert not is_qul_family_amr_surface("قَلْب")
    assert not is_qul_family_amr_surface("أَقْلَم")
    assert not is_qul_family_amr_surface("قَوْلٌ")


def test_b28_30_reporting_na_finite_surface_helper():
    assert is_reporting_na_finite_surface("آمَنَّا")
    assert is_reporting_na_finite_surface("سَمِعْنَا")
    assert is_reporting_na_finite_surface("أَطَعْنَا")
    assert is_reporting_na_finite_surface("وَأَطَعْنَا")
    assert not is_reporting_na_finite_surface("هُنَا")
    assert not is_reporting_na_finite_surface("أَنَا")


def test_b28_30_qul_and_na_l14_verb_not_noun():
    """Priority 1+2: L14 must classify قُلْ / قُلْنَا / آمَنَّا as VERB when L5 is weak."""
    for text, surf in [
        ("قُلْ هُوَ اللَّهُ", "قُلْ"),
        ("قُلْنَا اهْبِطُوا", "قُلْنَا"),
        ("قَالُوا آمَنَّا", "آمَنَّا"),
    ]:
        r = run_pipeline(text)
        l14 = ((r.get("layer_outputs") or {}).get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
        row = next((x for x in (l14.get("token_classifications") or []) if (x.get("surface") or "").strip() == surf), None)
        assert row is not None, surf
        assert row.get("derivational_class") == "VERB", (surf, row)


def test_b28_30_second_qala_no_qul_as_subj():
    """After second قَالَ, أَقُلْ must not be chosen as post-verbal nominal SUBJ."""
    r = run_pipeline("قَالَ أَلَمْ أَقُلْ لَكُمْ")
    dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    for l in links:
        if (
            l.get("head_id") == "0"
            and l.get("dependent_id") == "2"
            and l.get("relation") == "SUBJ"
        ):
            raise AssertionError(f"أَقُلْ must not be SUBJ of matrix verb: {l}")
