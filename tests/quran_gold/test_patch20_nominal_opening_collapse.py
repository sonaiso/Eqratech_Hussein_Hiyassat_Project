# -*- coding: utf-8 -*-
"""Patch 20 (final L14-only): nominal blockers gate finite-skeleton verb promotion.

An L8B derived-active R2 kasra/damma exclusion was reverted (ERQA integrity); فَعِيل/فَعُول
synthetic cases are not asserted here.
"""

from __future__ import annotations

import pytest

from orchestrator.l14_jamid_mushtaq import build_jamid_mushtaq, has_strong_true_verb_evidence
from orchestrator.l8b_verb_bab_governance import _has_strong_finite_verb_surface
from orchestrator.pipeline_orchestrator import run_pipeline
from orchestrator.quran_gold.analyzer_extract import extract_snapshots
from orchestrator.quran_gold.comparator import compare_token_conservative


def _snap_for_word(p: dict, surface: str):
    for s in extract_snapshots(p):
        if (s.surface or "").strip() == surface.strip():
            return s
    return None


@pytest.mark.parametrize(
    "surface,kind,wazn",
    [
        ("عَذَابٌ", "noun", "فَعَلٌ"),
        ("أُولَئِكَ", "demonstrative", ""),
    ],
)
def test_patch20_finite_skeleton_blocked_when_nominal_blocker(surface: str, kind: str, wazn: str):
    """L8B finite skeleton still fires, but L14 strong-verb gate respects nominal blockers (tanween / إشارة)."""
    wrow: dict = {"word": surface, "kind": kind}
    if wazn:
        wrow["template"] = wazn
        wrow["word_wazn"] = wazn
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [wrow]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": "ف-ع-ل"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [wrow]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    assert _has_strong_finite_verb_surface(surface) is True
    assert has_strong_true_verb_evidence("1", surface, lo) is False


def test_patch20_l14_noun_tanween_not_verb():
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "عَذَابٌ"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "عَذَابٌ", "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "عَذَابٌ", "root": "ع-ذ-ب"}]}},
        "L9_WAZN_MATCHING": {
            "transformation_result": {"words": [{"word": "عَذَابٌ", "template": "فَعَلٌ", "word_wazn": "فَعَلٌ"}]},
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    tc = build_jamid_mushtaq(lo)["token_classifications"][0]
    assert tc.get("derivational_class") != "VERB"


def test_patch20_full_pipeline_marad_ayah_token_not_verb_family():
    """2:10 مَرَضٌ — gold مبتدأ; L17 grammatical family must not be verb (nominal-opening collapse guard)."""
    p = run_pipeline(
        "فِي قُلُوبِهِمْ مَرَضٌ فَزَادَهُمُ اللَّهُ مَرَضًا وَلَهُمْ عَذَابٌ أَلِيمٌ بِمَا كَانُوا يَكْذِبُونَ"
    )
    snap = _snap_for_word(p, "مَرَضٌ")
    assert snap is not None
    dec = compare_token_conservative(
        "مُبْتَدَأٌ مُؤَخَّرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
        snap,
        repair_pass=False,
    )
    fam = ((dec.trace or {}).get("l17_family_guess") or "").strip().lower()
    assert fam != "verb"


def test_patch20_wallahu_pipeline_l17_not_verb_family():
    """2:19 وَاللَّهُ — gold مبتدأ (اسم الجلالة); must not be classified as verbal family."""
    p = run_pipeline(
        "أَوْ كَصَيِّبٍ مِنَ السَّمَاءِ فِيهِ ظُلُمَاتٌ وَرَعْدٌ وَبَرْقٌ يَجْعَلُونَ أَصَابِعَهُمْ فِي آذَانِهِمْ مِنَ الصَّوَاعِقِ حَذَرَ الْمَوْتِ وَاللَّهُ مُحِيطٌ بِالْكَافِرِينَ"
    )
    snap = _snap_for_word(p, "وَاللَّهُ")
    assert snap is not None
    dec = compare_token_conservative(
        '"" الْوَاوُ "" حَرْفُ اسْتِئْنَافٍ مَبْنِيٌّ عَلَى الْفَتْحِ، وَاسْمُ الْجَلَالَةِ مُبْتَدَأٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.',
        snap,
        repair_pass=False,
    )
    fam = ((dec.trace or {}).get("l17_family_guess") or "").strip().lower()
    assert fam != "verb"

