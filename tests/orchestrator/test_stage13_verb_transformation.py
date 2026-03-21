# -*- coding: utf-8 -*-
"""
Stage 13 Verb Transformation tests.
"""

from __future__ import annotations

from orchestrator.l13_verb_transformation import (
    apply_root_to_wazn,
    build_verb_transformation,
)

from .conftest import assert_has_section, run_pipeline_for_test


def _mock_lo(
    surface: str,
    *,
    root: str | None = "ض-ر-ب",
    root_type: str | None = "صحيح سالم",
    bab: str | None = "فَعَلَ-يَفْعِلُ",
    bab_status: str = "resolved",
    past_pattern: str = "فَعَلَ",
    present_pattern: str = "يَفْعِلُ",
    present_passive_pattern: str = "يُفْعَلُ",
    derivational_class: str = "VERB",
    voice: str = "active",
    include_l8b_profile: bool = True,
) -> dict:
    profiles = []
    if include_l8b_profile:
        profiles.append({
            "token_id": "0",
            "surface": surface,
            "root": root,
            "root_type": root_type,
            "bab": bab,
            "bab_status": bab_status,
            "voice": voice,
            "confidence": 0.92 if bab_status == "resolved" else 0.4,
            "tense_mapping": {
                "past_pattern": past_pattern,
                "present_pattern": present_pattern,
                "present_passive_pattern": present_passive_pattern,
            },
        })
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": "verb" if derivational_class == "VERB" else "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": root}]}},
        "L8B_VERB_BAB_GOVERNANCE": {
            "transformation_result": {
                "verb_governance_profiles": profiles
            }
        },
        "L14_JAMID_MUSHTAQ": {
            "transformation_result": {
                "token_classifications": [{
                    "token_id": "0",
                    "surface": surface,
                    "root": root,
                    "derivational_class": derivational_class,
                }]
            }
        },
    }


def _first_row(result: dict) -> dict:
    rows = result["verb_transformations"]
    assert len(rows) == 1
    return rows[0]


def test_stage13_in_stage_order_after_l14_before_l12():
    from orchestrator.types import STAGE_ORDER

    idx = STAGE_ORDER.index("L13_VERB_TRANSFORMATION")
    assert STAGE_ORDER[idx - 1] == "L14_JAMID_MUSHTAQ"
    assert STAGE_ORDER[idx + 1] == "L12_GENDER_NUMBER"


def test_apply_root_to_wazn_replaces_fa_ain_lam():
    assert apply_root_to_wazn("ض-ر-ب", "يَفْعِلُ") == "يَضْرِبُ"
    assert apply_root_to_wazn("س-ب-ح", "تَفْعِيل") == "تَسْبِيح"


def test_sound_trilateral_active_verb_transformation():
    result = build_verb_transformation(_mock_lo("ضَرَبَ"))
    row = _first_row(result)

    assert row["base_past_active"] == "ضَرَبَ"
    assert row["base_present_active"] == "يَضْرِبُ"
    assert row["base_past_passive"] == "ضُرِبَ"
    assert row["base_present_passive"] == "يُضْرَبُ"
    assert row["masdar"] == "ضَرْب"
    assert row["masdar_wazn"] == "فَعْل"
    assert row["imperative"] == "اِضْرِبْ"
    assert row["tense_of_surface"] == "past"
    assert row["voice_of_surface"] == "active"
    assert row["transformation_confidence"] >= 0.85


def test_passive_surface_populates_passive_fields():
    result = build_verb_transformation(_mock_lo("ضُرِبَ", voice="passive"))
    row = _first_row(result)

    assert row["voice_of_surface"] == "passive"
    assert row["base_past_passive"] == "ضُرِبَ"
    assert row["base_present_passive"] == "يُضْرَبُ"


def test_form_two_derived_masdar_and_imperative():
    result = build_verb_transformation(_mock_lo(
        "سَبَّحَ",
        root="س-ب-ح",
        bab="فَعَّلَ",
        past_pattern="فَعَّلَ",
        present_pattern="يُفَعِّلُ",
        present_passive_pattern="يُفَعَّلُ",
    ))
    row = _first_row(result)

    assert row["base_past_active"] == "سَبَّحَ"
    assert row["base_present_active"] == "يُسَبِّحُ"
    assert row["masdar_wazn"] == "تَفْعِيل"
    assert row["masdar"] == "تَسْبِيح"
    assert row["imperative"] == "سَبِّحْ"


def test_unknown_bab_stays_low_confidence_and_conservative():
    result = build_verb_transformation(_mock_lo(
        "فَعَلَ",
        bab="unknown",
        bab_status="unknown",
        past_pattern="unknown",
        present_pattern="unknown",
        present_passive_pattern="unknown",
    ))
    row = _first_row(result)

    assert row["transformation_confidence"] <= 0.4
    assert "masdar_not_derivable_unknown_bab" in row["limitations"]


def test_non_verb_token_is_skipped():
    result = build_verb_transformation(_mock_lo("زَيْدٌ", derivational_class="JAMID", voice="unknown", include_l8b_profile=False))
    assert result["verb_transformations"] == []


def test_output_shape_contains_required_keys():
    result = build_verb_transformation(_mock_lo("ضَرَبَ"))
    row = _first_row(result)
    required = {
        "token_id",
        "surface",
        "root",
        "root_type",
        "bab",
        "bab_status",
        "base_past_active",
        "base_present_active",
        "base_past_passive",
        "base_present_passive",
        "masdar",
        "masdar_wazn",
        "imperative",
        "tense_of_surface",
        "voice_of_surface",
        "transformation_confidence",
        "transformation_rule",
        "limitations",
    }
    assert required.issubset(row.keys())


def test_transformation_summary_matches_rows():
    result = build_verb_transformation(_mock_lo("ضَرَبَ"))
    summary = result["transformation_summary"]
    assert summary["total_verbs"] == len(result["verb_transformations"])
    assert summary["fully_transformed"] + summary["partially_transformed"] + summary["untransformed"] == summary["total_verbs"]


def test_null_root_yields_all_nulls_and_zero_confidence():
    result = build_verb_transformation(_mock_lo("ضَرَبَ", root=None))
    row = _first_row(result)

    assert row["root"] is None
    assert row["base_past_active"] is None
    assert row["base_present_active"] is None
    assert row["base_past_passive"] is None
    assert row["base_present_passive"] is None
    assert row["masdar"] is None
    assert row["imperative"] is None
    assert row["transformation_confidence"] == 0.0


def test_weak_root_keeps_conservative_limitation():
    result = build_verb_transformation(_mock_lo(
        "دَعَا",
        root="د-ع-و",
        root_type="معتل ناقص",
        bab="فَعَلَ-يَفْعُلُ",
        present_pattern="يَفْعُلُ",
    ))
    row = _first_row(result)

    assert "weak_root_transformation_approximate" in row["limitations"]
    assert row["transformation_confidence"] <= 0.8


def test_pipeline_integration_is_additive_only():
    pipeline = run_pipeline_for_test("ضَرَبَ زَيْدٌ عَمْراً", render_mode="detailed")
    lo = pipeline.get("layer_outputs") or {}

    assert "L13_VERB_TRANSFORMATION" in lo
    stage = (lo.get("L13_VERB_TRANSFORMATION") or {}).get("transformation_result") or {}
    assert stage.get("status") == "success"
    rows = stage.get("verb_transformations") or []
    assert any(row.get("surface") == "ضَرَبَ" for row in rows)

    assert (lo.get("L14_JAMID_MUSHTAQ") or {}).get("status") == "success"
    assert (lo.get("L12_GENDER_NUMBER") or {}).get("status") == "success"
    assert (lo.get("CLAUSE_ENGINE") or {}).get("status") in ("success", "partial")
    assert (lo.get("L17_RULE_BASED_I3RAB") or {}).get("status") == "success"
    assert_has_section(pipeline.get("rendered_output") or {}, "verb_transformations")


# --- Quranic surfaces: authentic spellings; layers mocked so L14=L8B agree on VERB + bab ---


def test_q11_quranic_qala_past_active_masdar():
    """قَالَ (2:30) — surface authentic; L8B/L14 mocked as resolved verb."""
    result = build_verb_transformation(_mock_lo(
        "قَالَ",
        root="ق-و-ل",
        root_type="معتل أجوف",
        bab="فَعَلَ-يَفْعُلُ",
        past_pattern="فَعَلَ",
        present_pattern="يَفْعُلُ",
        present_passive_pattern="يُفْعَلُ",
    ))
    row = _first_row(result)
    assert row["tense_of_surface"] == "past"
    assert row["voice_of_surface"] == "active"
    assert row["masdar"] is not None
    assert row["transformation_confidence"] >= 0.80


def test_q12_quranic_passive_pattern_uhilla_gold_missing_use_synthetic_passive():
    """أُحِلَّ: gold lookup may be None — use same passive paradigm as ضُرِبَ (trilateral)."""
    result = build_verb_transformation(_mock_lo(
        "ضُرِبَ",
        voice="passive",
    ))
    row = _first_row(result)
    assert row["voice_of_surface"] == "passive"
    assert row["base_past_passive"]
    assert row["tense_of_surface"] == "past"


def test_q13_quranic_ya3lamu_present_active():
    """يَعْلَمُ (2:77) — present active with mocked resolved bab."""
    result = build_verb_transformation(_mock_lo(
        "يَعْلَمُ",
        root="ع-ل-م",
        bab="فَعَلَ-يَفْعِلُ",
        past_pattern="فَعَلَ",
        present_pattern="يَفْعِلُ",
        present_passive_pattern="يُفْعَلُ",
    ))
    row = _first_row(result)
    assert row["tense_of_surface"] == "present"
    assert row["voice_of_surface"] == "active"
    assert row["base_present_active"]


def test_q14_quranic_ihdina_imperative_form_iv():
    """اهْدِنَا (1:6) — Form IV أَفْعَلَ; imperative template أَفْعِلْ → أَهْدِ (surface is longer; base imperative still derivable)."""
    result = build_verb_transformation(_mock_lo(
        "اهْدِنَا",
        root="ه-د-ي",
        bab="أَفْعَلَ",
        past_pattern="أَفْعَلَ",
        present_pattern="يُفْعِلُ",
        present_passive_pattern="يُفْعَلُ",
    ))
    row = _first_row(result)
    assert row["imperative"]
    assert row.get("bab") == "أَفْعَلَ"
    assert row.get("masdar_wazn") == "إِفْعَال"
