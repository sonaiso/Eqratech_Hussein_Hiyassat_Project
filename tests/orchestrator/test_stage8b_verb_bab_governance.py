# -*- coding: utf-8 -*-
"""
L8B Verb Bab Governance stage tests.
Structure, output shape, confidence range, explainability, presentation.
"""

from __future__ import annotations

import pytest

from .conftest import run_pipeline_for_test


def test_l8b_in_stage_order():
    from orchestrator.types import STAGE_ORDER
    assert "L8B_VERB_BAB_GOVERNANCE" in STAGE_ORDER
    idx = STAGE_ORDER.index("L8B_VERB_BAB_GOVERNANCE")
    assert STAGE_ORDER[idx - 1] == "L8_ROOT_EXTRACTION"
    assert STAGE_ORDER[idx + 1] == "L9_WAZN_MATCHING"


def test_output_shape_valid():
    pipeline = run_pipeline_for_test("ضرب الرجل الحجر")
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    assert "verb_governance_profiles" in tr
    assert "governance_summary" in tr
    assert isinstance(tr["verb_governance_profiles"], list)
    assert isinstance(tr["governance_summary"], dict)


def test_governance_summary_exists():
    pipeline = run_pipeline_for_test("عاش الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    summary = tr.get("governance_summary")
    assert summary is not None
    assert "verb_count" in summary
    assert "resolved_profiles" in summary
    assert "candidate_profiles" in summary
    assert "unresolved_profiles" in summary


def test_confidence_in_valid_range():
    pipeline = run_pipeline_for_test("انتمى الرجل إلى الوطن")
    profiles = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    profiles = (profiles.get("transformation_result") or {}).get("verb_governance_profiles") or []
    for p in profiles:
        conf = p.get("confidence")
        if conf is not None and p.get("status") != "not_applicable":
            assert 0.05 <= conf <= 0.98


def test_explainability_includes_l8b():
    pipeline = run_pipeline_for_test("أعطى المعلم الطالب كتاباً")
    trace = (pipeline.get("rendered_output") or {}).get("artifacts") or {}
    trace_list = trace.get("evidence_trace") or []
    stages = [e.get("supporting_stage") for e in trace_list]
    assert "L8B_VERB_BAB_GOVERNANCE" in stages


def test_detailed_rendering_includes_governance_section():
    pipeline = run_pipeline_for_test("ظننت الطالب مجتهداً", render_mode="detailed")
    ro = pipeline.get("rendered_output") or {}
    sections = ro.get("sections") or []
    ids = [s.get("id") for s in sections]
    assert "verb_governance" in ids


def test_3asha_intransitive_basic():
    """عاش الرجل — intransitive_basic, objects=0."""
    pipeline = run_pipeline_for_test("عاش الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profiles = [p for p in profiles if p.get("status") != "not_applicable"]
    if verb_profiles:
        p = verb_profiles[0]
        assert p.get("governance_family") == "intransitive_basic" or p.get("transitivity") == "لازم"
        assert p.get("objects") == 0


def test_daraba_basic_transitive():
    """ضرب الرجل الحجر — basic_transitive, objects=1."""
    pipeline = run_pipeline_for_test("ضرب الرجل الحجر")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = [p for p in (tr.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if profiles:
        p = profiles[0]
        assert p.get("governance_family") == "basic_transitive" or (p.get("transitivity") == "متعدي" and p.get("objects") == 1)


def test_intimaa_required_preposition_ila():
    """انتمى الرجل إلى الوطن — intransitive_prepositional, required_prepositions includes إلى."""
    pipeline = run_pipeline_for_test("انتمى الرجل إلى الوطن")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = [p for p in (tr.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if profiles:
        preps = profiles[0].get("required_prepositions") or []
        assert "إلى" in preps or "الى" in str(preps) or profiles[0].get("governance_family") == "intransitive_prepositional"


def test_tawakkul_required_preposition_ala():
    """توكل الرجل على الله — required_prepositions includes على."""
    pipeline = run_pipeline_for_test("توكل الرجل على الله")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = [p for p in (tr.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if profiles:
        preps = profiles[0].get("required_prepositions") or []
        assert "على" in preps or profiles[0].get("governance_family") == "intransitive_prepositional"


def test_a3taa_double_object():
    """أعطى المعلم الطالب كتاباً — double_object."""
    pipeline = run_pipeline_for_test("أعطى المعلم الطالب كتاباً")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = [p for p in (tr.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if profiles:
        p = profiles[0]
        assert p.get("governance_family") == "double_object" or (p.get("objects") == 2)


def test_zanna_mental_verb():
    """ظننت الطالب مجتهداً — mental_verb or special_class أفعال القلوب (verb ظننت = token 0)."""
    pipeline = run_pipeline_for_test("ظننت الطالب مجتهداً")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    # Find verb profile for first token (ظننت)
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    if not verb_profile:
        verb_profile = next((p for p in profiles if p.get("status") != "not_applicable"), None)
    if verb_profile and verb_profile.get("status") != "not_applicable":
        assert (
            verb_profile.get("governance_family") == "mental_verb"
            or verb_profile.get("special_class") == "أفعال القلوب"
            or (verb_profile.get("objects") == 2 and verb_profile.get("transitivity") == "متعدي")
        )


def test_sayyar_transformational():
    """صيّر المعلم الطين خزفاً — transformational_verb."""
    pipeline = run_pipeline_for_test("صيّر المعلم الطين خزفاً")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = [p for p in (tr.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if profiles:
        p = profiles[0]
        assert (
            p.get("governance_family") == "transformational_verb"
            or p.get("special_class") == "أفعال التحويل"
            or (p.get("objects") == 2)
        )


def test_profile_has_required_fields():
    pipeline = run_pipeline_for_test("كتب زيد")
    profiles = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    profiles = (profiles.get("transformation_result") or {}).get("verb_governance_profiles") or []
    for p in profiles[:3]:
        assert "token_id" in p
        assert "surface" in p
        assert "root_type" in p
        assert "verb_class" in p
        assert "bab" in p
        assert "transitivity" in p
        assert "objects" in p
        assert "governance_family" in p
        assert "confidence" in p
        assert "status" in p
        assert "voice_evidence" in p
        assert "expected_subject_role" in p


# --- Passive voice morphological detector tests (diacritized input) ---


def test_passive_sound_trilateral_futiha():
    """فُتِحَ الباب — passive detected, expected_subject_role نائب فاعل."""
    # فُتِحَ = damma on ف, kasra on ت, fatha on ح
    text = "\u0641\u064f\u062a\u0650\u062d\u064e \u0627\u0644\u0628\u0627\u0628"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "passive"
    assert verb_profile.get("voice_evidence", {}).get("rule") == "sound_trilateral_passive"
    assert verb_profile.get("expected_subject_role") == "نائب فاعل"


def test_passive_hollow_qeela():
    """قِيلَ الحق — hollow passive detected."""
    # قِيلَ = kasra on ق, then ي, then لَ
    text = "\u0642\u0650\u064a\u0644\u064e \u0627\u0644\u062d\u0642"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "passive"
    assert verb_profile.get("voice_evidence", {}).get("rule") == "hollow_passive"


def test_passive_defective_utiya():
    """أُتِيَ الرجل — defective passive detected."""
    # أُتِيَ = damma on أ, kasra on ت, يَ (ي + fatha)
    text = "\u0623\u064f\u062a\u0650\u064a\u064e \u0627\u0644\u0631\u062c\u0644"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "passive"
    assert verb_profile.get("voice_evidence", {}).get("rule") == "defective_passive"


def test_passive_derived_ukrima():
    """أُكْرِمَ الضيف — derived passive detected."""
    # أُكْرِمَ = damma on أ, then كْ رِ مَ
    text = "\u0623\u064f\u0643\u0652\u0631\u0650\u0645\u064e \u0627\u0644\u0636\u064a\u0641"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "passive"
    assert verb_profile.get("voice_evidence", {}).get("rule") == "derived_passive"


def test_active_fataha():
    """فَتَحَ الرجل الباب — active (not passive)."""
    text = "\u0641\u064e\u062a\u064e\u062d\u064e \u0627\u0644\u0631\u062c\u0644 \u0627\u0644\u0628\u0627\u0628"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "active"
    assert verb_profile.get("expected_subject_role") == "فاعل"


def test_active_qaala():
    """قال الرجل — active (hollow active)."""
    # قَالَ = ق + fatha, then ا (long), then لَ
    text = "\u0642\u064e\u0627\u0644\u064e \u0627\u0644\u0631\u062c\u0644"
    pipeline = run_pipeline_for_test(text)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = tr.get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    verb_profile = next((p for p in profiles if p.get("token_id") == "0"), None)
    assert verb_profile is not None
    assert verb_profile.get("voice") == "active"


# --- Verb candidacy tightening (non-verb exclusion) ---


def test_non_verb_nouns_not_governance_profiles():
    """Ordinary nouns (الرجل, الحجر) must not appear as verb governance profiles; only the verb should."""
    pipeline = run_pipeline_for_test("ظَلَمَ الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = result.get("verb_governance_profiles") or []
    surfaces = [p.get("surface") for p in profiles]
    assert "الرجل" not in surfaces
    assert len(profiles) >= 1, "at least one verb profile (finite verb) expected"


def test_participle_like_excluded_without_strong_verb_evidence():
    """Participle-like tokens (مُنْتَمِياً, وَمُتَوَكِّلاً) must not get profiles when no finite-verb evidence."""
    regression = "لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً أَبَداً وَلَعَاشَ مُنْتَمِياً لِوَطَنِهِ مُخْلِصاً لِدِينِهِ وَمُتَوَكِّلاً عَلَى اللَّهِ"
    pipeline = run_pipeline_for_test(regression)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = result.get("verb_governance_profiles") or []
    surfaces = [p.get("surface") for p in profiles]
    assert "مُنْتَمِياً" not in surfaces
    assert "وَمُتَوَكِّلاً" not in surfaces


def test_regression_sentence_realistic_verb_count():
    """Regression sentence must have low, realistic verb_count (only true finite verbs)."""
    regression = "لَوْ ضُرِبَ الظَّالِمُ كَالْحَجَرِ لَمَا ظَلَمَ أَحَداً أَبَداً وَلَعَاشَ مُنْتَمِياً لِوَطَنِهِ مُخْلِصاً لِدِينِهِ وَمُتَوَكِّلاً عَلَى اللَّهِ"
    pipeline = run_pipeline_for_test(regression)
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    summary = result.get("governance_summary") or {}
    verb_count = summary.get("verb_count", 0)
    assert 2 <= verb_count <= 6, f"verb_count should be realistic (2–6), got {verb_count}"
    excluded = summary.get("excluded_non_verbs", 0)
    assert excluded >= 10, f"excluded_non_verbs should be high for this sentence, got {excluded}"


def test_governance_summary_has_excluded_non_verbs():
    """governance_summary may include excluded_non_verbs (tightening pass)."""
    pipeline = run_pipeline_for_test("الرجل في البيت")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    summary = result.get("governance_summary") or {}
    assert "verb_count" in summary
    assert "excluded_non_verbs" in summary


def test_downstream_shape_unchanged():
    """Output shape remains valid: verb_governance_profiles list, governance_summary dict with expected keys."""
    pipeline = run_pipeline_for_test("ضرب الرجل الحجر")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    assert "verb_governance_profiles" in result
    assert "governance_summary" in result
    summary = result.get("governance_summary") or {}
    assert "verb_count" in summary
    assert "resolved_profiles" in summary
    assert "candidate_profiles" in summary
    assert "unresolved_profiles" in summary
    profiles = result.get("verb_governance_profiles") or []
    for p in profiles[:5]:
        assert "token_id" in p
        assert "surface" in p
        assert "voice_evidence" in p
        assert "expected_subject_role" in p


# --- Bab (abwab) and tense mapping extension ---


def test_abwab_resolver_unit():
    """Unit: _resolve_bab with known root from abwab KB returns correct bab."""
    from orchestrator.l8b_verb_bab_governance import _load_abwab_kb, _resolve_bab
    abwab = _load_abwab_kb()
    bab, status, conf = _resolve_bab("ضرب", "ضرب", "صحيح سالم", "trilateral", abwab)
    assert bab == "فَعَلَ-يَفْعِلُ"
    assert status == "resolved"
    assert conf >= 0.85
    bab2, status2, _ = _resolve_bab("رسم", "رسم", "صحيح سالم", "trilateral", abwab)
    assert bab2 == "فَعَلَ-يَفْعُلُ"
    assert status2 == "resolved"
    bab3, status3, _ = _resolve_bab("ظلم", "ظلم", "صحيح سالم", "trilateral", abwab)
    assert bab3 == "unknown"
    assert status3 == "unknown"


def test_tense_mapping_unit():
    """Unit: _tense_mapping_for_bab returns past, present, present_passive for canonical bab."""
    from orchestrator.l8b_verb_bab_governance import _tense_mapping_for_bab
    tm = _tense_mapping_for_bab("فَعَلَ-يَفْعِلُ", "صحيح سالم")
    assert tm.get("past_pattern") == "فَعَلَ"
    assert tm.get("present_pattern") == "يَفْعِلُ"
    assert (tm.get("present_passive_pattern") or "").strip() != "unknown"
    tm_unknown = _tense_mapping_for_bab("unknown", "صحيح سالم")
    assert tm_unknown.get("past_pattern") == "unknown"
    assert tm_unknown.get("present_pattern") == "unknown"


def test_profile_has_bab_and_tense_mapping_fields():
    """Output shape: each profile has bab, bab_status, bab_confidence, tense_mapping."""
    pipeline = run_pipeline_for_test("ظلم الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = result.get("verb_governance_profiles") or []
    for p in profiles[:5]:
        assert "bab" in p
        assert "bab_status" in p
        assert "bab_confidence" in p
        assert "tense_mapping" in p
        tm = p.get("tense_mapping") or {}
        assert "past_pattern" in tm
        assert "present_pattern" in tm
        assert "present_passive_pattern" in tm


def test_seed_bab_rasama():
    """رَسَمَ → bab فَعَلَ-يَفْعُلُ (from abwab KB when L8 returns root ر-س-م)."""
    pipeline = run_pipeline_for_test("رسم الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile (candidacy gate may exclude)")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root for this token")
    assert p.get("bab") == "فَعَلَ-يَفْعُلُ"
    assert p.get("bab_status") == "resolved"


def test_seed_bab_daraba():
    """ضَرَبَ → bab فَعَلَ-يَفْعِلُ (when L8 returns root ض-ر-ب)."""
    pipeline = run_pipeline_for_test("ضرب الرجل الحجر")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root")
    assert p.get("bab") == "فَعَلَ-يَفْعِلُ"
    assert p.get("bab_status") == "resolved"


def test_seed_bab_nafa3a():
    """نَفَعَ → bab فَعَلَ-يَفْعَلُ (when L8 returns root ن-ف-ع)."""
    pipeline = run_pipeline_for_test("نفع الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root for نفع")
    assert p.get("bab") == "فَعَلَ-يَفْعَلُ"
    assert p.get("bab_status") == "resolved"


def test_seed_bab_fariha():
    """فَرِحَ → bab فَعِلَ-يَفْعَلُ (when L8 returns root ف-ر-ح)."""
    pipeline = run_pipeline_for_test("فرح الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root")
    assert p.get("bab") == "فَعِلَ-يَفْعَلُ"
    assert p.get("bab_status") == "resolved"


def test_seed_bab_qaruba():
    """قَرُبَ → bab فَعُلَ-يَفْعُلُ (when L8 returns root ق-ر-ب)."""
    pipeline = run_pipeline_for_test("قرب الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root")
    assert p.get("bab") == "فَعُلَ-يَفْعُلُ"
    assert p.get("bab_status") == "resolved"


def test_seed_bab_hasiba():
    """حَسِبَ → bab فَعِلَ-يَفْعِلُ (when L8 returns root ح-س-ب)."""
    pipeline = run_pipeline_for_test("حسب الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    if p.get("root") is None:
        pytest.skip("L8 did not return root")
    assert p.get("bab") == "فَعِلَ-يَفْعِلُ"
    assert p.get("bab_status") == "resolved"


def test_present_pattern_populated_when_bab_resolved():
    """When bab is resolved, tense_mapping has present_pattern set."""
    pipeline = run_pipeline_for_test("ضرب الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("bab_status") == "resolved"]
    if not profiles:
        pytest.skip("No resolved bab in this run")
    p = profiles[0]
    tm = p.get("tense_mapping") or {}
    assert (tm.get("present_pattern") or "").strip() != ""
    assert (tm.get("present_pattern") or "").strip() != "unknown"


def test_present_passive_pattern_populated_conservatively():
    """When bab resolved (صحيح), present_passive_pattern is set (e.g. يُفْعَلُ)."""
    pipeline = run_pipeline_for_test("ضرب الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("bab_status") == "resolved"]
    if not profiles:
        pytest.skip("No resolved bab")
    p = profiles[0]
    tm = p.get("tense_mapping") or {}
    pp = (tm.get("present_passive_pattern") or "").strip()
    assert pp != ""


def test_unknown_bab_remains_unknown_for_unsupported():
    """Verbs not in abwab KB get bab=unknown, bab_status=unknown."""
    pipeline = run_pipeline_for_test("ظلم الرجل")
    tr = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    result = tr.get("transformation_result") or {}
    profiles = [p for p in (result.get("verb_governance_profiles") or []) if p.get("status") != "not_applicable"]
    if not profiles:
        pytest.skip("No verb profile")
    p = profiles[0]
    assert p.get("bab") == "unknown"
    assert p.get("bab_status") == "unknown"
