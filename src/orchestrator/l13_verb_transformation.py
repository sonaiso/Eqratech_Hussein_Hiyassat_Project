# -*- coding: utf-8 -*-
"""
L13_VERB_TRANSFORMATION — Verb transformation engine (Pass 1).

Deterministic, rule-based generation from L8/L8B/L14:
- past active
- present active
- past passive
- present passive
- masdar
- imperative

No linguistic logic is pushed into analyzer/presentation layers.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from .builders import build_layer_output, get_previous_output
from .l14_jamid_mushtaq import has_strong_true_verb_evidence
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict

_WEAK_ROOT_TYPES = frozenset({
    "معتل مثال",
    "معتل أجوف",
    "معتل ناقص",
    "معتل لفيف مقرون",
    "معتل لفيف مفروق",
})

_QUADRILATERAL_ROOT_TYPES = frozenset({"quadrilateral_candidate"})

_MASDAR_WAZN_BY_BAB: Dict[str, str] = {
    "فَعَلَ-يَفْعُلُ": "فَعْل",
    "فَعَلَ-يَفْعِلُ": "فَعْل",
    "فَعِلَ-يَفْعَلُ": "فَعَل",
    "فَعُلَ-يَفْعُلُ": "فُعُول",
    "فَعَّلَ": "تَفْعِيل",
    "أَفْعَلَ": "إِفْعَال",
    "تَفَعَّلَ": "تَفَعُّل",
    "انْفَعَلَ": "انْفِعَال",
    "افْتَعَلَ": "افْتِعَال",
    "اسْتَفْعَلَ": "اسْتِفْعَال",
}

_IMPERATIVE_TEMPLATE_BY_BAB: Dict[str, Optional[str]] = {
    "فَعَلَ-يَفْعُلُ": "اُفْعُلْ",
    "فَعَلَ-يَفْعِلُ": "اِفْعِلْ",
    "فَعِلَ-يَفْعَلُ": "اِفْعَلْ",
    "فَعُلَ-يَفْعُلُ": None,
    "فَعَّلَ": "فَعِّلْ",
    "أَفْعَلَ": "أَفْعِلْ",
    "تَفَعَّلَ": "تَفَعَّلْ",
    "انْفَعَلَ": "انْفَعِلْ",
    "افْتَعَلَ": "افْتَعِلْ",
    "اسْتَفْعَلَ": "اسْتَفْعِلْ",
}


def _normalize_text(text: str) -> str:
    if not text or not isinstance(text, str):
        return ""
    stripped = (text or "").strip().replace("\u0651", "")
    return "".join(
        ch for ch in stripped
        if not (0x064B <= ord(ch) <= 0x0652 or ord(ch) == 0x0670)
    ).strip()


def _parse_root_letters(root: Optional[str]) -> List[str]:
    if not root or not isinstance(root, str):
        return []
    cleaned = (root or "").strip().replace("-", "").replace(" ", "")
    return [ch for ch in cleaned if ch]


def apply_root_to_wazn(root_str: Optional[str], wazn: Optional[str]) -> Optional[str]:
    """Apply triliteral root letters to ف/ع/ل placeholders conservatively."""
    letters = _parse_root_letters(root_str)
    if len(letters) != 3 or not wazn or not isinstance(wazn, str):
        return None
    out = []
    for ch in wazn:
        if ch == "ف":
            out.append(letters[0])
        elif ch == "ع":
            out.append(letters[1])
        elif ch == "ل":
            out.append(letters[2])
        else:
            out.append(ch)
    return "".join(out)


def _get_tokens(lo: Dict[str, Any]) -> List[str]:
    l2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    return [(t.get("word") or "").strip() for t in (l2.get("tokens") or []) if isinstance(t, dict)]


def _root_by_index(lo: Dict[str, Any], idx: int) -> Optional[str]:
    l8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    words = l8.get("words") or []
    if 0 <= idx < len(words) and isinstance(words[idx], dict):
        return words[idx].get("root")
    return None


def _l14_entry_by_index(lo: Dict[str, Any], idx: int) -> Dict[str, Any]:
    l14 = (lo.get("L14_JAMID_MUSHTAQ") or {}).get("transformation_result") or {}
    rows = l14.get("token_classifications") or []
    if 0 <= idx < len(rows) and isinstance(rows[idx], dict):
        return rows[idx]
    return {}


def _l8b_profile_by_index(lo: Dict[str, Any], idx: int) -> Dict[str, Any]:
    l8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = l8b.get("verb_governance_profiles") or []
    for profile in profiles:
        if not isinstance(profile, dict):
            continue
        if str(profile.get("token_id")) == str(idx):
            return profile
    return {}


def _is_confirmed_verb(lo: Dict[str, Any], idx: int, surface: str) -> bool:
    l14_entry = _l14_entry_by_index(lo, idx)
    if (l14_entry.get("derivational_class") or "").strip() == "VERB":
        return True
    return has_strong_true_verb_evidence(str(idx), surface, lo)


def _derive_past_passive(
    root: Optional[str],
    root_type: Optional[str],
    present_passive_pattern: Optional[str],
    limitations: List[str],
) -> Optional[str]:
    if not root:
        return None
    if root_type == "صحيح سالم":
        return apply_root_to_wazn(root, "فُعِلَ")
    if present_passive_pattern and present_passive_pattern not in ("", "unknown", "derived", "يُسْتَعْمَلُ"):
        if present_passive_pattern.startswith("يُ"):
            inferred = "فُعِلَ"
            applied = apply_root_to_wazn(root, inferred)
            if applied:
                limitations.append("passive_past_inferred_from_present_passive")
                return applied
    limitations.append("passive_past_not_derivable")
    return None


def _derive_masdar(root: Optional[str], bab: Optional[str], bab_status: str, limitations: List[str]) -> Tuple[Optional[str], Optional[str]]:
    if not root:
        return None, None
    if not bab or bab in ("", "unknown"):
        limitations.append("masdar_not_derivable_unknown_bab")
        return None, None
    wazn = _MASDAR_WAZN_BY_BAB.get(bab)
    if not wazn:
        limitations.append("masdar_not_mapped_for_bab")
        return None, None
    masdar = apply_root_to_wazn(root, wazn)
    if not masdar:
        limitations.append("masdar_template_only")
        return wazn, wazn
    if bab_status != "resolved":
        limitations.append("masdar_from_nonresolved_bab")
    return masdar, wazn


def _derive_imperative(root: Optional[str], bab: Optional[str], limitations: List[str]) -> Optional[str]:
    if not root:
        return None
    if not bab or bab in ("", "unknown"):
        limitations.append("imperative_not_derivable_unknown_bab")
        return None
    template = _IMPERATIVE_TEMPLATE_BY_BAB.get(bab)
    if template is None:
        if bab in _IMPERATIVE_TEMPLATE_BY_BAB:
            limitations.append("imperative_not_supported_for_bab")
        else:
            limitations.append("imperative_not_mapped_for_bab")
        return None
    imperative = apply_root_to_wazn(root, template)
    if imperative:
        return imperative
    limitations.append("imperative_template_only")
    return template


def _detect_surface_tense_and_voice(
    surface: str,
    profile: Dict[str, Any],
    base_past_active: Optional[str],
    base_present_active: Optional[str],
    base_past_passive: Optional[str],
    base_present_passive: Optional[str],
) -> Tuple[str, str]:
    surface_raw = (surface or "").strip()
    if surface_raw:
        if surface_raw == (base_past_active or "").strip():
            return "past", "active"
        if surface_raw == (base_present_active or "").strip():
            return "present", "active"
        if surface_raw == (base_past_passive or "").strip():
            return "past", "passive"
        if surface_raw == (base_present_passive or "").strip():
            return "present", "passive"
    surface_norm = _normalize_text(surface)
    voice = (profile.get("voice") or "").strip().lower()
    if voice in ("active", "passive"):
        if surface_norm.startswith(("ي", "ت", "أ", "ن")):
            return "present", voice
        return "past", voice
    return "unknown", "unknown"


def _compute_transformation_confidence(
    *,
    root: Optional[str],
    bab_status: str,
    root_type: Optional[str],
    populated_fields: int,
) -> float:
    if not root:
        return 0.0
    if bab_status != "resolved":
        base = 0.4 if populated_fields > 0 else 0.0
    else:
        base = 0.9 if populated_fields >= 5 else 0.85 if populated_fields >= 3 else 0.75
    if root_type in _WEAK_ROOT_TYPES:
        base -= 0.1
    return round(max(0.0, min(0.95, base)), 2)


def _transform_one(idx: int, surface: str, lo: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if not _is_confirmed_verb(lo, idx, surface):
        return None

    profile = _l8b_profile_by_index(lo, idx)
    root = _root_by_index(lo, idx) or profile.get("root")
    root_type = profile.get("root_type")
    bab = profile.get("bab")
    bab_status = (profile.get("bab_status") or "unknown").strip()
    tense_mapping = profile.get("tense_mapping") or {}
    limitations: List[str] = []

    if not root:
        return {
            "token_id": str(idx),
            "surface": surface,
            "root": None,
            "root_type": root_type,
            "bab": bab,
            "bab_status": bab_status,
            "base_past_active": None,
            "base_present_active": None,
            "base_past_passive": None,
            "base_present_passive": None,
            "masdar": None,
            "masdar_wazn": None,
            "imperative": None,
            "tense_of_surface": "unknown",
            "voice_of_surface": "unknown",
            "transformation_confidence": 0.0,
            "transformation_rule": "no_root_available",
            "limitations": ["no_root_available"],
        }

    if root_type in _QUADRILATERAL_ROOT_TYPES or len(_parse_root_letters(root)) > 3:
        return {
            "token_id": str(idx),
            "surface": surface,
            "root": root,
            "root_type": root_type,
            "bab": bab,
            "bab_status": bab_status,
            "base_past_active": None,
            "base_present_active": None,
            "base_past_passive": None,
            "base_present_passive": None,
            "masdar": None,
            "masdar_wazn": None,
            "imperative": None,
            "tense_of_surface": "unknown",
            "voice_of_surface": "unknown",
            "transformation_confidence": 0.0,
            "transformation_rule": "quadrilateral_not_supported",
            "limitations": ["quadrilateral_transformation_not_supported"],
        }

    past_pattern = tense_mapping.get("past_pattern")
    present_pattern = tense_mapping.get("present_pattern")
    present_passive_pattern = tense_mapping.get("present_passive_pattern")

    base_past_active = None
    if past_pattern and past_pattern not in ("", "unknown", "derived"):
        base_past_active = apply_root_to_wazn(root, past_pattern) or past_pattern
    else:
        limitations.append("past_active_not_derivable")

    base_present_active = None
    if present_pattern and present_pattern not in ("", "unknown"):
        base_present_active = apply_root_to_wazn(root, present_pattern) or present_pattern
    else:
        limitations.append("present_active_not_derivable")

    base_present_passive = None
    if present_passive_pattern and present_passive_pattern not in ("", "unknown", "derived", "يُسْتَعْمَلُ"):
        base_present_passive = apply_root_to_wazn(root, present_passive_pattern) or present_passive_pattern
    else:
        limitations.append("present_passive_not_derivable")

    base_past_passive = _derive_past_passive(root, root_type, present_passive_pattern, limitations)
    masdar, masdar_wazn = _derive_masdar(root, bab, bab_status, limitations)
    imperative = _derive_imperative(root, bab, limitations)

    if root_type in _WEAK_ROOT_TYPES:
        limitations.append("weak_root_transformation_approximate")

    tense_of_surface, voice_of_surface = _detect_surface_tense_and_voice(
        surface,
        profile,
        base_past_active,
        base_present_active,
        base_past_passive,
        base_present_passive,
    )

    populated_fields = sum(
        1 for value in (
            base_past_active,
            base_present_active,
            base_past_passive,
            base_present_passive,
            masdar,
            imperative,
        ) if value is not None
    )
    confidence = _compute_transformation_confidence(
        root=root,
        bab_status=bab_status,
        root_type=root_type,
        populated_fields=populated_fields,
    )

    rule = "tense_mapping_bab_pass1"
    if bab_status != "resolved":
        rule = "partial_nonresolved_bab_pass1"
    if root_type in _WEAK_ROOT_TYPES:
        rule += "_weak_root"

    return {
        "token_id": str(idx),
        "surface": surface,
        "root": root,
        "root_type": root_type,
        "bab": bab,
        "bab_status": bab_status,
        "base_past_active": base_past_active,
        "base_present_active": base_present_active,
        "base_past_passive": base_past_passive,
        "base_present_passive": base_present_passive,
        "masdar": masdar,
        "masdar_wazn": masdar_wazn,
        "imperative": imperative,
        "tense_of_surface": tense_of_surface,
        "voice_of_surface": voice_of_surface,
        "transformation_confidence": confidence,
        "transformation_rule": rule,
        "limitations": sorted(set(limitations)),
    }


def build_verb_transformation(lo: Dict[str, Any]) -> Dict[str, Any]:
    tokens = _get_tokens(lo)
    verb_transformations: List[Dict[str, Any]] = []
    for idx, surface in enumerate(tokens):
        entry = _transform_one(idx, surface, lo)
        if entry is not None:
            verb_transformations.append(entry)

    fully_transformed = 0
    partially_transformed = 0
    untransformed = 0
    for entry in verb_transformations:
        filled = sum(
            1 for key in (
                "base_past_active",
                "base_present_active",
                "base_past_passive",
                "base_present_passive",
                "masdar",
                "imperative",
            ) if entry.get(key) is not None
        )
        if filled == 6:
            fully_transformed += 1
        elif filled == 0:
            untransformed += 1
        else:
            partially_transformed += 1

    return {
        "status": "success",
        "verb_transformations": verb_transformations,
        "transformation_summary": {
            "total_verbs": len(verb_transformations),
            "fully_transformed": fully_transformed,
            "partially_transformed": partially_transformed,
            "untransformed": untransformed,
        },
        "coverage": "verb_transformation_pass1",
    }


class RealL13VerbTransformation(BaseStage):
    """L13_VERB_TRANSFORMATION: derive base verb paradigm from L8B/L14 evidence."""

    def __init__(self) -> None:
        super().__init__(
            "L13_VERB_TRANSFORMATION",
            STAGE_NAMES["L13_VERB_TRANSFORMATION"],
            12,
        )

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        lo = pipeline.get("layer_outputs") or {}
        received = get_previous_output(pipeline, self.stage_index) or {}
        result = build_verb_transformation(lo)
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            "success",
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={
                "file": "orchestrator/l13_verb_transformation.py",
                "symbol": "RealL13VerbTransformation",
                "mode": "direct",
            },
        )
