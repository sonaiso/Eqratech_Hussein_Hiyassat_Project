# -*- coding: utf-8 -*-
"""
Real stage adapters — wrap existing FVAFK/engines output into canonical LayerOutput.

Each stage reads pipeline["_fvafk_result"] (set by run_fvafk_once) and maps to
transformation_result; preserves raw output in raw_module_output.
L11 i3rab is explicitly wired to c2b.c2e.i3rab_text.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from ..adapters.fvafk_runner import FVAFK_RESULT_KEY
from ..builders import build_layer_output, get_previous_output
from ..gates import compute_gates, gate_entry
from ..l8b_verb_bab_governance import RealL8BVerbBabGovernance

def _enrich_l4_with_connectives(items: List[Dict[str, Any]]) -> None:
    """Optionally add connective_group from shared connectives layer (non-invasive)."""
    try:
        from ..connectives import classify_connective
        for item in items:
            w = item.get("word")
            if not w:
                continue
            c = classify_connective(w)
            if c:
                item["connective_group"] = c.get("group")
                item["connective_hint"] = c.get("category_name") or c.get("group")
    except Exception:
        pass
from ..l10b_deep_syntax import RealL10BDeepSyntax
from ..l11b_causal_i3rab import RealL11BCausalI3rab
from ..l13_verb_transformation import RealL13VerbTransformation
from ..l12_gender_number import RealL12GenderNumber
from ..l14_jamid_mushtaq import RealL14JamidMushtaq
from ..l17_rule_based_i3rab import RealL17RuleBasedI3rab
from ..types import LayerOutputDict, PipelineDict, STAGE_ORDER
from .base_stage import BaseStage
from .placeholders import STAGE_NAMES


def _get_fvafk(pipeline: PipelineDict) -> Optional[Dict[str, Any]]:
    """Return the FVAFK result dict if present and successful."""
    data = pipeline.get(FVAFK_RESULT_KEY)
    if not isinstance(data, dict) or not data.get("success", True):
        return None
    return data


class RealL1Normalization(BaseStage):
    """L1: Normalization — OrthographyAdapter or from prior; fallback placeholder."""

    def __init__(self) -> None:
        super().__init__("L1_NORMALIZATION", STAGE_NAMES["L1_NORMALIZATION"], 1)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        text = pipeline.get("original_text", "") or get_previous_output(pipeline, 1).get("text", "")
        received = {"text": text}
        warnings: List[str] = []
        errors: List[str] = []
        try:
            from fvafk.orthography_adapter import OrthographyAdapter
            adapter = OrthographyAdapter()
            normalized = adapter.normalize(text, strip_diacritics=False)
            result = {"normalized_text": normalized, "original_length": len(text), "normalized_length": len(normalized)}
            status = "success"
            next_input = {"text": normalized}
            reused = {"file": "fvafk/orthography_adapter.py", "symbol": "OrthographyAdapter.normalize", "mode": "adapter"}
        except Exception as e:
            result = {"placeholder": True}
            status = "partial"
            next_input = {"text": text}
            errors.append(str(e))
            reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=result,
            next_input=next_input, warnings=warnings if warnings else None,
            errors=errors if errors else None, reused_module=reused,
        )


class RealL2Tokenization(BaseStage):
    """L2: Tokenization — from c2b.words (word + span)."""

    def __init__(self) -> None:
        super().__init__("L2_TOKENIZATION", STAGE_NAMES["L2_TOKENIZATION"], 2)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 2) or {"text": pipeline.get("original_text", "")}
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words")
            if isinstance(words_list, list) and words_list:
                tokens = [{"word": w.get("word", ""), "span": w.get("span", {})} for w in words_list]
                result = {"tokens": tokens, "count": len(tokens)}
                status = "success"
                next_input = {"tokens": tokens}
                raw = {"tokens": tokens, "source": "c2b.words"}
                reused = {"file": "fvafk/cli.main", "symbol": "WordBoundaryDetector", "mode": "adapter"}
            else:
                result = {"tokens": [], "count": 0}; status = "partial"; next_input = received
                raw = fvafk.get("c2b", {}); reused = None
        else:
            result = {"tokens": [], "count": 0}; status = "partial" if fvafk else "missing"
            next_input = received; raw = fvafk or {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL3Segmentation(BaseStage):
    """L3: Segmentation — from c2b.words affixes (prefix, suffix, stripped)."""

    def __init__(self) -> None:
        super().__init__("L3_SEGMENTATION", STAGE_NAMES["L3_SEGMENTATION"], 3)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 3)
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words")
            if isinstance(words_list, list):
                segments = []
                for w in words_list:
                    aff = w.get("affixes") or {}
                    segments.append({
                        "word": w.get("word"),
                        "prefix": aff.get("prefix"), "suffix": aff.get("suffix"), "stripped": aff.get("stripped"),
                    })
                result = {"segments": segments, "count": len(segments)}
                status = "success" if segments else "partial"
                next_input = {"segments": segments}
                raw = {"segments": segments}
                reused = {"file": "fvafk/c2b/root_extractor", "symbol": "extract_with_affixes", "mode": "adapter"}
            else:
                result = {"segments": []}; status = "partial"; next_input = received; raw = {}
                reused = None
        else:
            result = {"segments": []}; status = "partial" if fvafk else "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL4Operators(BaseStage):
    """L4: Operators — from c2b.words (kind, operator)."""

    def __init__(self) -> None:
        super().__init__("L4_OPERATORS", STAGE_NAMES["L4_OPERATORS"], 4)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 4)
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            items = []
            for w in words_list:
                items.append({
                    "word": w.get("word"), "kind": w.get("kind"),
                    "operator": w.get("operator") if w.get("kind") == "operator" else None,
                })
            _enrich_l4_with_connectives(items)
            result = {"words": items, "operator_count": sum(1 for i in items if i.get("operator"))}
            status = "success"
            next_input = {"words": items}
            raw = result
            reused = {"file": "fvafk/c2b/operators_catalog", "symbol": "OperatorsCatalog", "mode": "adapter"}
        else:
            result = {"words": []}; status = "partial" if fvafk else "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL5WordTyping(BaseStage):
    """L5: Word typing — from c2b.words (kind)."""

    def __init__(self) -> None:
        super().__init__("L5_WORD_TYPING", STAGE_NAMES["L5_WORD_TYPING"], 5)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 5)
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            items = [{"word": w.get("word"), "kind": w.get("kind")} for w in words_list]
            result = {"words": items, "count": len(items)}
            status = "success"
            next_input = {"words": items}
            raw = result
            reused = {"file": "fvafk/c2b/word_classifier", "symbol": "WordClassifier", "mode": "adapter"}
        else:
            result = {"words": []}; status = "partial" if fvafk else "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL6Phonology(BaseStage):
    """L6: Phonology / CV — from c1, c2a, cv_analysis."""

    def __init__(self) -> None:
        super().__init__("L6_PHONOLOGY", STAGE_NAMES["L6_PHONOLOGY"], 6)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 6)
        if fvafk:
            c1 = fvafk.get("c1") or {}
            c2a = fvafk.get("c2a") or {}
            cv_analysis = c1.get("cv_analysis") or {}
            result = {
                "num_units": c1.get("num_units"),
                "cv_analysis": cv_analysis,
                "gates_count": len(c2a.get("gates") or []),
                "syllables_count": (c2a.get("syllables") or {}).get("count"),
            }
            status = "success" if (c1 or c2a) else "partial"
            next_input = {"c1": c1, "c2a": c2a, "cv_analysis": cv_analysis}
            raw = {"c1": c1, "c2a": c2a}
            reused = {"file": "fvafk/c1, fvafk/c2a", "symbol": "C1Encoder, GateOrchestrator, cv_pattern", "mode": "adapter"}
        else:
            result = {}; status = "missing"; next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL7Syllabification(BaseStage):
    """L7: Syllabification — from c2a.syllables."""

    def __init__(self) -> None:
        super().__init__("L7_SYLLABIFICATION", STAGE_NAMES["L7_SYLLABIFICATION"], 7)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 7)
        if fvafk:
            c2a = fvafk.get("c2a") or {}
            syll = c2a.get("syllables") or {}
            result = {"count": syll.get("count"), "syllables": syll.get("syllables")}
            status = "success" if result.get("count") is not None else "partial"
            next_input = result
            raw = syll
            reused = {"file": "fvafk/c2a, fvafk/cli", "symbol": "syllables", "mode": "adapter"}
        else:
            result = {}; status = "missing"; next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
        )


class RealL8RootExtraction(BaseStage):
    """L8: Root extraction — from c2b.words (root). Eligibility: has_morphology_candidate."""

    def __init__(self) -> None:
        super().__init__("L8_ROOT_EXTRACTION", STAGE_NAMES["L8_ROOT_EXTRACTION"], 8)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 8)
        gates = compute_gates(pipeline)
        gates_applied_list: List[Dict[str, Any]] = [
            gate_entry("has_tokens", gates["has_tokens"]),
            gate_entry("has_morphology_candidate", gates["has_morphology_candidate"]),
        ]
        if not gates["has_tokens"]:
            return build_layer_output(
                self.layer_id, self.layer_name, self.stage_index, "skipped",
                received_input=received, transformation_result={"words": [], "count": 0},
                raw_module_output={}, next_input=received or {},
                gates_applied=gates_applied_list,
                warnings=["No tokens; root extraction skipped."],
            )
        if not gates["has_morphology_candidate"]:
            return build_layer_output(
                self.layer_id, self.layer_name, self.stage_index, "skipped",
                received_input=received, transformation_result={"words": [], "count": 0},
                raw_module_output={}, next_input=received or {},
                gates_applied=gates_applied_list,
                warnings=["No morphology candidate (all operator/particle/pronoun); root extraction skipped."],
            )
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            items = []
            for w in words_list:
                r = w.get("root")
                root_str = r.get("formatted", "") if isinstance(r, dict) else (r or "")
                if not root_str and isinstance(r, dict) and r.get("letters"):
                    root_str = "-".join(r["letters"]) if isinstance(r["letters"], list) else str(r["letters"])
                items.append({"word": w.get("word"), "root": root_str or None})
            result = {"words": items, "count": len(items)}
            has_any_root = any(it.get("root") for it in items)
            status = "success" if has_any_root else "partial"
            next_input = {"words": items}
            raw = result
            reused = {"file": "fvafk/c2b/root_extractor, root_resolver", "symbol": "RootExtractor, RootResolver", "mode": "adapter"}
        else:
            result = {"words": []}; status = "partial" if fvafk else "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
            gates_applied=gates_applied_list,
        )


class RealL9WaznMatching(BaseStage):
    """L9: Wazn matching — from c2b.words (pattern.template, word_wazn). Eligibility: has_root_candidate."""

    def __init__(self) -> None:
        super().__init__("L9_WAZN_MATCHING", STAGE_NAMES["L9_WAZN_MATCHING"], 10)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 10)
        gates = compute_gates(pipeline)
        gates_applied_list: List[Dict[str, Any]] = [
            gate_entry("has_tokens", gates["has_tokens"]),
            gate_entry("has_root_candidate", gates["has_root_candidate"]),
        ]
        if not gates["has_root_candidate"]:
            return build_layer_output(
                self.layer_id, self.layer_name, self.stage_index, "skipped",
                received_input=received, transformation_result={"words": [], "count": 0},
                raw_module_output={}, next_input=received or {},
                gates_applied=gates_applied_list,
                warnings=["No root candidate; wazn matching skipped."],
            )
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            items = []
            for w in words_list:
                pat = w.get("pattern") or {}
                template = pat.get("template") if isinstance(pat, dict) else None
                wazn = w.get("word_wazn") or w.get("features", {}).get("word_wazn") or template
                items.append({"word": w.get("word"), "template": template, "word_wazn": wazn})
            result = {"words": items, "count": len(items)}
            has_any_wazn = any(it.get("template") or it.get("word_wazn") for it in items)
            status = "success" if has_any_wazn else "partial"
            next_input = {"words": items}
            raw = result
            reused = {"file": "fvafk/c2b/root_resolver/wazn_adapter", "symbol": "WaznAdapter", "mode": "adapter"}
        else:
            result = {"words": []}; status = "partial" if fvafk else "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
            gates_applied=gates_applied_list,
        )


class RealL10Syntax(BaseStage):
    """L10: Syntax — from syntax (word_forms, links.isnadi); may have error."""

    def __init__(self) -> None:
        super().__init__("L10_SYNTAX", STAGE_NAMES["L10_SYNTAX"], 14)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, self.stage_index)
        errors: List[str] = []
        if fvafk:
            syntax = fvafk.get("syntax") or {}
            err = syntax.get("error")
            if err:
                errors.append(err)
                status = "failed"
            else:
                status = "success"
            result = {
                "word_forms": syntax.get("word_forms", []),
                "links": syntax.get("links", {}),
                "error": err,
            }
            next_input = result
            raw = syntax
            reused = {"file": "fvafk/syntax/linkers", "symbol": "find_isnadi_links", "mode": "adapter"}
        else:
            result = {}; status = "missing"; next_input = received or {}; raw = {}
            reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
            errors=errors if errors else None,
        )


# Patch D: Indeclinable proper nouns (مبني allowed); others default معرب
_INDECLINABLE_PROPER_NOUNS = frozenset({"إبراهيم", "إسماعيل", "إسحاق", "يعقوب", "نوح", "لوط", "هود", "صالح", "يوسف"})

# L11 CRITICAL: Nominal-role substrings — verb tokens must NEVER receive these
_NOMINAL_ROLE_SUBSTRINGS = frozenset({
    "فاعل", "نائب فاعل", "مفعول به", "مفعول مطلق", "مفعول لأجله", "مفعول معه", "مفعول فيه",
    "مبتدأ", "خبر", "اسم مجرور", "مضاف إليه", "حال", "تمييز", "نعت", "بدل", "عطف بيان",
    "اسم", "علم", "معرب", "مبني",
})
# Verbal i3rab: verb-family text (فعل ماض، فعل مضارع، etc.)
_VERBAL_INDICATORS = ("فِعْل", "فعل", "فعل ماض", "فعل مضارع", "فعل أمر", "مَبْنِيٌّ لِلْمَجْهُولِ", "مَبْنِيٌّ عَلَى")


def _normalize_surface(s: str) -> str:
    """Normalize for comparison: strip, remove shadda and tashkeel so ضُرِبَ and ضرب match."""
    if not s or not isinstance(s, str):
        return ""
    out = (s or "").strip().replace("\u0651", "")
    return "".join(c for c in out if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)).strip()


def _strong_l8b_profile_for_token(token_id: str, pipeline: PipelineDict, surface: Optional[str] = None) -> Optional[Dict[str, Any]]:
    """Return a strong L8B verb profile only; weak candidate noun-like profiles must not become VERB."""
    lo = pipeline.get("layer_outputs") or {}
    tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles_list = tr8b.get("verb_governance_profiles") or []
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words5 = tr5.get("words") or []
    l5_kind = ""
    try:
        idx = int(token_id)
        if 0 <= idx < len(words5) and isinstance(words5[idx], dict):
            l5_kind = (words5[idx].get("kind") or "").strip().lower()
    except (ValueError, TypeError):
        idx = -1
    surf_norm = _normalize_surface(surface or "")
    for p in profiles_list:
        same_token = str(p.get("token_id")) == str(token_id)
        same_surface = bool(surf_norm) and _normalize_surface(p.get("surface") or "") == surf_norm
        if not same_token and not same_surface:
            continue
        status = (p.get("status") or "").strip().lower()
        confidence = float(p.get("confidence") or 0.0)
        voice = (p.get("voice") or "").strip().lower()
        transitivity = (p.get("transitivity") or "").strip().lower()
        objects = int(p.get("objects") or 0)
        if status == "not_applicable":
            continue
        if status == "resolved" or voice == "passive" or confidence >= 0.75 or objects > 0 or "متعد" in transitivity or "transitive" in transitivity:
            return p
        if l5_kind in ("verb", "فعل"):
            return p
    return None


def _stage15_relation_for_token(token_id: str, pipeline: PipelineDict) -> str:
    """Return strongest Stage 15 relation for token as dependent, if any."""
    lo = pipeline.get("layer_outputs") or {}
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    links = dsb.get("dependency_links") or []
    for rel in ("NAIB_SUBJ", "OBJ", "SUBJ", "PRED", "JAR_MAJRUR", "IDAFA", "SIFA", "APPOS"):
        for link in links:
            if str(link.get("dependent_id")) == str(token_id) and (link.get("relation") or "").strip() == rel:
                return rel
    return ""


def get_token_grammatical_family(token_id: str, pipeline: PipelineDict, surface: Optional[str] = None) -> str:
    """Return VERB | NOUN | PARTICLE | UNKNOWN. Precedence: strong L8B -> L5 -> Stage15/L10B -> fallback."""
    if _strong_l8b_profile_for_token(token_id, pipeline, surface=surface):
        return "VERB"
    lo = pipeline.get("layer_outputs") or {}
    if surface:
        surf_norm = _normalize_surface(surface)
        tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
        for w in (tr4.get("words") or []):
            if _normalize_surface(w.get("word") or "") == surf_norm and w.get("operator"):
                return "PARTICLE"
    try:
        idx = int(token_id)
    except (ValueError, TypeError):
        idx = -1
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words5 = tr5.get("words") or []
    if 0 <= idx < len(words5):
        w = words5[idx]
        if isinstance(w, dict):
            kind = (w.get("kind") or "").strip().lower()
            if kind in ("verb", "فعل"):
                return "VERB"
            if kind in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
                return "NOUN"
            if kind in ("particle", "حرف", "أداة"):
                return "PARTICLE"
    rel = _stage15_relation_for_token(token_id, pipeline)
    if rel in ("SUBJ", "OBJ", "NAIB_SUBJ", "PRED", "JAR_MAJRUR", "IDAFA", "SIFA", "APPOS"):
        return "NOUN"
    l10b = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
    for node in (l10b.get("dependency_nodes") or []):
        if str(node.get("token_id")) != str(token_id):
            continue
        pos_hint = (node.get("pos_hint") or "").strip().lower()
        if pos_hint in ("verb", "فعل"):
            return "VERB"
        if pos_hint in ("noun", "اسم", "name", "proper_noun", "proper noun", "علم"):
            return "NOUN"
    return "UNKNOWN"


def _i3rab_text_grammatical_family(i3rab_text: str) -> str:
    """Return VERBAL | NOMINAL | PARTICLE | UNKNOWN from i3rab text content."""
    if not i3rab_text or not isinstance(i3rab_text, str):
        return "UNKNOWN"
    t = (i3rab_text or "").strip()
    t_norm = _normalize_surface(t)
    for v in _VERBAL_INDICATORS:
        if v in t or (t_norm and v in t_norm):
            return "VERBAL"
    for sub in _NOMINAL_ROLE_SUBSTRINGS:
        if sub in t or (t_norm and sub in t_norm):
            return "NOMINAL"
    if "حرف" in t or "أداة" in t:
        return "PARTICLE"
    return "UNKNOWN"


def _contains_normalized(text: str, needle: str) -> bool:
    """True if normalized text contains normalized needle."""
    return _normalize_surface(needle) in _normalize_surface(text)


def _verb_safe_template(voice: Optional[str], token_id: str, pipeline: PipelineDict) -> str:
    """Return verb-family i3rab template. Passive/active from L8B when available."""
    if (voice or "").strip().lower() == "passive":
        return "فِعْلٌ مَاضٍ مَبْنِيٌّ لِلْمَجْهُولِ مَبْنِيٌّ عَلَى الْفَتْحِ"
    return "فِعْلٌ مَاضٍ مَبْنِيٌّ عَلَى الْفَتْحِ"


def _noun_safe_template(token_id: str, pipeline: PipelineDict, surface: Optional[str] = None) -> str:
    """Return noun-family i3rab text using strongest available structural evidence."""
    rel = _stage15_relation_for_token(token_id, pipeline)
    if rel == "NAIB_SUBJ":
        return "نَائِبُ فَاعِلٍ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ"
    if rel == "SUBJ":
        return "فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ"
    if rel == "OBJ":
        return "مَفْعُولٌ بِهِ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ"
    if rel == "PRED":
        return "خَبَرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ"
    if rel == "JAR_MAJRUR":
        return "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ"
    surf_norm = _normalize_surface(surface or "")
    if surf_norm and surf_norm not in _INDECLINABLE_PROPER_NOUNS:
        return "اسْمٌ مُعْرَبٌ يَحْتَاجُ إِلَى مَزِيدِ تَحَقُّقٍ"
    return "اسْمٌ يَحْتَاجُ إِلَى مَزِيدِ تَحَقُّقٍ"


def _particle_safe_template() -> str:
    """Return particle-family fallback."""
    return "حَرْفٌ مَبْنِيٌّ"


def _apply_family_guardrail(token_results: List[Dict[str, Any]], pipeline: PipelineDict) -> None:
    """Pre-template guardrail: route each token to a family-compatible template."""
    lo = pipeline.get("layer_outputs") or {}
    tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profile_by_id = {str(p.get("token_id")): p for p in (tr8b.get("verb_governance_profiles") or []) if p.get("token_id") is not None}
    for tr in token_results:
        tid = tr.get("token_id")
        if tid is None:
            continue
        surface = (tr.get("surface") or "").strip()
        family = get_token_grammatical_family(str(tid), pipeline, surface=surface)
        if family != "VERB":
            continue
        i3rab_text = (tr.get("i3rab_text") or "").strip()
        if not i3rab_text:
            continue
        text_family = _i3rab_text_grammatical_family(i3rab_text)
        if family == "VERB" and text_family == "NOMINAL":
            profile = profile_by_id.get(str(tid)) or _strong_l8b_profile_for_token(str(tid), pipeline, surface=surface)
            voice = (profile.get("voice") or "").strip() if isinstance(profile, dict) else None
            tr["i3rab_text"] = _verb_safe_template(voice, str(tid), pipeline)
        elif family == "NOUN" and text_family == "VERBAL":
            tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
        elif family == "PARTICLE" and text_family in ("NOMINAL", "VERBAL"):
            tr["i3rab_text"] = _particle_safe_template()


def _validate_and_repair_token_families(token_results: List[Dict[str, Any]], pipeline: PipelineDict) -> None:
    """Post-generation: ensure final i3rab text matches token family."""
    lo = pipeline.get("layer_outputs") or {}
    tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    prof_list = tr8b.get("verb_governance_profiles") or []
    profile_by_id = {str(p.get("token_id")): p for p in prof_list if p.get("token_id") is not None}
    for tr in token_results:
        tid = tr.get("token_id")
        if tid is None:
            continue
        surface = (tr.get("surface") or "").strip()
        family = get_token_grammatical_family(str(tid), pipeline, surface=surface)
        i3rab_text = (tr.get("i3rab_text") or "").strip()
        if not i3rab_text:
            continue
        text_family = _i3rab_text_grammatical_family(i3rab_text)
        if family == "VERB" and text_family == "NOMINAL":
            profile = profile_by_id.get(str(tid)) or _strong_l8b_profile_for_token(str(tid), pipeline, surface=surface)
            voice = (profile.get("voice") or "").strip() if isinstance(profile, dict) else None
            tr["i3rab_text"] = _verb_safe_template(voice, str(tid), pipeline)
        elif family == "NOUN" and text_family == "VERBAL":
            tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
        elif family == "PARTICLE" and text_family in ("NOMINAL", "VERBAL"):
            tr["i3rab_text"] = _particle_safe_template()


def _apply_l11_legacy_i3rab_fixes(
    token_results: List[Dict[str, Any]],
    pipeline: PipelineDict,
) -> None:
    """Patch D: Correct L11 legacy i3rab mislabels using L10B/L4 context."""
    lo = pipeline.get("layer_outputs") or {}
    dsb = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    dsb_links = dsb.get("dependency_links") or []
    l10b = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
    edges = l10b.get("dependency_edges") or []
    nodes = l10b.get("dependency_nodes") or []
    summary = l10b.get("syntax_summary") or {}
    main_clause_type = (summary.get("main_clause_type") or "").strip().lower()
    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    op_words = tr4.get("words") or []
    node_by_id = {n.get("token_id"): n for n in nodes if n.get("token_id") is not None}
    # L10B tokens that are object (maf'ul_bih)
    to_id_maful_bih = {e.get("to_id") for e in edges if (e.get("relation") or "").strip() in ("maf'ul_bih", "maful_bih")}
    dsb_obj_ids = {str(l.get("dependent_id")) for l in dsb_links if (l.get("relation") or "").strip() == "OBJ"}
    dsb_subj_ids = {str(l.get("dependent_id")) for l in dsb_links if (l.get("relation") or "").strip() == "SUBJ"}
    dsb_naib_ids = {str(l.get("dependent_id")) for l in dsb_links if (l.get("relation") or "").strip() == "NAIB_SUBJ"}
    indeclinable_norm = {_normalize_surface(x) for x in _INDECLINABLE_PROPER_NOUNS}
    # First token index that is preposition (harf jar) for D3
    first_pp_idx: Optional[int] = None
    for i, tr in enumerate(token_results):
        surf = (tr.get("surface") or "").strip()
        if not surf:
            continue
        if any((x.get("word") or "").strip() == surf and x.get("operator") for x in op_words):
            first_pp_idx = i
            break
    for tr in token_results:
        tid = tr.get("token_id")
        i3rab_text = tr.get("i3rab_text")
        if not i3rab_text or not isinstance(i3rab_text, str):
            continue
        surface = (tr.get("surface") or "").strip()
        family = get_token_grammatical_family(str(tid), pipeline, surface=surface) if tid is not None else "UNKNOWN"
        # D2: Direct object priority — Stage 15/L10B says object → must be مفعول به not مفعول مطلق
        if tid and (str(tid) in to_id_maful_bih or str(tid) in dsb_obj_ids) and _contains_normalized(i3rab_text, "مفعول مطلق"):
            tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
            i3rab_text = tr["i3rab_text"]
        # Passive role priority — if Stage 15/L10B says نائب فاعل, keep noun token noun-family and prefer نائب فاعل text
        if tid and (str(tid) in dsb_naib_ids or (tr.get("dependency_relation") or "").strip() in ("naib_fa'il", "naib_fail")):
            if _contains_normalized(i3rab_text, "فاعل") and not _contains_normalized(i3rab_text, "نائب فاعل"):
                tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
                i3rab_text = tr["i3rab_text"]
        # Stage 15 subject/object are stronger than weak proper-noun/jamid fallbacks
        if tid and family == "NOUN":
            if str(tid) in dsb_subj_ids and _contains_normalized(i3rab_text, "مبني"):
                tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
                i3rab_text = tr["i3rab_text"]
            if str(tid) in dsb_obj_ids and (_contains_normalized(i3rab_text, "مفعول مطلق") or _contains_normalized(i3rab_text, "مبني")):
                tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
                i3rab_text = tr["i3rab_text"]
        # D1: Proper noun — do not label as مبني unless in indeclinable list
        norm_surf = _normalize_surface(surface)
        if _contains_normalized(i3rab_text, "مبني") and norm_surf not in indeclinable_norm and family == "NOUN":
            tr["i3rab_text"] = _noun_safe_template(str(tid), pipeline, surface=surface)
            i3rab_text = tr["i3rab_text"]
        # D3: Fronted PP — في البيت رجل: رجل = مبتدأ مؤخر not فاعل
        if main_clause_type == "nominal" and first_pp_idx is not None and tid is not None:
            try:
                idx = int(tid)
                if idx > first_pp_idx and _contains_normalized(i3rab_text, "فاعل"):
                    node = node_by_id.get(str(tid))
                    if node and (node.get("relation") or "").strip() not in ("fa'il", "subject"):
                        tr["i3rab_text"] = "مُبْتَدَأٌ مُؤَخَّرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ"
            except (ValueError, TypeError):
                pass


class RealL11I3rab(BaseStage):
    """L11: i3rab — explicit layer; from c2b.words[].c2e.i3rab_text. Eligibility: has_i3rab_evidence for success."""

    def __init__(self) -> None:
        super().__init__("L11_I3RAB", STAGE_NAMES["L11_I3RAB"], 17)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, self.stage_index)
        gates = compute_gates(pipeline)
        gates_applied_list: List[Dict[str, Any]] = [
            gate_entry("has_tokens", gates["has_tokens"]),
            gate_entry("has_i3rab_evidence", gates["has_i3rab_evidence"]),
        ]
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            token_results: List[Dict[str, Any]] = []
            for i, w in enumerate(words_list):
                c2e = w.get("c2e") or {}
                i3rab_text = c2e.get("i3rab_text") if isinstance(c2e, dict) else None
                token_results.append({
                    "token_id": str(i),
                    "surface": w.get("word"),
                    "i3rab_text": i3rab_text,
                    "status": "success" if i3rab_text else "partial",
                })
            _apply_family_guardrail(token_results, pipeline)
            _apply_l11_legacy_i3rab_fixes(token_results, pipeline)
            _validate_and_repair_token_families(token_results, pipeline)
            # Optional: enrich from L10B deep syntax when present (pass-through evidence)
            lo = pipeline.get("layer_outputs") or {}
            l10b = lo.get("L10B_DEEP_SYNTAX") or {}
            tr10b = (l10b.get("transformation_result") or {}).get("dependency_nodes") or []
            node_by_id = {n.get("token_id"): n for n in tr10b if n.get("token_id") is not None}
            for tr in token_results:
                tid = tr.get("token_id")
                node = node_by_id.get(str(tid)) if tid is not None else None
                if node and (node.get("head_id") is not None or node.get("relation")):
                    tr["dependency_head_id"] = node.get("head_id")
                    tr["dependency_relation"] = node.get("relation")
            result = {"token_results": token_results, "count": len(token_results)}
            has_any = gates["has_i3rab_evidence"] or any(t.get("i3rab_text") for t in token_results)
            status = "success" if has_any else "partial"
            next_input = result
            raw = {"token_results": token_results}
            reused = {"file": "fvafk/c2e/enricher", "symbol": "MorphEnricher", "mode": "adapter"}
        else:
            result = {"token_results": []}; status = "missing"
            next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
            gates_applied=gates_applied_list,
        )


class RealL12SemanticRhetorical(BaseStage):
    """L12: Semantic / rhetorical — from c2d, rhetoric_signals. Eligibility: has_sentence_level_evidence."""

    def __init__(self) -> None:
        super().__init__("L12_SEMANTIC_RHETORICAL", STAGE_NAMES["L12_SEMANTIC_RHETORICAL"], 20)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, self.stage_index)
        gates = compute_gates(pipeline)
        gates_applied_list: List[Dict[str, Any]] = [
            gate_entry("has_tokens", gates["has_tokens"]),
            gate_entry("has_sentence_level_evidence", gates["has_sentence_level_evidence"]),
        ]
        if fvafk:
            c2d = fvafk.get("c2d") or {}
            rhetoric = fvafk.get("rhetoric_signals") or []
            result = {
                "sentence_type": c2d.get("sentence_type"),
                "confidence": c2d.get("confidence"),
                "rhetoric_signals": rhetoric,
                "rhetoric_count": len(rhetoric),
            }
            status = "success" if gates["has_sentence_level_evidence"] else "partial"
            next_input = result
            raw = {"c2d": c2d, "rhetoric_signals": rhetoric}
            reused = {"file": "fvafk/c2d, engines/rhetoric", "symbol": "SentenceClassifier, RhetoricSignalsExtractor", "mode": "adapter"}
        else:
            result = {}; status = "missing"; next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
            gates_applied=gates_applied_list,
        )


def get_real_stages_l1_l12() -> List[BaseStage]:
    """Return real adapters for L1–L12 in order (for registry)."""
    return [
        RealL1Normalization(),
        RealL2Tokenization(),
        RealL3Segmentation(),
        RealL4Operators(),
        RealL5WordTyping(),
        RealL6Phonology(),
        RealL7Syllabification(),
        RealL8RootExtraction(),
        RealL8BVerbBabGovernance(),
        RealL9WaznMatching(),
        RealL14JamidMushtaq(),
        RealL13VerbTransformation(),
        RealL12GenderNumber(),
        RealL10Syntax(),
        RealL10BDeepSyntax(),
        RealL11I3rab(),
        RealL11BCausalI3rab(),
        RealL17RuleBasedI3rab(),
        RealL12SemanticRhetorical(),
    ]
