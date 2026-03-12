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
    """L8: Root extraction — from c2b.words (root)."""

    def __init__(self) -> None:
        super().__init__("L8_ROOT_EXTRACTION", STAGE_NAMES["L8_ROOT_EXTRACTION"], 8)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 8)
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
            status = "success"
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
        )


class RealL9WaznMatching(BaseStage):
    """L9: Wazn matching — from c2b.words (pattern.template, word_wazn)."""

    def __init__(self) -> None:
        super().__init__("L9_WAZN_MATCHING", STAGE_NAMES["L9_WAZN_MATCHING"], 9)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 9)
        if fvafk and isinstance(fvafk.get("c2b"), dict):
            words_list = fvafk["c2b"].get("words") or []
            items = []
            for w in words_list:
                pat = w.get("pattern") or {}
                template = pat.get("template") if isinstance(pat, dict) else None
                wazn = w.get("word_wazn") or w.get("features", {}).get("word_wazn") or template
                items.append({"word": w.get("word"), "template": template, "word_wazn": wazn})
            result = {"words": items, "count": len(items)}
            status = "success"
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
        )


class RealL10Syntax(BaseStage):
    """L10: Syntax — from syntax (word_forms, links.isnadi); may have error."""

    def __init__(self) -> None:
        super().__init__("L10_SYNTAX", STAGE_NAMES["L10_SYNTAX"], 10)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 10)
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


class RealL11I3rab(BaseStage):
    """L11: i3rab — explicit layer; from c2b.words[].c2e.i3rab_text."""

    def __init__(self) -> None:
        super().__init__("L11_I3RAB", STAGE_NAMES["L11_I3RAB"], 11)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 11)
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
            result = {"token_results": token_results, "count": len(token_results)}
            has_any = any(t.get("i3rab_text") for t in token_results)
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
        )


class RealL12SemanticRhetorical(BaseStage):
    """L12: Semantic / rhetorical — from c2d, rhetoric_signals."""

    def __init__(self) -> None:
        super().__init__("L12_SEMANTIC_RHETORICAL", STAGE_NAMES["L12_SEMANTIC_RHETORICAL"], 12)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        fvafk = _get_fvafk(pipeline)
        received = get_previous_output(pipeline, 12)
        if fvafk:
            c2d = fvafk.get("c2d") or {}
            rhetoric = fvafk.get("rhetoric_signals") or []
            result = {
                "sentence_type": c2d.get("sentence_type"),
                "confidence": c2d.get("confidence"),
                "rhetoric_signals": rhetoric,
                "rhetoric_count": len(rhetoric),
            }
            status = "success"
            next_input = result
            raw = {"c2d": c2d, "rhetoric_signals": rhetoric}
            reused = {"file": "fvafk/c2d, engines/rhetoric", "symbol": "SentenceClassifier, RhetoricSignalsExtractor", "mode": "adapter"}
        else:
            result = {}; status = "missing"; next_input = received or {}; raw = {}; reused = None
        return build_layer_output(
            self.layer_id, self.layer_name, self.stage_index, status,
            received_input=received, transformation_result=result, raw_module_output=raw,
            next_input=next_input, reused_module=reused,
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
        RealL9WaznMatching(),
        RealL10Syntax(),
        RealL11I3rab(),
        RealL12SemanticRhetorical(),
    ]
