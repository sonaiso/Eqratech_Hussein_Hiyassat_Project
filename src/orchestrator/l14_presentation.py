# -*- coding: utf-8 -*-
"""
L14 — Real presentation/rendering layer.

Renders pipeline object into readable output (compact, detailed, debug).
Uses existing pipeline outputs only; no linguistic logic.
i3rab is an explicit standalone section.
"""

from __future__ import annotations

from typing import Any, Dict, List

from .builders import build_layer_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import STAGE_ORDER


def _section(section_id: str, title: str, content: str) -> Dict[str, Any]:
    return {"id": section_id, "title": title, "content": content}


def _render_compact(pipeline: Dict[str, Any]) -> Dict[str, Any]:
    """Short readable summary."""
    text = (pipeline.get("original_text") or "").strip()
    fv = pipeline.get("final_validation") or {}
    validity = fv.get("global_validity") or "unknown"
    confidence = fv.get("final_confidence")
    issues = fv.get("issues") or []
    L12 = (pipeline.get("layer_outputs") or {}).get("L12_SEMANTIC_RHETORICAL") or {}
    tr12 = L12.get("transformation_result") or {}
    sentence_type = tr12.get("sentence_type") or "—"
    L11 = (pipeline.get("layer_outputs") or {}).get("L11_I3RAB") or {}
    tr11 = L11.get("transformation_result") or {}
    token_results = tr11.get("token_results") or []
    i3rab_lines = []
    for t in token_results[:5]:
        surface = t.get("surface") or ""
        i3rab = (t.get("i3rab_text") or "").strip()
        if i3rab:
            i3rab_lines.append(f"  {surface}: {i3rab[:60]}{'…' if len(i3rab) > 60 else ''}")
    i3rab_block = "\n".join(i3rab_lines) if i3rab_lines else "—"
    L8 = (pipeline.get("layer_outputs") or {}).get("L8_ROOT_EXTRACTION") or {}
    tr8 = L8.get("transformation_result") or {}
    words8 = tr8.get("words") or []
    roots = [f"{w.get('word')}: {w.get('root') or '—'}" for w in words8[:5]]
    roots_line = "; ".join(roots) if roots else "—"
    validation_note = f"{len(issues)} issue(s)" if issues else "No issues."
    summary = (
        f"Input: {text[:80]}{'…' if len(text) > 80 else ''}\n"
        f"Validity: {validity}" + (f" (confidence: {confidence})" if confidence is not None else "") + "\n"
        f"Sentence type: {sentence_type}\n"
        f"Roots: {roots_line}\n"
        f"I3rab: {i3rab_block if i3rab_lines else '—'}\n"
        f"Validation: {validation_note}"
    )
    return {
        "mode": "compact",
        "summary": summary,
        "sections": [_section("compact_summary", "Summary", summary)],
        "artifacts": {},
    }


def _render_detailed(pipeline: Dict[str, Any]) -> Dict[str, Any]:
    """Layer-by-layer readable report."""
    sections: List[Dict[str, Any]] = []
    lo = pipeline.get("layer_outputs") or {}
    fv = pipeline.get("final_validation") or {}
    text = (pipeline.get("original_text") or "").strip()

    # 1. Overview
    validity = fv.get("global_validity") or "unknown"
    confidence = fv.get("final_confidence")
    overview = f"النص: {text}\n\nالصلاحية: {validity}"
    if confidence is not None:
        overview += f"\nالثقة: {confidence}"
    overview += "\n\nنتيجة المسار من التحقق (L13)."
    sections.append(_section("overview", "Overview", overview))

    # 2. Stage Status Summary (L14 not yet in layer_outputs when we render, so show as success)
    lines = []
    for lid in STAGE_ORDER:
        if lid == "L14_PRESENTATION":
            lines.append(f"  {lid}: success")
            continue
        layer = lo.get(lid) or {}
        st = layer.get("status", "missing")
        lines.append(f"  {lid}: {st}")
    sections.append(_section("stage_status", "Stage Status Summary", "\n".join(lines)))

    # 3. Token / Word Summary
    L2 = lo.get("L2_TOKENIZATION") or {}
    tr2 = L2.get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    L5 = lo.get("L5_WORD_TYPING") or {}
    tr5 = L5.get("transformation_result") or {}
    words5 = tr5.get("words") or []
    token_lines = [f"  {t.get('word', '')}" for t in tokens]
    kind_lines = [f"  {w.get('word', '')}: {w.get('kind', '')}" for w in words5]
    content = "Tokens (L2):\n" + ("\n".join(token_lines) if token_lines else "  (none)")
    content += "\n\nWord typing (L5):\n" + ("\n".join(kind_lines) if kind_lines else "  (none)")
    sections.append(_section("token_word", "Token / Word Summary", content))

    # 4. Phonology / Syllables
    L6 = lo.get("L6_PHONOLOGY") or {}
    L7 = lo.get("L7_SYLLABIFICATION") or {}
    tr6 = L6.get("transformation_result") or {}
    tr7 = L7.get("transformation_result") or {}
    ph = f"L6 status: {L6.get('status', '')}; units: {tr6.get('num_units')}; gates: {tr6.get('gates_count')}."
    syl = f"L7 status: {L7.get('status', '')}; syllables count: {tr7.get('count')}."
    sections.append(_section("phonology_syllables", "Phonology / Syllables", f"{ph}\n{syl}"))

    # 5. Morphology
    L8 = lo.get("L8_ROOT_EXTRACTION") or {}
    L9 = lo.get("L9_WAZN_MATCHING") or {}
    tr8 = L8.get("transformation_result") or {}
    tr9 = L9.get("transformation_result") or {}
    st8 = L8.get("status", "")
    st9 = L9.get("status", "")
    if st8 == "skipped":
        morph = "L8 (roots): skipped (no morphology candidate or no tokens)."
    else:
        words8 = tr8.get("words") or []
        morph = "L8 roots:\n" + "\n".join(f"  {w.get('word')}: {w.get('root') or '—'}" for w in words8) if words8 else "L8: no words."
    if st9 == "skipped":
        morph += "\n\nL9 (wazn): skipped (no root candidate)."
    else:
        words9 = tr9.get("words") or []
        morph += "\n\nL9 wazn:\n" + "\n".join(f"  {w.get('word')}: {w.get('template') or w.get('word_wazn') or '—'}" for w in words9) if words9 else ""
    sections.append(_section("morphology", "Morphology", morph))

    # 6. Syntax
    L10 = lo.get("L10_SYNTAX") or {}
    tr10 = L10.get("transformation_result") or {}
    st10 = L10.get("status", "")
    err10 = tr10.get("error") or (L10.get("errors") or [None])[0]
    if st10 == "failed":
        syntax = f"L10 syntax: failed. {err10 or ''}"
    else:
        wf = tr10.get("word_forms") or []
        links = (tr10.get("links") or {}).get("isnadi") or []
        syntax = f"L10 status: {st10}. Word forms: {len(wf)}; isnadi links: {len(links)}."
    sections.append(_section("syntax", "Syntax", syntax))

    # 7. I3rab (explicit standalone section)
    L11 = lo.get("L11_I3RAB") or {}
    tr11 = L11.get("transformation_result") or {}
    token_results = tr11.get("token_results") or []
    i3rab_lines = []
    for t in token_results:
        surface = t.get("surface") or ""
        i3rab_text = (t.get("i3rab_text") or "").strip()
        i3rab_lines.append(f"  {surface}: {i3rab_text if i3rab_text else '—'}")
    i3rab_content = "I3rab (L11) — إعراب:\n" + ("\n".join(i3rab_lines) if i3rab_lines else "  (no token results)")
    sections.append(_section("i3rab", "I3rab", i3rab_content))

    # 8. Semantic / Rhetorical
    L12 = lo.get("L12_SEMANTIC_RHETORICAL") or {}
    tr12 = L12.get("transformation_result") or {}
    sentence_type = tr12.get("sentence_type") or "—"
    rhetoric = tr12.get("rhetoric_signals") or []
    rhet = "\n".join(f"  {s.get('type', s) if isinstance(s, dict) else s}" for s in rhetoric[:10]) if rhetoric else "  (none)"
    sections.append(_section("semantic_rhetorical", "Semantic / Rhetorical", f"Sentence type: {sentence_type}\n\nRhetoric signals:\n{rhet}"))

    # 9. Validation
    issues = fv.get("issues") or []
    issue_lines = [f"  [{i.get('severity')}] {i.get('code')}: {i.get('message')}" for i in issues]
    val = f"Global validity: {validity}\nFinal confidence: {confidence}\n\nIssues:\n" + ("\n".join(issue_lines) if issue_lines else "  (none)")
    sections.append(_section("validation", "Validation", val))

    summary = f"Pipeline rendered (detailed). Validity: {validity}. Sections: {len(sections)}."
    return {
        "mode": "detailed",
        "summary": summary,
        "sections": sections,
        "artifacts": {},
    }


def _render_debug(pipeline: Dict[str, Any]) -> Dict[str, Any]:
    """Structural summary for developers."""
    lo = pipeline.get("layer_outputs") or {}
    fv = pipeline.get("final_validation") or {}
    request_id = pipeline.get("request_id") or ""
    lines = [
        f"request_id: {request_id}",
        f"stage_order: {STAGE_ORDER}",
        "",
        "Stage statuses:",
    ]
    for lid in STAGE_ORDER:
        layer = lo.get(lid) or {}
        st = layer.get("status", "missing")
        warnings = len(layer.get("warnings") or [])
        errors = len(layer.get("errors") or [])
        lines.append(f"  {lid}: {st} (warnings={warnings}, errors={errors})")
    lines.append("")
    lines.append("Validation:")
    lines.append(f"  global_validity: {fv.get('global_validity')}")
    lines.append(f"  issue_count: {len(fv.get('issues') or [])}")
    for i in (fv.get("issues") or [])[:15]:
        lines.append(f"    {i.get('code')} [{i.get('severity')}] {i.get('layer_id')}")
    content = "\n".join(lines)
    return {
        "mode": "debug",
        "summary": f"Debug view. Validity: {fv.get('global_validity')}. Issues: {len(fv.get('issues') or [])}.",
        "sections": [_section("debug", "Debug", content)],
        "artifacts": {"stage_ids": list(lo.keys())},
    }


def render_pipeline(pipeline: Dict[str, Any], mode: str = "detailed") -> Dict[str, Any]:
    """
    Render pipeline into readable output. mode: compact | detailed | debug.
    Uses pipeline data only; no fabricated content.
    """
    mode = (mode or "detailed").strip().lower()
    if mode == "compact":
        out = _render_compact(pipeline)
    elif mode == "debug":
        out = _render_debug(pipeline)
    else:
        out = _render_detailed(pipeline)
    return out


class RealL14Presentation(BaseStage):
    """L14: Presentation — render pipeline to readable output (compact/detailed/debug)."""

    def __init__(self) -> None:
        super().__init__("L14_PRESENTATION", STAGE_NAMES["L14_PRESENTATION"], 14)

    def run(self, pipeline: Dict[str, Any]) -> Dict[str, Any]:
        render_mode = pipeline.get("_render_mode") or "detailed"
        try:
            rendered = render_pipeline(pipeline, mode=render_mode)
        except Exception as e:
            rendered = {
                "mode": render_mode,
                "summary": f"Rendering failed: {e}",
                "sections": [],
                "artifacts": {},
            }
        status = "success" if rendered.get("sections") else "partial"
        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input={
                "layer_outputs_keys": list((pipeline.get("layer_outputs") or {}).keys()),
                "final_validation": bool(pipeline.get("final_validation")),
                "render_mode": render_mode,
            },
            transformation_result=rendered,
            raw_module_output=rendered,
            next_input=rendered,
        )
