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
from .explainability import build_evidence_trace
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
    # Stage 8: short "why" lines from evidence trace
    trace = build_evidence_trace(pipeline)
    why_lines: List[str] = []
    for e in trace:
        if e.get("status") == "skipped" and e.get("supporting_stage") in ("L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING"):
            why_lines.append(f"Why: {e.get('claim', '')[:60]}…" if len(e.get("claim", "")) > 60 else f"Why: {e.get('claim', '')}")
            break
    if not why_lines and trace:
        v = next((e for e in trace if e.get("supporting_stage") == "L13_VALIDATION"), None)
        if v and v.get("limitation"):
            why_lines.append(f"Validation: {v.get('limitation', '')[:70]}")
    L12B = (pipeline.get("layer_outputs") or {}).get("L12B_ANALOGICAL_REASONING") or {}
    tr12b = L12B.get("transformation_result") or {}
    analogical_used = (tr12b.get("analogical_summary") or {}).get("total_inferences", 0) > 0
    analogical_line = "\nAnalogical inference used: yes" if analogical_used else "\nAnalogical inference used: no"
    cf = pipeline.get("cognitive_fusion") or {}
    fusion_conf = cf.get("global_confidence")
    fusion_line = f"\nFusion confidence: {fusion_conf}" if fusion_conf is not None else ""
    post_audit = pipeline.get("post_stage13_audit") or {}
    pa_consistency = post_audit.get("fusion_consistency")
    fusion_audit_line = f"\nFusion audit: {pa_consistency}" if pa_consistency else ""
    L10B = (pipeline.get("layer_outputs") or {}).get("L10B_DEEP_SYNTAX") or {}
    tr10b = L10B.get("transformation_result") or {}
    sum10b = tr10b.get("syntax_summary") or {}
    deep_syntax_resolved = sum10b.get("resolved_edges", 0)
    deep_syntax_line = f"\nDeep syntax: {deep_syntax_resolved} relations resolved" if deep_syntax_resolved is not None else ""
    L8B = (pipeline.get("layer_outputs") or {}).get("L8B_VERB_BAB_GOVERNANCE") or {}
    sum8b = (L8B.get("transformation_result") or {}).get("governance_summary") or {}
    verb_gov_resolved = sum8b.get("resolved_profiles", 0)
    verb_governance_line = f"\nVerb governance: {verb_gov_resolved} verb profiles resolved" if verb_gov_resolved is not None else ""
    L11B = (pipeline.get("layer_outputs") or {}).get("L11B_CAUSAL_I3RAB") or {}
    sum11b = (L11B.get("transformation_result") or {}).get("i3rab_summary") or {}
    causal_res = sum11b.get("resolved_tokens")
    causal_cand = sum11b.get("candidate_tokens")
    causal_i3rab_line = f"\nStructured i3rab reasoning: {causal_res} resolved / {causal_cand} candidate" if (causal_res is not None or causal_cand is not None) else ""
    perf_line = ""
    if pipeline.get("profiling"):
        total_ms = (pipeline["profiling"] or {}).get("total_time_ms")
        if total_ms is not None:
            perf_line = f"\nTotal time: {total_ms} ms"
    summary = (
        f"Input: {text[:80]}{'…' if len(text) > 80 else ''}\n"
        + analogical_line + "\n"
        f"Validity: {validity}" + (f" (confidence: {confidence})" if confidence is not None else "") + "\n"
        f"Sentence type: {sentence_type}\n"
        f"Roots: {roots_line}\n"
        f"I3rab: {i3rab_block if i3rab_lines else '—'}\n"
        f"Validation: {validation_note}"
        + fusion_line
        + fusion_audit_line
        + deep_syntax_line
        + verb_governance_line
        + causal_i3rab_line
        + ("\n" + "\n".join(why_lines) if why_lines else "")
        + perf_line
    )
    artifacts: Dict[str, Any] = {"evidence_trace": trace}
    return {
        "mode": "compact",
        "summary": summary,
        "sections": [_section("compact_summary", "Summary", summary)],
        "artifacts": artifacts,
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

    # 5b. Verb governance (L8B)
    L8B = lo.get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr8b = L8B.get("transformation_result") or {}
    profiles8b = tr8b.get("verb_governance_profiles") or []
    sum8b = tr8b.get("governance_summary") or {}
    gov_lines = [f"Verbs with profile: {sum8b.get('verb_count', 0)} | resolved: {sum8b.get('resolved_profiles', 0)} | candidate: {sum8b.get('candidate_profiles', 0)}"]
    for p in profiles8b:
        if p.get("status") == "not_applicable":
            continue
        gov_lines.append(f"  {p.get('surface')}: root={p.get('root') or '—'} | root_type={p.get('root_type') or '—'} | bab={p.get('bab') or '—'} | bab_status={p.get('bab_status') or '—'}")
        tm = p.get("tense_mapping") or {}
        gov_lines.append(f"    past_pattern={tm.get('past_pattern') or '—'} | present_pattern={tm.get('present_pattern') or '—'} | present_passive_pattern={tm.get('present_passive_pattern') or '—'}")
        gov_lines.append(f"    transitivity={p.get('transitivity')} | objects={p.get('objects')} | governance_family={p.get('governance_family')}")
        voice_ev = p.get("voice_evidence") or {}
        voice = p.get("voice") or voice_ev.get("voice") or "—"
        rule = voice_ev.get("rule") or "—"
        gov_lines.append(f"    voice={voice} | voice_rule={rule} | expected_subject_role={p.get('expected_subject_role') or '—'}")
        if (p.get("required_prepositions") or []):
            gov_lines.append(f"    required_prepositions={p.get('required_prepositions')}")
        if p.get("special_class"):
            gov_lines.append(f"    special_class={p.get('special_class')}")
        gov_lines.append(f"    valency_class={p.get('valency_class') or '—'} | valency_required_roles={p.get('valency_required_roles') or []} | valency_optional_roles={p.get('valency_optional_roles') or []} | valency_confidence={p.get('valency_confidence')}")
        gov_lines.append(f"    confidence={p.get('confidence')} | status={p.get('status')}")
    sections.append(_section("verb_governance", "VERB GOVERNANCE PROFILE", "\n".join(gov_lines) if gov_lines else "No verb profiles."))

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

    # 6b. Deep Syntax (L10B)
    L10B = lo.get("L10B_DEEP_SYNTAX") or {}
    tr10b = L10B.get("transformation_result") or {}
    summary10b = tr10b.get("syntax_summary") or {}
    nodes10b = tr10b.get("dependency_nodes") or []
    edges10b = tr10b.get("dependency_edges") or []
    clauses10b = tr10b.get("clause_units") or []
    deep_syntax_lines = [
        f"Main clause type: {summary10b.get('main_clause_type', '—')}",
        f"Resolved edges: {summary10b.get('resolved_edges', 0)}",
        f"Candidate edges: {summary10b.get('candidate_edges', 0)}",
        f"Unresolved tokens: {summary10b.get('unresolved_tokens', 0)}",
        f"Parse strength: {summary10b.get('parse_strength', '—')}",
    ]
    if summary10b.get("verb_governance_applied"):
        deep_syntax_lines.append(f"Verb governance: applied; alignment score: {summary10b.get('governance_alignment_score', '—')}")
        for m in (summary10b.get("missing_arguments") or [])[:5]:
            deep_syntax_lines.append(f"  Missing: {m}")
        for il in (summary10b.get("illegal_arguments") or [])[:5]:
            deep_syntax_lines.append(f"  Illegal: {il}")
    if summary10b.get("passive_alignment_used"):
        deep_syntax_lines.append("Passive alignment used (L8B → نائب فاعل).")
    if summary10b.get("valency_alignment_used"):
        deep_syntax_lines.append("Valency alignment used.")
    idafa_supp = [e for e in edges10b if e.get("idafa_suppression")]
    if idafa_supp:
        deep_syntax_lines.append(f"Weak idafa suppressed: {len(idafa_supp)} edge(s).")
    for note in (summary10b.get("advisory_notes") or [])[:5]:
        deep_syntax_lines.append(f"Advisory: {note}")
    trace10b = tr10b.get("syntax_reasoning_trace") or []
    for t in trace10b[:8]:
        deep_syntax_lines.append(f"  Trace: {t}")
    for e in edges10b[:10]:
        deep_syntax_lines.append(f"  {e.get('from_id')} → {e.get('to_id')}: {e.get('relation')} ({e.get('status')})")
    deep_syntax_lines.append(f"Clause units: {len(clauses10b)}")
    for c in clauses10b[:5]:
        deep_syntax_lines.append(f"  {c.get('clause_id')}: {c.get('type')} [{c.get('start_token_id')}-{c.get('end_token_id')}]")
    # Connective/discourse hints from shared connectives layer (optional)
    conn_hints = [(n.get("surface"), n.get("connective_group"), n.get("connective_hint")) for n in nodes10b if n.get("connective_group")]
    if conn_hints:
        deep_syntax_lines.append("Connective hints (shared layer):")
        for surf, grp, hint in conn_hints[:10]:
            deep_syntax_lines.append(f"  {surf}: group={grp} hint={hint or '—'}")
    sections.append(_section("deep_syntax", "DEEP SYNTAX STRUCTURE", "\n".join(deep_syntax_lines)))

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

    # 7b. Causal I3rab Reasoning (L11B)
    L11B = lo.get("L11B_CAUSAL_I3RAB") or {}
    tr11b = L11B.get("transformation_result") or {}
    sum11b = tr11b.get("i3rab_summary") or {}
    reasoning_list = tr11b.get("token_i3rab_reasoning") or []
    causal_lines = [
        f"Resolved: {sum11b.get('resolved_tokens', 0)}",
        f"Candidate: {sum11b.get('candidate_tokens', 0)}",
        f"Unresolved: {sum11b.get('unresolved_tokens', 0)}",
    ]
    naib_count = sum(1 for r in reasoning_list if (r.get("role") or "").strip() == "نائب فاعل")
    if naib_count:
        causal_lines.append(f"نائب فاعل assigned: {naib_count}")
    if any(r.get("limitations") and any("weak idafa suppressed" in (x or "") for x in r.get("limitations", [])) for r in reasoning_list):
        causal_lines.append("Weak idafa suppressed in role prioritization.")
    causal_lines.append("Per-token (role | governing_factor | case/mood | confidence):")
    for r in reasoning_list[:15]:
        causal_lines.append(f"  {r.get('surface')}: {r.get('role')} | {r.get('governing_factor') or '—'} | {r.get('case_or_mood') or '—'} | {r.get('confidence')}")
    unresolved_items = [r.get("surface") for r in reasoning_list if r.get("role_status") == "unresolved"]
    if unresolved_items:
        causal_lines.append(f"Unresolved tokens: {', '.join(unresolved_items[:10])}")
    sections.append(_section("causal_i3rab", "CAUSAL I'RAB REASONING", "\n".join(causal_lines)))

    # 7c. SECTION 4d — SEMANTIC ROLES (structural projection only)
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    sem_roles = proj.get("semantic_roles") or []
    sem_by_idx = {r["token_index"]: r for r in sem_roles if r.get("token_index") is not None}
    sem_lines = [f"  projection_coverage: {proj.get('projection_coverage', 0)}"]
    sem_lines.append("  surface | syntactic_role | semantic_role | confidence")
    for idx, r in enumerate(reasoning_list):
        surf = r.get("surface") or "—"
        syn_role = (r.get("role") or "").strip() or "—"
        sr = sem_by_idx.get(idx)
        if sr:
            sem_lines.append(f"  {surf} | {syn_role} | {sr.get('semantic_role', '—')} | {sr.get('confidence', '—')}")
        else:
            sem_lines.append(f"  {surf} | {syn_role} | — | —")
    sections.append(_section("semantic_roles", "SECTION 4d — SEMANTIC ROLES", "\n".join(sem_lines)))

    # 8. Semantic / Rhetorical
    L12 = lo.get("L12_SEMANTIC_RHETORICAL") or {}
    tr12 = L12.get("transformation_result") or {}
    sentence_type = tr12.get("sentence_type") or "—"
    rhetoric = tr12.get("rhetoric_signals") or []
    rhet = "\n".join(f"  {s.get('type', s) if isinstance(s, dict) else s}" for s in rhetoric[:10]) if rhetoric else "  (none)"
    sections.append(_section("semantic_rhetorical", "Semantic / Rhetorical", f"Sentence type: {sentence_type}\n\nRhetoric signals:\n{rhet}"))

    # 8b. Analogical Reasoning (L12B)
    L12B = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr12b = L12B.get("transformation_result") or {}
    inferences_12b = tr12b.get("analogical_inferences") or []
    resolutions_12b = tr12b.get("ambiguity_resolutions") or []
    summary_12b = tr12b.get("analogical_summary") or {}
    analogical_lines = [f"Inferences: {summary_12b.get('total_inferences', len(inferences_12b))} (strong: {summary_12b.get('strong_count', 0)}, weak: {summary_12b.get('weak_count', 0)})"]
    for inf in inferences_12b[:5]:
        analogical_lines.append(f"  [{inf.get('reasoning_type')}] {inf.get('claim', '')[:70]}{'…' if len(inf.get('claim', '')) > 70 else ''}")
    for res in resolutions_12b[:3]:
        analogical_lines.append(f"  Resolution: {res.get('token')} -> {res.get('preferred_role')} ({res.get('reason', '')[:50]})")
    analogical_content = "\n".join(analogical_lines) if analogical_lines else "No analogical inferences."
    sections.append(_section("analogical_reasoning", "Analogical Reasoning", analogical_content))

    # 9. Validation
    issues = fv.get("issues") or []
    issue_lines = [f"  [{i.get('severity')}] {i.get('code')}: {i.get('message')}" for i in issues]
    val = f"Global validity: {validity}\nFinal confidence: {confidence}\n\nIssues:\n" + ("\n".join(issue_lines) if issue_lines else "  (none)")
    sections.append(_section("validation", "Validation", val))

    # 9b. Cognitive Fusion Stability
    cf = pipeline.get("cognitive_fusion") or {}
    fusion_mode = cf.get("fusion_mode") or "—"
    global_conf = cf.get("global_confidence")
    token_states = cf.get("token_states") or []
    high = cf.get("tokens_high_confidence", 0)
    low = cf.get("tokens_low_confidence", 0)
    unresolved = cf.get("unresolved_ambiguities", 0)
    n = len(token_states)
    pct_stable = (n - low) / n * 100 if n else 0
    pct_ambig = (unresolved / n * 100) if n else 0
    fusion_lines = [f"Fusion mode: {fusion_mode}", f"Global confidence: {global_conf}"]
    fusion_lines.append(f"Tokens stabilized: {pct_stable:.0f}%")
    fusion_lines.append(f"Tokens ambiguous: {pct_ambig:.0f}%")
    sections.append(_section("cognitive_fusion_stability", "Cognitive Fusion Stability", "\n".join(fusion_lines)))

    # 9c. POST-STAGE-13 FUSION AUDIT
    post_audit = pipeline.get("post_stage13_audit") or {}
    pa_consistency = post_audit.get("fusion_consistency") or "—"
    pa_resolved = post_audit.get("resolved_conflicts", 0)
    pa_remaining = post_audit.get("remaining_ambiguities", 0)
    pa_issues = post_audit.get("issues") or []
    pa_notes = post_audit.get("advisory_notes") or []
    pa_lines = [f"Fusion consistency: {pa_consistency}", f"Resolved conflicts: {pa_resolved}", f"Remaining ambiguities: {pa_remaining}"]
    pa_lines.append("Issues:")
    for i in pa_issues[:10]:
        pa_lines.append(f"  [{i.get('severity')}] {i.get('code')}: {i.get('message', '')[:60]}")
    if not pa_issues:
        pa_lines.append("  (none)")
    pa_lines.append("Advisory notes: " + "; ".join(pa_notes) if pa_notes else "Advisory notes: (none)")
    sections.append(_section("post_stage13_fusion_audit", "POST-STAGE-13 FUSION AUDIT", "\n".join(pa_lines)))

    # Stage 8: evidence-aware explanation sections
    trace = build_evidence_trace(pipeline)
    artifacts_detail: Dict[str, Any] = {"evidence_trace": trace}

    # 10. Evidence Trace Overview
    supported_stages = list({e["supporting_stage"] for e in trace if e.get("status") == "supported"})
    skipped_stages = list({e["supporting_stage"] for e in trace if e.get("status") == "skipped"})
    overview_ev = "Stages with decisive evidence: " + (", ".join(sorted(supported_stages)) if supported_stages else "none")
    overview_ev += "\nStages skipped (gate/eligibility): " + (", ".join(sorted(skipped_stages)) if skipped_stages else "none")
    sections.append(_section("evidence_trace_overview", "Evidence Trace Overview", overview_ev))

    # 11. Morphology Evidence
    morph_ev = []
    for e in trace:
        if e.get("supporting_stage") in ("L8_ROOT_EXTRACTION", "L9_WAZN_MATCHING"):
            morph_ev.append(f"  [{e.get('supporting_stage')}] {e.get('claim', '')}")
            for ev in (e.get("evidence") or [])[:5]:
                morph_ev.append(f"    {ev}")
            if e.get("limitation"):
                morph_ev.append(f"    Limitation: {e['limitation']}")
    sections.append(_section("morphology_evidence", "Morphology Evidence", "\n".join(morph_ev) if morph_ev else "  (no morphology evidence)"))

    # 12. I3rab Evidence
    i3rab_ev = []
    for e in trace:
        if e.get("supporting_stage") == "L11_I3RAB":
            i3rab_ev.append(f"  {e.get('claim', '')}")
            for ev in (e.get("evidence") or [])[:6]:
                i3rab_ev.append(f"    {ev}")
            if e.get("confidence_hint"):
                i3rab_ev.append(f"    Source: {e['confidence_hint']}")
            if e.get("limitation"):
                i3rab_ev.append(f"    Limitation: {e['limitation']}")
    sections.append(_section("i3rab_evidence", "I3rab Evidence", "\n".join(i3rab_ev) if i3rab_ev else "  (no i3rab evidence)"))

    # 13. Validation Reasoning
    val_ev = []
    for e in trace:
        if e.get("supporting_stage") == "L13_VALIDATION":
            val_ev.append(f"  {e.get('claim', '')}")
            for ev in (e.get("evidence") or [])[:8]:
                val_ev.append(f"    {ev}")
            if e.get("limitation"):
                val_ev.append(f"  Why validity: {e['limitation']}")
    sections.append(_section("validation_reasoning", "Validation Reasoning", "\n".join(val_ev) if val_ev else "  (no validation evidence)"))

    # 14. Skipped/Partial Reasoning
    skip_ev = []
    for e in trace:
        if e.get("status") in ("skipped", "limited", "absent"):
            skip_ev.append(f"  [{e.get('supporting_stage')}] {e.get('claim', '')}")
            if e.get("limitation"):
                skip_ev.append(f"    Reason: {e['limitation']}")
            for g in (e.get("evidence") or [])[:3]:
                skip_ev.append(f"    {g}")
    sections.append(_section("skipped_partial_reasoning", "Skipped/Partial Reasoning", "\n".join(skip_ev) if skip_ev else "  (no skipped/partial stages)"))

    # 15. Performance Summary (Stage 11; when profiling present)
    if pipeline.get("profiling"):
        pf = pipeline["profiling"]
        perf_lines = [
            f"Total time: {pf.get('total_time_ms')} ms",
            f"Stages run: {pf.get('stages_run_count')}, skipped: {pf.get('stages_skipped_count')}",
            f"Slowest stage: {pf.get('slowest_stage_id')} ({pf.get('slowest_stage_time_ms')} ms)",
        ]
        per_stage = pf.get("per_stage") or {}
        for sid in STAGE_ORDER[:5]:  # first 5 only in detailed
            s = per_stage.get(sid) or {}
            perf_lines.append(f"  {sid}: {s.get('elapsed_ms')} ms, {s.get('status')}")
        sections.append(_section("performance_summary", "Performance Summary", "\n".join(perf_lines)))

    summary = f"Pipeline rendered (detailed). Validity: {validity}. Sections: {len(sections)}."
    return {
        "mode": "detailed",
        "summary": summary,
        "sections": sections,
        "artifacts": artifacts_detail,
    }


def _render_debug(pipeline: Dict[str, Any]) -> Dict[str, Any]:
    """Structural summary for developers; includes stage-to-evidence trace."""
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
    # Stage 8: stage-to-evidence trace summary
    trace = build_evidence_trace(pipeline)
    lines.append("")
    lines.append("Evidence trace (stage -> status):")
    for e in trace[:20]:
        c = e.get("claim", "")
        lines.append(f"  {e.get('supporting_stage')}: {e.get('status')} | {c[:50]}{'…' if len(c) > 50 else ''}")
    # L12B: inference count
    L12B = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr12b = L12B.get("transformation_result") or {}
    summary_12b = tr12b.get("analogical_summary") or {}
    lines.append("")
    lines.append(f"L12B_ANALOGICAL_REASONING: inferences={summary_12b.get('total_inferences', 0)}, resolutions={len(tr12b.get('ambiguity_resolutions') or [])}")

    # L13 Cognitive Fusion
    cf = pipeline.get("cognitive_fusion") or {}
    lines.append("")
    lines.append("L13 fusion:")
    for ts in (cf.get("token_states") or [])[:10]:
        tok = ts.get("token", "")
        pos = ts.get("stable_pos", "")
        conf = ts.get("confidence")
        sources = [s.get("source", "") for s in (ts.get("evidence_stack") or [])]
        lines.append(f"  {tok} -> POS={pos} conf={conf} sources={sources}")
    if not (cf.get("token_states")):
        lines.append("  (no token states)")
    L8B = lo.get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr8b = L8B.get("transformation_result") or {}
    profiles8b = tr8b.get("verb_governance_profiles") or []
    lines.append("")
    lines.append("L8B Verb Bab Governance:")
    for p in profiles8b[:15]:
        if p.get("status") == "not_applicable":
            continue
        ve = p.get("voice_evidence") or {}
        tm = p.get("tense_mapping") or {}
        lines.append(f"  {p.get('surface')} -> bab={p.get('bab')} bab_status={p.get('bab_status')} valency_class={p.get('valency_class')} required_roles={p.get('valency_required_roles') or []} past={tm.get('past_pattern')} pres={tm.get('present_pattern')} pres_pass={tm.get('present_passive_pattern')} voice={p.get('voice')} transitivity={p.get('transitivity')} conf={p.get('confidence')}")
    lines.append(f"  summary: resolved={tr8b.get('governance_summary', {}).get('resolved_profiles')} candidate={tr8b.get('governance_summary', {}).get('candidate_profiles')}")
    L10B = lo.get("L10B_DEEP_SYNTAX") or {}
    tr10b = L10B.get("transformation_result") or {}
    sum10b = tr10b.get("syntax_summary") or {}
    lines.append("")
    lines.append("L10B Deep Syntax:")
    lines.append(f"  node_count: {len(tr10b.get('dependency_nodes') or [])}")
    lines.append(f"  edge_count: {len(tr10b.get('dependency_edges') or [])}")
    conn_nodes = [n for n in (tr10b.get("dependency_nodes") or []) if n.get("connective_group")]
    if conn_nodes:
        lines.append(f"  connective_groups: {[(n.get('surface'), n.get('connective_group')) for n in conn_nodes[:15]]}")
    lines.append(f"  unresolved_tokens: {sum10b.get('unresolved_tokens')}")
    rel_labels = list({e.get("relation") for e in (tr10b.get("dependency_edges") or []) if e.get("relation")})
    lines.append(f"  relation_labels: {rel_labels[:15]}")
    L11B = lo.get("L11B_CAUSAL_I3RAB") or {}
    tr11b = L11B.get("transformation_result") or {}
    reasoning_list = tr11b.get("token_i3rab_reasoning") or []
    lines.append("")
    lines.append("L11B Causal I3rab:")
    for r in reasoning_list[:12]:
        lines.append(f"  {r.get('surface')} -> role={r.get('role')} factor={r.get('governing_factor')} conf={r.get('confidence')}")
    unresolved_11b = [r.get("surface") for r in reasoning_list if r.get("role_status") == "unresolved"]
    lines.append(f"  unresolved_tokens: {unresolved_11b[:15]}")
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    lines.append(f"  semantic_role_projection_coverage={proj.get('projection_coverage', 0)}")
    post_audit = pipeline.get("post_stage13_audit") or {}
    lines.append("")
    lines.append("Post-Stage-13 Fusion Audit:")
    lines.append(f"  fusion_consistency: {post_audit.get('fusion_consistency')}")
    lines.append(f"  issues_count: {len(post_audit.get('issues') or [])}")
    for i in (post_audit.get("issues") or [])[:5]:
        lines.append(f"    {i.get('code')} [{i.get('severity')}]")

    # Stage 11: profiling stage-by-stage timing
    if pipeline.get("profiling"):
        pf = pipeline["profiling"]
        lines.append("")
        lines.append("Profiling (elapsed_ms, status, warnings, errors):")
        for sid in STAGE_ORDER:
            s = (pf.get("per_stage") or {}).get(sid) or {}
            lines.append(f"  {sid}: {s.get('elapsed_ms')} ms | {s.get('status')} | w={s.get('warnings_count', 0)} e={s.get('errors_count', 0)}")
        lines.append(f"  total_time_ms: {pf.get('total_time_ms')}, slowest: {pf.get('slowest_stage_id')}")
    content = "\n".join(lines)
    return {
        "mode": "debug",
        "summary": f"Debug view. Validity: {fv.get('global_validity')}. Issues: {len(fv.get('issues') or [])}.",
        "sections": [_section("debug", "Debug", content)],
        "artifacts": {"stage_ids": list(lo.keys()), "evidence_trace": trace},
    }


def augment_rendered_output_with_profiling(pipeline: Dict[str, Any]) -> None:
    """Stage 11: When pipeline has profiling and rendered_output, add performance section to it."""
    if not pipeline.get("profiling") or not pipeline.get("rendered_output"):
        return
    ro = pipeline["rendered_output"]
    sections = ro.get("sections") or []
    pf = pipeline["profiling"]
    perf_lines = [
        f"Total time: {pf.get('total_time_ms')} ms",
        f"Stages run: {pf.get('stages_run_count')}, skipped: {pf.get('stages_skipped_count')}",
        f"Slowest stage: {pf.get('slowest_stage_id')} ({pf.get('slowest_stage_time_ms')} ms)",
    ]
    per_stage = pf.get("per_stage") or {}
    for sid in STAGE_ORDER:
        s = per_stage.get(sid) or {}
        perf_lines.append(f"  {sid}: {s.get('elapsed_ms')} ms | {s.get('status')} | w={s.get('warnings_count', 0)} e={s.get('errors_count', 0)}")
    sections.append(_section("performance_summary", "Performance Summary", "\n".join(perf_lines)))
    ro["sections"] = sections
    if ro.get("summary"):
        ro["summary"] = ro["summary"] + f" Total time: {pf.get('total_time_ms')} ms."


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
        super().__init__("L14_PRESENTATION", STAGE_NAMES["L14_PRESENTATION"], 19)

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
