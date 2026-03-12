# -*- coding: utf-8 -*-
"""
Explainability and evidence rendering — Stage 8.

Extracts evidence from pipeline outputs only. No new analysis.
Model: claim, supporting_stage, evidence, confidence_hint, limitation, status.
"""

from __future__ import annotations

from typing import Any, Dict, List


def explanation_entry(
    claim: str,
    supporting_stage: str,
    evidence: List[str],
    *,
    confidence_hint: str | None = None,
    limitation: str | None = None,
    status: str = "supported",
) -> Dict[str, Any]:
    """Build one explainability entry. status: supported | limited | absent | skipped."""
    out: Dict[str, Any] = {
        "claim": claim,
        "supporting_stage": supporting_stage,
        "evidence": evidence,
        "status": status,
    }
    if confidence_hint is not None:
        out["confidence_hint"] = confidence_hint
    if limitation is not None:
        out["limitation"] = limitation
    return out


def extract_evidence_L4(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L4_OPERATORS: words with operator flag; operator_count. If absent, say absent."""
    layer = lo.get("L4_OPERATORS") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    words = tr.get("words") or []
    op_count = tr.get("operator_count", sum(1 for w in words if isinstance(w, dict) and w.get("operator")))
    if not words:
        entries.append(explanation_entry(
            "No words from operators stage.",
            "L4_OPERATORS",
            ["words_count=0"],
            status="absent",
        ))
        return entries
    ev = [f"operator_count={op_count}", f"words_count={len(words)}"]
    for w in words[:5]:
        if isinstance(w, dict) and w.get("operator"):
            ev.append(f"matched operator token={w.get('word', '')}")
    entries.append(explanation_entry(
        "Operator detection from L4 (c2b kind=operator)." if op_count else "No operator tokens; L4 word list from c2b.",
        "L4_OPERATORS",
        ev,
        confidence_hint="direct lexical match" if op_count else "no operator match",
        status="supported" if op_count else "limited",
    ))
    return entries


def extract_evidence_L5(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L5_WORD_TYPING: word type/kind per token."""
    layer = lo.get("L5_WORD_TYPING") or {}
    tr = layer.get("transformation_result") or {}
    words = tr.get("words") or []
    entries: List[Dict[str, Any]] = []
    if not words:
        entries.append(explanation_entry(
            "Word typing: no words in output.",
            "L5_WORD_TYPING",
            ["words_count=0"],
            status="absent",
        ))
        return entries
    ev = [f"words_count={len(words)}"]
    for w in words[:5]:
        ev.append(f"{w.get('word', '')}: kind={w.get('kind', '')}")
    entries.append(explanation_entry(
        "Word typing (kind) from morphology.",
        "L5_WORD_TYPING",
        ev,
        confidence_hint="from c2b word analysis",
        status="supported",
    ))
    return entries


def extract_evidence_L6_L7(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L6 phonology, L7 syllables: CV pattern, gates, syllable count."""
    entries: List[Dict[str, Any]] = []
    L6 = lo.get("L6_PHONOLOGY") or {}
    tr6 = L6.get("transformation_result") or {}
    st6 = L6.get("status", "missing")
    ev6 = [f"status={st6}", f"num_units={tr6.get('num_units')}", f"gates_count={tr6.get('gates_count')}"]
    entries.append(explanation_entry(
        "Phonology (CV, units) from L6.",
        "L6_PHONOLOGY",
        ev6,
        confidence_hint="phonology_v2 adapter" if st6 == "success" else "limited",
        limitation=None if st6 == "success" else "Phonology may be partial or skipped.",
        status="supported" if st6 == "success" else "limited",
    ))
    L7 = lo.get("L7_SYLLABIFICATION") or {}
    tr7 = L7.get("transformation_result") or {}
    st7 = L7.get("status", "missing")
    ev7 = [f"status={st7}", f"count={tr7.get('count')}"]
    entries.append(explanation_entry(
        "Syllable count from L7.",
        "L7_SYLLABIFICATION",
        ev7,
        confidence_hint="syllabifier output" if st7 == "success" else "limited",
        status="supported" if st7 == "success" else "limited",
    ))
    return entries


def extract_evidence_L8(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L8 root extraction: root candidates; if skipped, explain gate."""
    layer = lo.get("L8_ROOT_EXTRACTION") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    if st == "skipped":
        gates = layer.get("gates_applied") or []
        ev = [f"status={st}"] + [g.get("gate", str(g)) for g in gates if isinstance(g, dict)][:3]
        entries.append(explanation_entry(
            "Root extraction was skipped (no morphology candidate or ineligible input).",
            "L8_ROOT_EXTRACTION",
            ev,
            limitation="Gate: has_morphology_candidate or has_root_candidate false.",
            status="skipped",
        ))
        return entries
    words = tr.get("words") or []
    if not words:
        entries.append(explanation_entry(
            "Root extraction produced no words.",
            "L8_ROOT_EXTRACTION",
            ["words_count=0"],
            status="absent",
        ))
        return entries
    ev = [f"words_count={len(words)}"]
    roots_found = 0
    for w in words[:10]:
        r = w.get("root")
        if r:
            roots_found += 1
            ev.append(f"{w.get('word')}: root={r}")
    entries.append(explanation_entry(
        "Root(s) extracted from L8 (resolver/pattern).",
        "L8_ROOT_EXTRACTION",
        ev[:8],
        confidence_hint="resolver + wazn/heuristic" if roots_found else "roots absent for content words",
        limitation=None if roots_found else "No roots extracted; may be particle/mabni or unresolved.",
        status="supported" if roots_found else "limited",
    ))
    return entries


def extract_evidence_L9(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L9 wazn matching: template/word_wazn; if skipped, explain gate."""
    layer = lo.get("L9_WAZN_MATCHING") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    if st == "skipped":
        gates = layer.get("gates_applied") or []
        ev = [f"status={st}"] + [g.get("gate", str(g)) for g in gates if isinstance(g, dict)][:3]
        entries.append(explanation_entry(
            "Wazn matching was skipped (no root candidate).",
            "L9_WAZN_MATCHING",
            ev,
            limitation="Gate: has_root_candidate false; wazn requires root.",
            status="skipped",
        ))
        return entries
    words = tr.get("words") or []
    if not words:
        entries.append(explanation_entry(
            "Wazn matching produced no words.",
            "L9_WAZN_MATCHING",
            ["words_count=0"],
            status="absent",
        ))
        return entries
    ev = [f"words_count={len(words)}"]
    for w in words[:5]:
        tpl = w.get("template") or w.get("word_wazn") or "—"
        ev.append(f"{w.get('word')}: template={tpl}")
    entries.append(explanation_entry(
        "Wazn/template from L9 (pattern match).",
        "L9_WAZN_MATCHING",
        ev,
        confidence_hint="awzan pattern match",
        status="supported",
    ))
    return entries


def extract_evidence_L10(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L10 syntax: word_forms, links. Honest about shallow depth."""
    layer = lo.get("L10_SYNTAX") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    if st == "failed":
        err = tr.get("error") or (layer.get("errors") or [None])[0]
        entries.append(explanation_entry(
            "Syntax stage failed.",
            "L10_SYNTAX",
            [f"status={st}", f"error={err}"],
            limitation="Syntax analysis unavailable.",
            status="skipped",
        ))
        return entries
    wf = tr.get("word_forms") or []
    links = (tr.get("links") or {}).get("isnadi") or []
    ev = [f"word_forms_count={len(wf)}", f"isnadi_links={len(links)}"]
    entries.append(explanation_entry(
        "Syntax: word forms and isnadi links from L10.",
        "L10_SYNTAX",
        ev,
        confidence_hint="syntax adapter" if st == "success" else "partial",
        limitation="Syntax depth may be shallow; full dependency parse not guaranteed.",
        status="supported" if st == "success" else "limited",
    ))
    return entries


def extract_evidence_L11(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L11 i3rab: token_results, i3rab_text. Evidence from current c2e payload."""
    layer = lo.get("L11_I3RAB") or {}
    tr = layer.get("transformation_result") or {}
    token_results = tr.get("token_results") or []
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    if not token_results:
        entries.append(explanation_entry(
            "I3rab: no token results.",
            "L11_I3RAB",
            ["token_results_count=0"],
            status="absent",
        ))
        return entries
    ev = [f"token_results_count={len(token_results)}"]
    with_text = 0
    for t in token_results[:5]:
        surface = t.get("surface") or t.get("word", "")
        it = t.get("i3rab_text") or ""
        if it:
            with_text += 1
        ev.append(f"{surface}: i3rab_text={'present' if it else 'absent'}")
    entries.append(explanation_entry(
        "I3rab per token from L11 (c2e i3rab_text).",
        "L11_I3RAB",
        ev,
        confidence_hint="current c2e i3rab text payload; rule-based.",
        limitation="I3rab evidence is text-based; no deep syntactic case reasoning.",
        status="supported" if with_text else "limited",
    ))
    return entries


def extract_evidence_L12(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L12 semantic/rhetorical: sentence_type, rhetoric_signals. Honest about limited depth."""
    layer = lo.get("L12_SEMANTIC_RHETORICAL") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    sentence_type = tr.get("sentence_type") or "—"
    rhetoric = tr.get("rhetoric_signals") or []
    entries: List[Dict[str, Any]] = []
    ev = [f"sentence_type={sentence_type}", f"rhetoric_signals_count={len(rhetoric)}"]
    entries.append(explanation_entry(
        "Sentence type and rhetoric signals from L12.",
        "L12_SEMANTIC_RHETORICAL",
        ev,
        confidence_hint="c2d + rhetoric extractor" if st == "success" else "partial",
        limitation="Rhetoric detection is surface/syntax-assisted; deep semantic rhetoric not implemented.",
        status="supported" if (sentence_type and sentence_type != "—") or rhetoric else "limited",
    ))
    return entries


def extract_evidence_L13(lo: Dict[str, Any], fv: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L13 validation: global_validity, issues, final_confidence. Why validity has its value."""
    issues = fv.get("issues") or []
    validity = fv.get("global_validity") or "unknown"
    confidence = fv.get("final_confidence")
    entries: List[Dict[str, Any]] = []
    ev = [f"global_validity={validity}", f"issue_count={len(issues)}"]
    if confidence is not None:
        ev.append(f"final_confidence={confidence}")
    for i in issues[:5]:
        ev.append(f"{i.get('code')} [{i.get('severity')}] {i.get('layer_id')}")
    reason = "No issues; all key stages consistent." if not issues else f"{len(issues)} issue(s) from L13 checks."
    entries.append(explanation_entry(
        f"Validation: {validity}. {reason}",
        "L13_VALIDATION",
        ev,
        confidence_hint="cross-layer consistency checks",
        limitation=None if validity == "valid" else "Issues or weak evidence reduced validity.",
        status="supported" if validity == "valid" else "limited",
    ))
    return entries


def build_evidence_trace(pipeline: Dict[str, Any]) -> List[Dict[str, Any]]:
    """
    Build full evidence trace from pipeline. Uses layer_outputs and final_validation only.
    Returns list of explanation entries (claim, supporting_stage, evidence, ...).
    """
    lo = pipeline.get("layer_outputs") or {}
    fv = pipeline.get("final_validation") or {}
    trace: List[Dict[str, Any]] = []
    trace.extend(extract_evidence_L4(lo))
    trace.extend(extract_evidence_L5(lo))
    trace.extend(extract_evidence_L6_L7(lo))
    trace.extend(extract_evidence_L8(lo))
    trace.extend(extract_evidence_L9(lo))
    trace.extend(extract_evidence_L10(lo))
    trace.extend(extract_evidence_L11(lo))
    trace.extend(extract_evidence_L12(lo))
    trace.extend(extract_evidence_L13(lo, fv))
    return trace
