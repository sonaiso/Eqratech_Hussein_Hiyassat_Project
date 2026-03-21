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


def extract_evidence_L8B(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L8B verb bab / governance: root type, bab, transitivity, required preposition, special class."""
    layer = lo.get("L8B_VERB_BAB_GOVERNANCE") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    entries: List[Dict[str, Any]] = []
    profiles = tr.get("verb_governance_profiles") or []
    summary = tr.get("governance_summary") or {}
    resolved = summary.get("resolved_profiles", 0)
    candidate = summary.get("candidate_profiles", 0)
    if st == "skipped":
        entries.append(explanation_entry(
            "Verb governance was skipped (no tokens).",
            "L8B_VERB_BAB_GOVERNANCE",
            ["status=skipped"],
            status="skipped",
        ))
        return entries
    excluded = summary.get("excluded_non_verbs", 0)
    ev = [f"verb_count={summary.get('verb_count', 0)}", f"resolved={resolved}", f"candidate={candidate}"]
    if excluded is not None and excluded > 0:
        ev.append(f"excluded_non_verbs={excluded}")
    claims: List[str] = []
    for p in profiles[:8]:
        root_type = p.get("root_type") or "unknown"
        trans = p.get("transitivity") or "unknown"
        gov = p.get("governance_family") or "unknown"
        objs = p.get("objects", 0)
        preps = p.get("required_prepositions") or []
        special = p.get("special_class")
        ev.append(f"{p.get('surface')}: root_type={root_type}, transitivity={trans}, objects={objs}, governance={gov}")
        if preps:
            ev.append(f"  required_prepositions={preps}")
        if special:
            ev.append(f"  special_class={special}")
        # Passive voice evidence
        voice_ev = p.get("voice_evidence") or {}
        voice = (voice_ev.get("voice") or "").strip()
        rule = (voice_ev.get("rule") or "").strip()
        conf = float(voice_ev.get("confidence") or 0)
        if voice == "passive" and rule and rule != "none":
            if rule == "sound_trilateral_passive":
                claims.append("Passive voice detected by rule sound_trilateral_passive.")
            elif rule == "hollow_passive":
                claims.append("Hollow passive pattern detected (root middle weak).")
            elif rule == "defective_passive":
                claims.append("Defective passive morphology inferred.")
            elif rule == "derived_passive":
                claims.append("Derived passive morphology inferred.")
            else:
                claims.append(f"Passive voice detected by rule {rule}.")
        elif voice == "passive" and conf < 0.5:
            claims.append("Passive voice candidate only — weak vowel evidence.")
        if p.get("expected_subject_role") == "نائب فاعل":
            ev.append("  expected_subject_role=نائب فاعل")
        bab_status = (p.get("bab_status") or "").strip()
        bab_val = (p.get("bab") or "").strip()
        tm = p.get("tense_mapping") or {}
        if bab_status == "resolved" and bab_val != "unknown":
            claims.append("Bab resolved from lexical bab knowledge base.")
        elif bab_status == "candidate":
            claims.append("Bab candidate inferred from surface/root pattern.")
        elif bab_val == "unknown":
            claims.append("Bab unresolved; no reliable lexical or pattern evidence.")
        if (tm.get("present_passive_pattern") or "").strip() and (tm.get("present_passive_pattern") or "").strip() != "unknown":
            claims.append("Present passive pattern estimated from root type and bab.")
        vc = (p.get("valency_class") or "").strip()
        if vc and vc != "unknown":
            claims.append("Verb valency class inferred from semantic valency seed knowledge.")
            ev.append(f"  valency_class={vc}, required_roles={p.get('valency_required_roles') or []}")
        if trans != "unknown" and gov != "unknown":
            if objs == 0 and "intransitive" in gov:
                claims.append("Verb governance profile: لازم (intransitive).")
            elif objs >= 1 and preps:
                claims.append("Verb governance profile: متعدي requiring preposition.")
            elif objs == 1:
                claims.append("Verb governance profile: transitive verb expecting one object.")
            elif objs == 2 and special == "أفعال القلوب":
                claims.append("Verb governance profile: mental verb (أفعال القلوب).")
            elif objs == 2 and special == "أفعال التحويل":
                claims.append("Verb governance profile: transformational verb (أفعال التحويل).")
    claim = " ".join(claims[:3]) if claims else "Verb governance profiles from L8B (root type, transitivity, governance family)."
    limitation_parts: List[str] = []
    if excluded and excluded > 0:
        limitation_parts.append("Tokens without strong verb evidence excluded from verb governance (verb-focused gating).")
    limitation_parts.append("Valency knowledge is seed-level and does not yet cover full Arabic verb semantics.")
    if resolved == 0 and candidate == 0 and profiles:
        limitation_parts.append("Bab unknown; governance from lexical knowledge base only.")
    elif resolved == 0 and not limitation_parts:
        limitation_parts.append("No resolved verb profiles; candidate or unresolved only.")
    limitation = " ".join(limitation_parts) if limitation_parts else None
    entries.append(explanation_entry(
        claim,
        "L8B_VERB_BAB_GOVERNANCE",
        ev[:12],
        confidence_hint="lexical KB + root type" if resolved else "candidate or unknown",
        limitation=limitation,
        status="supported" if resolved else ("limited" if candidate else "absent"),
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


def extract_evidence_L10B(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L10B deep syntax: dependency_nodes, dependency_edges, clause_units, attachments."""
    layer = lo.get("L10B_DEEP_SYNTAX") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    nodes = tr.get("dependency_nodes") or []
    edges = tr.get("dependency_edges") or []
    clause_units = tr.get("clause_units") or []
    summary = tr.get("syntax_summary") or {}
    entries: List[Dict[str, Any]] = []
    resolved = summary.get("resolved_edges", 0)
    candidate = summary.get("candidate_edges", 0)
    unresolved = summary.get("unresolved_tokens", len(nodes))
    main_clause = summary.get("main_clause_type") or "unknown"
    ev = [
        f"dependency_nodes={len(nodes)}",
        f"dependency_edges={len(edges)}",
        f"resolved_edges={resolved}",
        f"candidate_edges={candidate}",
        f"unresolved_tokens={unresolved}",
        f"main_clause_type={main_clause}",
        f"clause_units={len(clause_units)}",
    ]
    if summary.get("verb_governance_applied"):
        ev.append(f"governance_alignment_score={summary.get('governance_alignment_score', '—')}")
        for m in (summary.get("missing_arguments") or [])[:3]:
            ev.append(f"missing: {m}")
        for il in (summary.get("illegal_arguments") or [])[:3]:
            ev.append(f"illegal: {il}")
        for t in (tr.get("syntax_reasoning_trace") or [])[:5]:
            ev.append(f"trace: {t}")
    if summary.get("passive_alignment_used"):
        ev.append("passive_alignment_used=True")
    if summary.get("valency_alignment_used"):
        ev.append("valency_alignment_used=True")
    naib_edges = [e for e in edges if (e.get("relation") or "").strip() == "naib_fa'il"]
    if naib_edges:
        ev.append(f"naib_fa'il_edges={len(naib_edges)}")
    idafa_suppressed = [e for e in edges if e.get("idafa_suppression")]
    if idafa_suppressed:
        ev.append(f"weak_idafa_suppressed={len(idafa_suppressed)}")
    claims: List[str] = []
    if resolved > 0:
        claims.append("Resolved dependency relations from L10 isnadi and rule-based harf_jar/idafa.")
    if summary.get("passive_alignment_used"):
        claims.append("Passive frame from L8B used to prioritize نائب فاعل over active فاعل.")
    if summary.get("valency_alignment_used"):
        claims.append("Valency/governance expectation used as weak syntactic prior.")
    if idafa_suppressed:
        claims.append("Weak idafa candidate suppressed due to stronger verbal/passive structure.")
    if summary.get("verb_governance_applied"):
        claims.append("Verb governance rule applied: transitivity alignment.")
    if clause_units:
        types = [c.get("type") for c in clause_units if c.get("type")]
        if types:
            claims.append(f"Clause units: {', '.join(types)}.")
    if not edges and not clause_units:
        claims.append("No dependency edges or clause units produced.")
    claim = " ".join(claims) if claims else "Deep syntax: dependency nodes and edges from L10 + rules."
    entries.append(explanation_entry(
        claim,
        "L10B_DEEP_SYNTAX",
        ev,
        confidence_hint="rule-based dependency from L10/morphology" if resolved > 0 else "candidate only",
        limitation="Rule-constrained dependency inference with guarded relation generation.",
        status="supported" if resolved > 0 else "limited",
    ))
    return entries


def extract_evidence_connectives(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Connectives knowledge: report tokens recognized as conditional/adversative/negation/explanation from shared layer."""
    entries: List[Dict[str, Any]] = []
    # Prefer L10B nodes (they carry connective_group from shared layer)
    layer = lo.get("L10B_DEEP_SYNTAX") or {}
    tr = layer.get("transformation_result") or {}
    nodes = tr.get("dependency_nodes") or []
    by_group: Dict[str, List[str]] = {}
    for n in nodes:
        group = (n.get("connective_group") or "").strip()
        if not group:
            continue
        surface = (n.get("surface") or "").strip()
        if surface and group not in by_group:
            by_group[group] = []
        if surface and surface not in (by_group.get(group) or []):
            by_group.setdefault(group, []).append(surface)
    # Fallback: L4 words with connective_group
    if not by_group:
        l4 = lo.get("L4_OPERATORS") or {}
        words = (l4.get("transformation_result") or {}).get("words") or []
        for w in words:
            group = (w.get("connective_group") or "").strip()
            if not group:
                continue
            surface = (w.get("word") or "").strip()
            if surface:
                by_group.setdefault(group, []).append(surface)
    if not by_group:
        return entries
    group_claims = {
        "conditional": "Conditional connective recognized from shared connectives knowledge.",
        "negation": "Negation connective used as weak clause-level hint.",
        "explanation_causation": "Explanatory/causal connective recognized from shared knowledge base.",
        "adversative": "Adversative connective recognized from connectives layer.",
    }
    for group, tokens in by_group.items():
        claim = group_claims.get(group) or f"Connective group {group} recognized from shared connectives knowledge."
        ev = [f"group={group}", f"tokens={tokens[:10]}"]
        entries.append(explanation_entry(
            claim,
            "CONNECTIVES_KNOWLEDGE",
            ev,
            confidence_hint="lexical match from data/connectives_api",
            status="supported",
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


def extract_evidence_L11B(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L11B causal i3rab: structured role, governing factor, case/mood, reasoning. Reports parse_strength impact."""
    layer = lo.get("L11B_CAUSAL_I3RAB") or {}
    tr = layer.get("transformation_result") or {}
    reasoning = tr.get("token_i3rab_reasoning") or []
    summary = tr.get("i3rab_summary") or {}
    resolved = summary.get("resolved_tokens", 0)
    candidate = summary.get("candidate_tokens", 0)
    unresolved = summary.get("unresolved_tokens", len(reasoning))
    entries: List[Dict[str, Any]] = []
    ev = [
        f"resolved_tokens={resolved}",
        f"candidate_tokens={candidate}",
        f"unresolved_tokens={unresolved}",
    ]
    for r in reasoning[:5]:
        if r.get("role") and r.get("role") != "—":
            ev.append(f"{r.get('surface')}: role={r.get('role')} status={r.get('role_status')} gov={r.get('governing_factor')}")
    naib_count = sum(1 for r in reasoning if (r.get("role") or "").strip() == "نائب فاعل")
    if naib_count:
        ev.append(f"نائب فاعل assigned={naib_count}")
    weak_idafa_lim = [r for r in reasoning if r.get("limitations") and any("weak idafa suppressed" in (x or "") for x in r.get("limitations", []))]
    if weak_idafa_lim:
        ev.append("weak idafa suppressed in role prioritization")
    # L10B parse_strength: when low, L11B lowers confidence and prefers candidate
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    sum10b = (l10b.get("transformation_result") or {}).get("syntax_summary") or {}
    parse_strength = sum10b.get("parse_strength")
    if parse_strength is not None and float(parse_strength) < 0.35:
        ev.append("L10B parse_strength < 0.35: confidence reduced, prefer candidate over resolved.")
        limitation_extra = " Lowered confidence due to shallow deep-syntax parse."
    else:
        limitation_extra = ""
    claims: List[str] = []
    if resolved > 0:
        claims.append("Resolved grammatical roles from L10B/L11 and rule-based governing factors.")
    if naib_count:
        claims.append("Passive evidence used to assign نائب فاعل where L8B/L10B support it.")
    if weak_idafa_lim:
        claims.append("Weak idafa suppressed; نائب فاعل preferred over مضاف إليه when passive evidence exists.")
    if candidate > 0:
        claims.append("Candidate roles from nominal/idafa/object heuristics.")
    if not claims:
        claims.append("Structured causal i3rab: role and case reasoning from pipeline evidence.")
    claim = " ".join(claims)
    limitation = "Rule-constrained; first-scope roles only. No full Arabic i3rab coverage." + limitation_extra
    entries.append(explanation_entry(
        claim,
        "L11B_CAUSAL_I3RAB",
        ev,
        confidence_hint="causal i3rab from L10B + L11" if resolved else "candidate or text fallback only",
        limitation=limitation.strip(),
        status="supported" if resolved > 0 else "limited",
    ))
    return entries


def extract_evidence_semantic_roles(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """SEMANTIC_ROLE_PROJECTION: structural semantic projection from L8B/L10B/L11B. Hint only."""
    proj = lo.get("SEMANTIC_ROLE_PROJECTION") or {}
    roles = proj.get("semantic_roles") or []
    coverage = proj.get("projection_coverage") or 0.0
    entries: List[Dict[str, Any]] = []
    if not roles:
        return entries
    ev = [f"projection_coverage={coverage}", f"assigned_roles={len(roles)}"]
    for r in roles[:5]:
        ev.append(f"{r.get('surface')}: {r.get('semantic_role')} ({r.get('source', '')})")
    claims: List[str] = []
    patient_from_passive = [x for x in roles if x.get("semantic_role") == "PATIENT" and "passive" in (x.get("source") or "")]
    if patient_from_passive:
        claims.append("Semantic role projection: PATIENT inferred from passive syntactic structure.")
    pp_operator = [x for x in roles if "operator_catalog" in (x.get("source") or "")]
    if pp_operator:
        claims.append("Operator semantic hints from enriched operator catalog used for PP role projection.")
        goal_roles = [x for x in pp_operator if x.get("semantic_role") == "GOAL"]
        if goal_roles:
            claims.append("GOAL inferred from preposition (e.g. إلى or على) with governed PP structure.")
        source_roles = [x for x in pp_operator if x.get("semantic_role") == "SOURCE"]
        if source_roles:
            claims.append("SOURCE inferred from preposition من with structural support.")
        loc_roles = [x for x in pp_operator if x.get("semantic_role") == "LOCATION"]
        if loc_roles:
            claims.append("LOCATION inferred conservatively from في.")
    if not claims:
        claims.append("Semantic role projection applied from syntactic roles and valency (structural hint only).")
    entries.append(explanation_entry(
        " ".join(claims),
        "SEMANTIC_ROLE_PROJECTION",
        ev,
        confidence_hint="structural projection from L8B/L10B/L11B",
        limitation="Structural semantic projection only; not deep semantics or logical inference.",
        status="supported" if roles else "limited",
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


def extract_evidence_L12B(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L12B analogical reasoning: inferences and ambiguity resolutions. supported | limited."""
    layer = lo.get("L12B_ANALOGICAL_REASONING") or {}
    tr = layer.get("transformation_result") or {}
    st = layer.get("status", "missing")
    inferences = tr.get("analogical_inferences") or []
    resolutions = tr.get("ambiguity_resolutions") or []
    summary = tr.get("analogical_summary") or {}
    total = summary.get("total_inferences", len(inferences))
    entries: List[Dict[str, Any]] = []
    ev = [f"total_inferences={total}", f"ambiguity_resolutions={len(resolutions)}"]
    if inferences:
        for inf in inferences[:3]:
            rtype = inf.get("reasoning_type", "")
            ev.append(f"inference: {rtype} ({inf.get('status', '')})")
    if st == "skipped":
        entries.append(explanation_entry(
            "Analogical reasoning skipped (no tokens or gate).",
            "L12B_ANALOGICAL_REASONING",
            ev,
            status="skipped",
        ))
        return entries
    claim = "Analogical inference: pattern similarity and ambiguity resolution from L5–L12."
    if total > 0:
        claim = "Analogical inference: ism fa'il pattern similarity, syntactic role inference, or i3rab analogy."
    entries.append(explanation_entry(
        claim,
        "L12B_ANALOGICAL_REASONING",
        ev,
        confidence_hint="analogical similarity" if total else "no inference produced",
        limitation="Deterministic rules only; no ML or corpus lookup." if total else "No inference applied.",
        status="supported" if total > 0 else "limited",
    ))
    return entries


def extract_evidence_dependency_syntax(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """DEPENDENCY_SYNTAX_BUILDER: additive layer after L10B; dependency_links, root_resolution, ambiguity_log, candidate_markers."""
    ds = lo.get("DEPENDENCY_SYNTAX_BUILDER") or {}
    entries: List[Dict[str, Any]] = []
    if not ds:
        return entries
    links = ds.get("dependency_links") or []
    root_res = ds.get("root_resolution") or {}
    amb_log = ds.get("ambiguity_log") or []
    cand_mark = ds.get("candidate_markers") or []
    coverage = ds.get("coverage") or "—"
    ev = [
        f"coverage={coverage}",
        f"dependency_links={len(links)}",
        f"root_id={root_res.get('root_id')} root_form={root_res.get('root_form')}",
        f"ambiguity_log={len(amb_log)}",
        f"candidate_markers={len(cand_mark)}",
    ]
    if links:
        for L in links[:5]:
            ev.append(f"  {L.get('head_id')}→{L.get('dependent_id')} {L.get('relation')}")
    claim = "Dependency syntax builder (Stage 15): explicit dependency graph from L10B; root in root_resolution; canonical head→dependent directions."
    if amb_log:
        claim += " Ambiguities logged with ranked candidates (no silent collapse)."
    if cand_mark:
        claim += f" Candidate markers (TAMYIZ_CAND/HAL_CAND): {len(cand_mark)} passed to Stage 16."
    entries.append(explanation_entry(
        claim,
        "DEPENDENCY_SYNTAX_BUILDER",
        ev,
        confidence_hint="additive layer after L10B; does not mutate L10B",
        limitation="Quality depends on L10B/L8B upstream; clause-first and root priority applied (Pass E).",
        status="supported" if links or root_res.get("root_id") is not None else "limited",
    ))
    return entries


def extract_evidence_discourse_frames(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """DISCOURSE_FRAME_BUILDER: frames from connectives + L10B clause + L12/L12B. Evidence quality reflected."""
    df = lo.get("DISCOURSE_FRAME_BUILDER") or {}
    frames = df.get("frames") or []
    entries: List[Dict[str, Any]] = []
    if not frames:
        return entries
    ev = [
        f"frame_count={df.get('frame_count', 0)}",
        f"strong_frame_count={df.get('strong_frame_count', 0)}",
        f"weak_frame_count={df.get('weak_frame_count', 0)}",
    ]
    for f in frames[:5]:
        trigger = f.get("trigger", "")
        ft = f.get("frame_type", "")
        conf = f.get("confidence", "")
        scope = f.get("scope_hint", "")
        lim = f.get("limitation") or ""
        ev.append(f"{trigger}: {ft} ({conf}, {scope})" + (f" — {lim}" if lim else ""))
    claims: List[str] = []
    strong_conditional = [x for x in frames if x.get("frame_type") == "conditional" and x.get("confidence") == "strong"]
    if strong_conditional:
        claims.append("Conditional discourse frame supported by connective recognition and clause structure.")
    weak_conditional = [x for x in frames if x.get("frame_type") == "conditional" and x.get("confidence") == "weak"]
    if weak_conditional:
        claims.append("Conditional discourse frame inferred from connective recognition only.")
    adversative_weak = [x for x in frames if x.get("frame_type") == "adversative" and x.get("confidence") == "weak"]
    if adversative_weak:
        claims.append("Adversative discourse frame inferred from connective recognition only.")
    explanation_frames = [x for x in frames if x.get("frame_type") == "explanation"]
    if explanation_frames and any(x.get("limitation") for x in explanation_frames):
        claims.append("Explanation frame kept conservative; causation not fully disambiguated.")
    suppressed = [x for x in frames if x.get("limitation") and "suppressed" in (x.get("limitation") or "")]
    if suppressed:
        claims.append("Weak discourse frame suppressed due to lack of structural support.")
    if not claims:
        claims.append("Discourse frames built from connectives and L10B/L12B; token vs clause support reflected.")
    entries.append(explanation_entry(
        " ".join(claims),
        "DISCOURSE_FRAME_BUILDER",
        ev,
        confidence_hint="connective + clause/discourse alignment",
        limitation="Additive layer only; does not override syntax or i'rab.",
        status="supported" if frames else "limited",
    ))
    return entries


def extract_evidence_L13_verb_transformation(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L13 verb transformation: generated paradigm from L8B tense_mapping + root."""
    layer = lo.get("L13_VERB_TRANSFORMATION") or {}
    tr = layer.get("transformation_result") or {}
    rows = tr.get("verb_transformations") or []
    summary = tr.get("transformation_summary") or {}
    ev = [
        f"total_verbs={summary.get('total_verbs', len(rows))}",
        f"fully_transformed={summary.get('fully_transformed', 0)}",
        f"partially_transformed={summary.get('partially_transformed', 0)}",
    ]
    for row in rows[:5]:
        ev.append(
            f"{row.get('surface', '—')}: past={row.get('base_past_active') or '—'} "
            f"present={row.get('base_present_active') or '—'} masdar={row.get('masdar') or '—'} "
            f"imperative={row.get('imperative') or '—'}"
        )
    return [explanation_entry(
        "Verb transformation engine generated conservative base paradigms from L8B tense mapping and root evidence.",
        "L13_VERB_TRANSFORMATION",
        ev,
        confidence_hint="resolved bab/root yields stronger paradigm coverage",
        limitation="Pass 1 only; quadrilateral and weak-root handling remains conservative.",
        status="supported" if rows else "limited",
    )]


def extract_evidence_L13_cognitive_fusion(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L13 Cognitive Fusion: dominant source per token, conflict resolved, ambiguity remaining."""
    layer = lo.get("L13_COGNITIVE_FUSION") or {}
    tr = layer.get("transformation_result") or {}
    token_states = tr.get("token_states") or []
    fusion_mode = tr.get("fusion_mode") or "normal"
    global_conf = tr.get("global_confidence")
    entries: List[Dict[str, Any]] = []
    ev = [f"fusion_mode={fusion_mode}", f"token_states_count={len(token_states)}"]
    if global_conf is not None:
        ev.append(f"global_confidence={global_conf}")
    dominant_sources: List[str] = []
    for ts in token_states[:5]:
        stack = ts.get("evidence_stack") or []
        if stack:
            top = max(stack, key=lambda x: x.get("weight") or 0)
            dominant_sources.append(f"{ts.get('token', '')}->{top.get('source', '')}")
    if dominant_sources:
        ev.extend(dominant_sources)
    conflicts = [c for ts in token_states for c in (ts.get("conflicts_resolved") or [])]
    ambiguities = [a for ts in token_states for a in (ts.get("ambiguities_remaining") or [])]
    if conflicts:
        ev.append(f"conflicts_resolved={len(conflicts)}")
    if ambiguities:
        ev.append(f"ambiguities_remaining={len(ambiguities)}")
    entries.append(explanation_entry(
        "Cognitive fusion: hierarchical evidence arbitration; dominant source per token.",
        "L13_COGNITIVE_FUSION",
        ev,
        confidence_hint="fusion_mode=" + fusion_mode,
        limitation="Arbitration only; no invention. Syntax depth limits role resolution.",
        status="supported" if token_states else "limited",
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
    trace.extend(extract_evidence_L8B(lo))
    trace.extend(extract_evidence_L9(lo))
    trace.extend(extract_evidence_L10(lo))
    trace.extend(extract_evidence_L10B(lo))
    trace.extend(extract_evidence_dependency_syntax(lo))
    trace.extend(extract_evidence_connectives(lo))
    trace.extend(extract_evidence_L11(lo))
    trace.extend(extract_evidence_L11B(lo))
    trace.extend(extract_evidence_semantic_roles(lo))
    trace.extend(extract_evidence_L12(lo))
    trace.extend(extract_evidence_L12B(lo))
    trace.extend(extract_evidence_discourse_frames(lo))
    trace.extend(extract_evidence_L13_verb_transformation(lo))
    trace.extend(extract_evidence_L13_cognitive_fusion(lo))
    trace.extend(extract_evidence_L13(lo, fv))
    return trace
