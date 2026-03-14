# -*- coding: utf-8 -*-
"""
L10B — Deep Dependency Syntax Engine.

Builds a dependency-oriented representation from L2, L4, L5, L8, L9, L10 only.
Does NOT re-run raw analyzers. Does NOT invent tokens or overwrite upstream.
Deterministic, rule-based; marks uncertain relations as candidate.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from .builders import build_layer_output, get_previous_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict
from .verb_governance import infer_expected_arguments, load_verb_governance

# Confidence bands (never 1.0; never 0.0 for existing relations)
CONF_STRONG = 0.90
CONF_GOOD = 0.75
CONF_CANDIDATE = 0.55
CONF_WEAK = 0.30

# Relation label set (stable, documented)
REL_FAIL = "fa'il"
REL_NAIB_FAIL = "naib_fa'il"
REL_MAFUL_BIH = "maf'ul_bih"
REL_MUBTADA = "mubtada"
REL_KHABAR = "khabar"
REL_NAAT = "naat"
REL_IDAFA = "idafa"
REL_HARF_JAR = "harf_jar"
REL_MAJRUR = "majrur"
REL_ZARF = "zarf"
REL_JAR_MAJRUR_ATTACHMENT = "jar_majrur_attachment"
REL_HAL_CANDIDATE = "hal_candidate"
REL_SHART_MARKER = "shart_marker"
REL_JAWAB_SHART_CANDIDATE = "jawab_shart_candidate"
REL_SILA_CANDIDATE = "sila_candidate"
REL_ATF_CANDIDATE = "atf_candidate"
REL_UNKNOWN = "unknown"

# Strict harf jar: majrur ONLY when token.kind==operator AND surface (normalized) in this set
HARF_JAR_SET = frozenset({
    "مِن", "إِلَى", "عَنْ", "عَلَى", "فِي",
    "رُبَّ", "بِ", "كَ", "لِ", "حَتَّى",
})
# Normalized (strip diacritics) for matching
_HARF_JAR_NORMALIZED = frozenset({"من", "الى", "عن", "على", "في", "رب", "ب", "ك", "ل", "حتى"})

# Conditional markers: if operator and surface in set → main_clause_type = conditional
SHART_MARKERS = frozenset({"لَو", "إِن", "إِذَا", "لَمَّا"})
_SHART_MARKERS_NORMALIZED = frozenset({"لو", "ان", "اذا", "لما"})


def _normalize_surface(s: str) -> str:
    """Strip Arabic diacritics for relation matching. Does not change letter order."""
    if not s:
        return ""
    # Remove combining tashkeel (064B-0652, 0670)
    result = []
    for c in s:
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _get_tokens(pipeline: PipelineDict) -> List[str]:
    """Token list from L2 or L5."""
    lo = pipeline.get("layer_outputs") or {}
    tr2 = (lo.get("L2_TOKENIZATION") or {}).get("transformation_result") or {}
    tokens = tr2.get("tokens") or []
    if tokens:
        return [t.get("word") or "" for t in tokens if t.get("word")]
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    words = tr5.get("words") or []
    return [w.get("word") or "" for w in words if w.get("word")]


def _l10_structures(lo: Dict[str, Any]) -> Tuple[List[Dict], List[Dict]]:
    """Return (word_forms, isnadi_links) from L10."""
    tr10 = (lo.get("L10_SYNTAX") or {}).get("transformation_result") or {}
    wf = tr10.get("word_forms") or []
    links = (tr10.get("links") or {}).get("isnadi") or []
    return wf, links


def _is_operator_token(surface: str, op_words: List[Dict]) -> bool:
    """True iff L4 marks this token as operator."""
    return any((x.get("word") or "").strip() == (surface or "").strip() and x.get("operator") for x in op_words)


def _token_in_normalized_set(surface: str, normalized_set: frozenset) -> bool:
    """True iff normalized surface is in set (for harf jar / shart)."""
    return _normalize_surface(surface or "") in normalized_set


def _pos_hint(token: str, words5: List[Dict], words8: List[Dict], words9: List[Dict], op_words: List[Dict]) -> str:
    """POS hint from L5/L8/L9/L4."""
    w5 = next((x for x in words5 if (x.get("word") or "") == token), None)
    if w5 and (w5.get("kind") or "").strip():
        return (w5.get("kind") or "").strip().lower()
    if any((x.get("word") or "") == token and x.get("operator") for x in op_words):
        return "particle"
    w9 = next((x for x in words9 if (x.get("word") or "") == token), None)
    if w9 and (w9.get("template") or w9.get("word_wazn") or ""):
        tpl = (w9.get("template") or w9.get("word_wazn") or "").strip()
        if "فعل" in tpl or "فَعَلَ" in tpl or "أفعال" in tpl:
            return "verb"
        if "فاعل" in tpl or "مفعول" in tpl or "اسم" in tpl:
            return "noun"
    return ""


def _is_finite_verb_wazn(template: str) -> bool:
    """True if wazn suggests finite verb (فعل/فعل/يفعل), not participle or masdar."""
    if not template:
        return False
    t = (template or "").strip()
    # Finite: فَعَلَ, فُعِلَ, يَفْعَلُ, تَفْعَلُ, أَفْعَلُ, etc.
    if "فعل" in t or "يفعل" in t or "تفعل" in t or "أفعل" in t or "نفعل" in t:
        # Exclude participle patterns
        if "فاعل" in t or "مفعول" in t or "مفعل" in t or "فعلة" in t or "فعال" in t:
            return False
        return True
    return False


def _second_noun_definite_or_possessive(surface: str) -> bool:
    """Heuristic: second token in idafa is often definite (ال) or has possessive suffix."""
    if not surface or not isinstance(surface, str):
        return False
    s = (surface or "").strip()
    if s.startswith("ال"):
        return True
    # Common possessive suffixes (simplified)
    for suf in ("ي", "ك", "ه", "ها", "نا", "كم", "هم", "هن"):
        if s.endswith(suf) and len(s) > len(suf):
            return True
    return False


def _is_verbish(pos_hint: str, words9: List[Dict], token: str) -> bool:
    """True if token is verb or operator or participle with active verbal role (ism fa'il etc)."""
    if (pos_hint or "").lower() in ("verb", "فعل"):
        return True
    if (pos_hint or "").lower() in ("particle", "operator"):
        return True
    w9 = next((x for x in words9 if (x.get("word") or "").strip() == (token or "").strip()), None)
    if w9:
        tpl = (w9.get("template") or w9.get("word_wazn") or "").strip()
        if "فاعل" in tpl or "مفعول" in tpl:
            return True  # participle treated as verbish for idafa suppression
    return False


def _map_l10_link_to_relation(link: Dict) -> str:
    """Map L10 isnadi link type to our relation label."""
    type_en = (link.get("type_en") or link.get("type") or "").strip()
    if not type_en:
        return REL_UNKNOWN
    type_lower = type_en.lower()
    if "subject" in type_lower or "fa'il" in type_lower or "فاعل" in type_lower:
        return REL_FAIL
    if "object" in type_lower or "maf'ul" in type_lower or "مفعول" in type_lower:
        return REL_MAFUL_BIH
    if "mubtada" in type_lower or "khabar" in type_lower or "مبتدأ" in type_lower or "خبر" in type_lower:
        if "khabar" in type_lower or "خبر" in type_lower:
            return REL_KHABAR
        return REL_MUBTADA
    if "isnadi" in type_lower or "إسنادي" in type_lower:
        return REL_MUBTADA  # generic isnadi as nominal head
    return REL_UNKNOWN


def _l8b_profile_by_token_index(tokens: List[str], lo: Dict[str, Any]) -> Dict[int, Dict[str, Any]]:
    """Build token_index -> L8B verb governance profile. Aligns by surface. Used for passive/valency/idafa logic."""
    out: Dict[int, Dict[str, Any]] = {}
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    for i, surface in enumerate(tokens):
        word = (surface or "").strip()
        if not word:
            continue
        for p in profiles:
            if (p.get("surface") or "").strip() == word:
                out[i] = p
                break
    return out


def _run_verb_governance_pass(
    tokens: List[str],
    lo: Dict[str, Any],
    nodes: List[Dict],
    edges: List[Dict],
    syntax_summary: Dict[str, Any],
    base_parse_strength: float,
) -> Tuple[Dict[str, Any], List[str]]:
    """
    L10B-V: Apply verb governance rules. Compute alignment, penalties, boost candidate objects,
    extend syntax_summary and return syntax_reasoning_trace.
    """
    trace: List[str] = []
    gov = load_verb_governance()
    if not gov:
        out = {**syntax_summary, "verb_governance_applied": False, "governance_alignment_score": 0.0, "missing_arguments": [], "illegal_arguments": []}
        return out, trace

    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    words8 = tr8.get("words") or []
    words9 = tr9.get("words") or []
    op_words = tr4.get("words") or []

    l8b_map = _l8b_profile_by_token_index(tokens, lo)

    def root_for_token(surface: str) -> Optional[str]:
        for w in words8:
            if (w.get("word") or "").strip() == (surface or "").strip():
                r = w.get("root")
                if isinstance(r, dict):
                    r = r.get("formatted") or (("-".join(r["letters"]) if r.get("letters") else None))
                return (r or "").strip() or None
        return None

    def template_for_token(surface: str) -> str:
        for w in words9:
            if (w.get("word") or "").strip() == (surface or "").strip():
                return (w.get("template") or w.get("word_wazn") or "").strip()
        return ""

    missing_arguments: List[str] = []
    illegal_arguments: List[str] = []
    alignment_scores: List[float] = []
    conflict_penalty = 0.0

    for i, surface in enumerate(tokens):
        word = (surface or "").strip()
        root = root_for_token(word)
        template = template_for_token(word)
        if not _is_finite_verb_wazn(template) or not root:
            continue
        verb_id = str(i)
        verb_node = {"lemma": root, "token_id": verb_id, "surface": word}
        expected = infer_expected_arguments(verb_node)
        exp_objects = expected.get("expected_objects") or 0
        exp_pp = expected.get("expected_pp_relations") or []

        # L8B valency prior: reinforce expected objects from valency_class when present
        profile = l8b_map.get(i)
        if profile:
            vc = (profile.get("valency_class") or "").strip()
            if vc == "intransitive":
                exp_objects = 0
            elif vc == "transitive_one_object":
                exp_objects = max(exp_objects, 1)

        actual_subj = sum(1 for e in edges if e.get("from_id") == verb_id and e.get("relation") == REL_FAIL)
        actual_naib = sum(1 for e in edges if e.get("from_id") == verb_id and e.get("relation") == REL_NAIB_FAIL)
        actual_obj = sum(1 for e in edges if e.get("from_id") == verb_id and e.get("relation") == REL_MAFUL_BIH)
        has_required_pp = True
        if exp_pp:
            exp_pp_norm = [ _normalize_surface(p) for p in exp_pp ]
            has_required_pp = any(
                _normalize_surface(tokens[j]) in exp_pp_norm
                for j in range(len(tokens))
                if _is_operator_token((tokens[j] or "").strip(), op_words)
            )

        score = 1.0
        if exp_objects == 0 and actual_obj > 0:
            illegal_arguments.append(f"direct object (verb '{root}' intransitive)")
            conflict_penalty += 0.25
            score -= 0.3
            trace.append("Verb governance rule applied: intransitive verb has direct object — anomaly")
        elif exp_objects > 0 and actual_obj < exp_objects:
            for _ in range(exp_objects - actual_obj):
                missing_arguments.append(f"object (verb '{root}' expects {exp_objects})")
            score -= 0.1 * (exp_objects - actual_obj)
        if exp_pp and not has_required_pp:
            missing_arguments.append(f"PP({exp_pp[0]}) for verb '{root}'")
            score -= 0.2
            trace.append("Verb governance rule applied: missing required preposition")
        if exp_pp and has_required_pp:
            score = min(1.0, score + 0.15)
            trace.append("Verb governance rule applied: transitivity alignment")
        if exp_objects > 0 and actual_obj >= exp_objects and not illegal_arguments:
            trace.append("Verb governance rule applied: transitivity alignment")
        if profile and (profile.get("voice") or "").strip() == "passive" and actual_naib >= 1:
            trace.append("Passive verb: نائب فاعل alignment used.")
        alignment_scores.append(max(0.0, min(1.0, score)))

        # Promote candidate object -> probable when verb expects object
        if exp_objects >= 1:
            for e in edges:
                if e.get("from_id") == verb_id and e.get("relation") == REL_MAFUL_BIH and e.get("status") == "candidate":
                    e["status"] = "probable"
                    trace.append("Verb governance rule applied: promoted candidate object to probable")

    applied = len(alignment_scores) > 0
    governance_alignment_score = round(sum(alignment_scores) / len(alignment_scores), 3) if alignment_scores else 0.0
    structural_conflict_penalty = min(0.5, conflict_penalty)
    if applied:
        parse_strength = max(0.0, min(1.0, base_parse_strength + governance_alignment_score - structural_conflict_penalty))
    else:
        parse_strength = base_parse_strength

    # Tightening pass: optional summary flags for downstream/explainability
    passive_alignment_used = any(e.get("relation") == REL_NAIB_FAIL for e in edges)
    valency_alignment_used = applied

    out = {
        **syntax_summary,
        "verb_governance_applied": applied,
        "governance_alignment_score": governance_alignment_score,
        "structural_conflict_penalty": structural_conflict_penalty,
        "missing_arguments": missing_arguments,
        "illegal_arguments": illegal_arguments,
        "parse_strength": round(parse_strength, 3),
        "passive_alignment_used": passive_alignment_used,
        "valency_alignment_used": valency_alignment_used,
    }
    return out, trace


def _build_dependency_structure(
    tokens: List[str],
    lo: Dict[str, Any],
) -> Tuple[List[Dict], List[Dict], List[Dict], List[Dict], Dict[str, Any], List[str]]:
    """
    Build dependency_nodes, dependency_edges, clause_units, attachments, syntax_summary, syntax_reasoning_trace.
    Uses only L2, L4, L5, L8, L9, L10; no raw parsing.
    """
    nodes: List[Dict[str, Any]] = []
    edges: List[Dict[str, Any]] = []
    clause_units: List[Dict[str, Any]] = []
    attachments: List[Dict[str, Any]] = []

    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    tr8 = (lo.get("L8_ROOT_EXTRACTION") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    words5 = tr5.get("words") or []
    words8 = tr8.get("words") or []
    words9 = tr9.get("words") or []
    op_words = tr4.get("words") or []

    word_forms, isnadi_links = _l10_structures(lo)

    # 1) Create one node per token
    for i, surface in enumerate(tokens):
        tid = str(i)
        pos_hint = _pos_hint(surface, words5, words8, words9, op_words)
        nodes.append({
            "token_id": tid,
            "surface": surface,
            "pos_hint": pos_hint or "unknown",
            "head_id": None,
            "relation": None,
            "confidence": None,
            "status": "unresolved",
        })

    # 1b) Optional: enrich nodes with connective hints from shared connectives layer
    try:
        from .connectives import classify_connective
        for n in nodes:
            surface = n.get("surface") or ""
            c = classify_connective(surface)
            if c:
                n["connective_group"] = c.get("group")
                n["connective_hint"] = c.get("category_name") or c.get("group")
    except Exception:
        pass

    if not tokens:
        summary = {
            "resolved_edges": 0,
            "candidate_edges": 0,
            "unresolved_tokens": 0,
            "main_clause_type": "unknown",
            "parse_strength": 0.0,
            "advisory_notes": [],
            "verb_governance_applied": False,
            "governance_alignment_score": 0.0,
            "missing_arguments": [],
            "illegal_arguments": [],
        }
        return nodes, edges, clause_units, attachments, summary, []

    # L8B profile map for passive/valency/idafa (tightening pass)
    l8b_map = _l8b_profile_by_token_index(tokens, lo)

    # 2) Map L10 isnadi links to edges (passive-aware: subject after passive verb -> naib_fa'il)
    for link in isnadi_links:
        head = link.get("head") or {}
        dep = link.get("dependent") or {}
        head_id = head.get("id")
        dep_id = dep.get("id")
        if head_id is None or dep_id is None:
            continue
        head_id_str = str(head_id)
        dep_id_str = str(dep_id)
        conf = link.get("confidence")
        if conf is not None:
            conf = max(CONF_WEAK, min(CONF_STRONG, float(conf)))
        else:
            conf = CONF_GOOD
        rel = _map_l10_link_to_relation(link)
        if rel == REL_UNKNOWN:
            rel = REL_MUBTADA  # default isnadi to nominal
        # Passive-aware: if head is passive verb, subject link -> naib_fa'il
        try:
            head_idx = int(head_id_str)
            prof = l8b_map.get(head_idx)
            if prof and rel == REL_FAIL and (prof.get("voice") == "passive" or (prof.get("expected_subject_role") or "").strip() == "نائب فاعل"):
                rel = REL_NAIB_FAIL
        except (ValueError, TypeError):
            pass
        edges.append({
            "from_id": head_id_str,
            "to_id": dep_id_str,
            "relation": rel,
            "confidence": round(conf, 2),
            "status": "resolved" if conf >= CONF_GOOD else "candidate",
        })
        # Update node head/relation for dependent
        for n in nodes:
            if n.get("token_id") == dep_id_str:
                n["head_id"] = head_id_str
                n["relation"] = rel
                n["confidence"] = round(conf, 2)
                n["status"] = "resolved" if conf >= CONF_GOOD else "candidate"
                break

    # 3) Preposition → object (harf_jar + majrur) — STRICT: only if operator AND surface ∈ HARF_JAR_SET
    for i, surface in enumerate(tokens):
        if i + 1 >= len(tokens):
            break
        word = (surface or "").strip()
        is_operator = _is_operator_token(word, op_words)
        is_jar = is_operator and _token_in_normalized_set(word, _HARF_JAR_NORMALIZED)
        if is_jar:
            tid = str(i)
            next_tid = str(i + 1)
            if not any(e.get("from_id") == tid and e.get("to_id") == next_tid for e in edges):
                edges.append({
                    "from_id": tid,
                    "to_id": next_tid,
                    "relation": REL_MAJRUR,
                    "confidence": CONF_GOOD,
                    "status": "resolved",
                })
                attachments.append({
                    "token_id": next_tid,
                    "attached_to": tid,
                    "attachment_type": "jar_majrur",
                    "confidence": CONF_GOOD,
                })
                for n in nodes:
                    if n.get("token_id") == next_tid:
                        n["head_id"] = tid
                        n["relation"] = REL_MAJRUR
                        n["confidence"] = CONF_GOOD
                        n["status"] = "resolved"
                        break

    # 3b) Passive-aware: L8B passive verb + following noun -> naib_fa'il candidate (suppress active fa'il)
    for i in range(len(tokens) - 1):
        prof = l8b_map.get(i)
        if not prof:
            continue
        if (prof.get("voice") or "").strip() != "passive":
            continue
        exp_role = (prof.get("expected_subject_role") or "").strip()
        gov_fam = (prof.get("governance_family") or "") or ""
        if exp_role != "نائب فاعل" and "passive" not in gov_fam:
            continue
        tid_i = str(i)
        tid_next = str(i + 1)
        next_has_head = any(n.get("token_id") == tid_next and n.get("head_id") is not None for n in nodes)
        if next_has_head:
            continue
        pos_next = _pos_hint((tokens[i + 1] or "").strip(), words5, words8, words9, op_words)
        if pos_next not in ("noun", "اسم"):
            continue
        voice_ev = prof.get("voice_evidence") or {}
        conf_passive = max(CONF_CANDIDATE, min(CONF_STRONG, float(voice_ev.get("confidence", CONF_GOOD))))
        if not any(e.get("from_id") == tid_i and e.get("to_id") == tid_next for e in edges):
            edges.append({
                "from_id": tid_i,
                "to_id": tid_next,
                "relation": REL_NAIB_FAIL,
                "confidence": round(conf_passive, 2),
                "status": "resolved" if conf_passive >= CONF_GOOD else "candidate",
            })
            for n in nodes:
                if n.get("token_id") == tid_next:
                    n["head_id"] = tid_i
                    n["relation"] = REL_NAIB_FAIL
                    n["confidence"] = round(conf_passive, 2)
                    n["status"] = "resolved" if conf_passive >= CONF_GOOD else "candidate"
                    break

    # 4) Idafa: STRICT — both nouns, second definite or possessive; first not verbish/L8B verb/harf jar; do not attach to token already naib_fa'il (weak idafa suppression)
    for i in range(len(tokens) - 1):
        tid_i = str(i)
        tid_j = str(i + 1)
        t1 = (tokens[i] or "").strip()
        t2 = (tokens[i + 1] or "").strip()
        pos_i = _pos_hint(t1, words5, words8, words9, op_words)
        pos_j = _pos_hint(t2, words5, words8, words9, op_words)
        both_nouns = pos_i in ("noun", "اسم") and pos_j in ("noun", "اسم")
        second_def_or_poss = _second_noun_definite_or_possessive(t2)
        first_not_verbish = not _is_verbish(pos_i, words9, t1)
        first_not_l8b_verb = i not in l8b_map  # L8B verb must not head idafa
        first_not_harf_jar = not (_is_operator_token(t1, op_words) and _token_in_normalized_set(t1, _HARF_JAR_NORMALIZED))
        # Do not make j mudaf ilayh if j is already naib_fa'il (stronger verbal structure)
        j_node = next((n for n in nodes if n.get("token_id") == tid_j), None)
        j_already_naib_fail = (j_node and (j_node.get("relation") or "").strip() == REL_NAIB_FAIL)
        if both_nouns and second_def_or_poss and first_not_verbish and first_not_l8b_verb and first_not_harf_jar and not j_already_naib_fail:
            if not any(e.get("from_id") == tid_i and e.get("to_id") == tid_j for e in edges):
                edges.append({
                    "from_id": tid_i,
                    "to_id": tid_j,
                    "relation": REL_IDAFA,
                    "confidence": CONF_CANDIDATE,
                    "status": "candidate",
                })
                for n in nodes:
                    if n.get("token_id") == tid_j and n.get("head_id") is None:
                        n["head_id"] = tid_i
                        n["relation"] = REL_IDAFA
                        n["confidence"] = CONF_CANDIDATE
                        n["status"] = "candidate"
                        break

    # 4b) Weak idafa suppression: downgrade idafa when mudaf (from_id) follows a passive verb (competing verbal structure)
    for e in edges:
        if e.get("relation") != REL_IDAFA:
            continue
        try:
            i = int(e.get("from_id", -1))
            if i <= 0:
                continue
            prev_prof = l8b_map.get(i - 1)
            if prev_prof and (prev_prof.get("voice") or "").strip() == "passive":
                e["confidence"] = CONF_WEAK
                e["status"] = "candidate"
                e["idafa_suppression"] = "weak idafa candidate under competing verbal structure"
                for n in nodes:
                    if n.get("token_id") == e.get("to_id"):
                        n["confidence"] = CONF_WEAK
                        n["idafa_suppression"] = "weak idafa candidate under competing verbal structure"
                        break
        except (ValueError, TypeError):
            pass

    # 5) Conditional marker: any token operator AND surface ∈ SHART_MARKERS → mark shart and set clause type
    conditional_marker_present = False
    for i, surface in enumerate(tokens):
        w = (surface or "").strip()
        if _is_operator_token(w, op_words) and _token_in_normalized_set(w, _SHART_MARKERS_NORMALIZED):
            conditional_marker_present = True
            for n in nodes:
                if n.get("token_id") == str(i):
                    n["relation"] = REL_SHART_MARKER
                    n["status"] = "resolved"
                    break
            clause_units.append({
                "clause_id": f"clause_{i}",
                "type": "conditional",
                "start_token_id": str(i),
                "end_token_id": str(len(tokens) - 1),
                "head_token_id": str(i),
            })
            break

    # 6) Main clause type hierarchy: conditional > verbal > nominal
    main_finite_verb_present = False
    for w9 in words9:
        tpl = (w9.get("template") or w9.get("word_wazn") or "").strip()
        if _is_finite_verb_wazn(tpl):
            main_finite_verb_present = True
            break
    if conditional_marker_present:
        main_clause_type = "conditional"
    elif main_finite_verb_present or isnadi_links:
        main_clause_type = "verbal"
    else:
        main_clause_type = "nominal"

    clause_units.insert(0, {
        "clause_id": "main",
        "type": main_clause_type,
        "start_token_id": "0",
        "end_token_id": str(len(tokens) - 1),
        "head_token_id": "0" if tokens else None,
    })

    # 7) Summary + parse_strength and shallow-parse advisory
    resolved_edges = sum(1 for e in edges if e.get("status") == "resolved")
    candidate_edges = sum(1 for e in edges if e.get("status") == "candidate")
    unresolved_tokens = sum(1 for n in nodes if n.get("status") == "unresolved")
    denom = resolved_edges + candidate_edges + 1
    base_parse_strength = (resolved_edges / denom) if denom else 0.0
    advisory_notes: List[str] = []
    if base_parse_strength < 0.35:
        advisory_notes.append("dependency parse shallow — interpret cautiously")

    syntax_summary = {
        "resolved_edges": resolved_edges,
        "candidate_edges": candidate_edges,
        "unresolved_tokens": unresolved_tokens,
        "main_clause_type": main_clause_type,
        "parse_strength": round(base_parse_strength, 3),
        "advisory_notes": advisory_notes,
    }

    # 8) L10B-V Verb Governance: alignment, penalties, boosting, trace
    syntax_summary, syntax_reasoning_trace = _run_verb_governance_pass(
        tokens, lo, nodes, edges, syntax_summary, base_parse_strength
    )

    # Tightening pass: record weak idafa suppression in trace
    if any(e.get("idafa_suppression") for e in edges):
        syntax_reasoning_trace.append("Weak idafa candidate suppressed due to stronger verbal/passive structure.")

    return nodes, edges, clause_units, attachments, syntax_summary, syntax_reasoning_trace


class RealL10BDeepSyntax(BaseStage):
    """
    L10B: Deep dependency syntax — builds dependency graph from L2, L4, L5, L8, L9, L10.
    Does not replace L10; coexists as deeper structured layer.
    """

    def __init__(self) -> None:
        super().__init__("L10B_DEEP_SYNTAX", STAGE_NAMES["L10B_DEEP_SYNTAX"], 12)

    def run(self, pipeline: PipelineDict) -> LayerOutputDict:
        lo = pipeline.get("layer_outputs") or {}
        received = get_previous_output(pipeline, self.stage_index) or {}

        tokens = _get_tokens(pipeline)
        if not tokens:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "skipped",
                received_input=received,
                transformation_result={
                    "dependency_nodes": [],
                    "dependency_edges": [],
                    "clause_units": [],
                    "attachments": [],
                    "syntax_summary": {
                        "resolved_edges": 0,
                        "candidate_edges": 0,
                        "unresolved_tokens": 0,
                        "main_clause_type": "unknown",
                        "parse_strength": 0.0,
                        "advisory_notes": [],
                        "verb_governance_applied": False,
                        "governance_alignment_score": 0.0,
                        "missing_arguments": [],
                        "illegal_arguments": [],
                    },
                    "syntax_reasoning_trace": [],
                },
                raw_module_output={},
                next_input=received,
                warnings=["No tokens; deep syntax skipped."],
            )

        try:
            nodes, edges, clause_units, attachments, syntax_summary, syntax_reasoning_trace = _build_dependency_structure(tokens, lo)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result={
                    "dependency_nodes": [],
                    "dependency_edges": [],
                    "clause_units": [],
                    "attachments": [],
                    "syntax_summary": {
                        "resolved_edges": 0, "candidate_edges": 0, "unresolved_tokens": len(tokens),
                        "main_clause_type": "unknown", "parse_strength": 0.0, "advisory_notes": [],
                        "verb_governance_applied": False, "governance_alignment_score": 0.0,
                        "missing_arguments": [], "illegal_arguments": [],
                    },
                    "syntax_reasoning_trace": [],
                },
                raw_module_output={},
                next_input=received,
                errors=[str(e)],
            )

        has_strong = syntax_summary.get("resolved_edges", 0) > 0
        has_any = len(edges) > 0 or len(attachments) > 0
        status = "success" if has_strong else ("partial" if has_any else "partial")

        result = {
            "dependency_nodes": nodes,
            "dependency_edges": edges,
            "clause_units": clause_units,
            "attachments": attachments,
            "syntax_summary": syntax_summary,
            "syntax_reasoning_trace": syntax_reasoning_trace,
        }

        return build_layer_output(
            self.layer_id,
            self.layer_name,
            self.stage_index,
            status,
            received_input=received,
            transformation_result=result,
            raw_module_output=result,
            next_input=result,
            reused_module={"file": "orchestrator/l10b_deep_syntax.py", "symbol": "RealL10BDeepSyntax", "mode": "direct"},
        )
