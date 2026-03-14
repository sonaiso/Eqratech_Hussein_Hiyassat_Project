# -*- coding: utf-8 -*-
"""
L11B — Causal I3rab Engine.

Structured grammatical cause, syntactic role, case/mood reasoning, marker reasoning.
Consumes only L2, L4, L5, L8, L9, L10, L10B, L11. Does not invent roots/wazn/syntax.
Conservative, deterministic; weak evidence → candidate/partial.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from .builders import build_layer_output, get_previous_output
from .stages.base_stage import BaseStage
from .stages.placeholders import STAGE_NAMES
from .types import LayerOutputDict, PipelineDict

# Confidence bands [0.05, 0.98]; never 1.0 or 0.0
CONF_STRONG = 0.90
CONF_GOOD = 0.75
CONF_CANDIDATE = 0.60
CONF_WEAK_TEXT = 0.40
CONF_UNRESOLVED = 0.20

# Roles (first-scope)
ROLE_FAIL = "فاعل"
ROLE_NAIB_FAIL = "نائب فاعل"
ROLE_MAFUL_BIH = "مفعول به"
ROLE_MUBTADA = "مبتدأ"
ROLE_KHABAR = "خبر"
ROLE_ISM_MAJRUR = "اسم مجرور بحرف الجر"
ROLE_NAAT = "نعت"
ROLE_HAL = "حال"
ROLE_MDAF_ILAYH = "مضاف إليه"

# Governing factors
GOV_FAIL = "الفعل"
GOV_HARF_JAR = "حرف الجر"
GOV_IBTIDA = "الابتداء"
GOV_INNA = "إن وأخواتها"
GOV_KANA = "كان وأخواتها"
GOV_MAJHOUL = "فعل مبني للمجهول"

# Case/mood
CASE_MARFU = "مرفوع"
CASE_MANSUB = "منصوب"
CASE_MAJRUR = "مجرور"
CASE_MAJZUM = "مجزوم"
CASE_MABNI = "مبني"
CASE_GHAYR_MAHSUM = "غير محسوم"

# Markers
MARKER_DAMMA = "الضمة"
MARKER_FATHA = "الفتحة"
MARKER_KASRA = "الكسرة"
MARKER_SUKUN = "السكون"
MARKER_MABNI = "مبني"
MARKER_GHAYR = "غير محسوم"


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


def _l11_token_results(lo: Dict[str, Any]) -> List[Dict[str, Any]]:
    """L11 token_results with i3rab_text and optional dependency_head_id/relation."""
    tr11 = (lo.get("L11_I3RAB") or {}).get("transformation_result") or {}
    return tr11.get("token_results") or []


def _l10b_edges_and_nodes(lo: Dict[str, Any]) -> Tuple[List[Dict], List[Dict], str]:
    """L10B dependency_edges, dependency_nodes, main_clause_type."""
    tr = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
    edges = tr.get("dependency_edges") or []
    nodes = tr.get("dependency_nodes") or []
    summary = tr.get("syntax_summary") or {}
    clause_type = summary.get("main_clause_type") or "unknown"
    return edges, nodes, clause_type


def _l10b_parse_strength_and_advisory(lo: Dict[str, Any]) -> Tuple[float, List[str]]:
    """L10B parse_strength and advisory_notes. Respect these to avoid over-resolution."""
    tr = (lo.get("L10B_DEEP_SYNTAX") or {}).get("transformation_result") or {}
    summary = tr.get("syntax_summary") or {}
    parse_strength = summary.get("parse_strength")
    if parse_strength is None:
        resolved = summary.get("resolved_edges", 0)
        candidate = summary.get("candidate_edges", 0)
        denom = resolved + candidate + 1
        parse_strength = (resolved / denom) if denom else 0.0
    else:
        parse_strength = float(parse_strength)
    advisory_notes = list(summary.get("advisory_notes") or [])
    return parse_strength, advisory_notes


def _l8b_has_upstream_passive_verb(lo: Dict[str, Any], token_index: int, tokens: List[str]) -> bool:
    """True if any token before token_index has L8B profile with voice==passive (for idafa guard)."""
    tr = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
    profiles = tr.get("verb_governance_profiles") or []
    surface_to_passive: Dict[str, bool] = {}
    for p in profiles:
        surf = (p.get("surface") or "").strip()
        if surf and (p.get("voice") or "").strip() == "passive":
            surface_to_passive[surf] = True
    for k in range(token_index):
        if k >= len(tokens):
            break
        w = (tokens[k] or "").strip()
        if surface_to_passive.get(w):
            return True
    return False


def _is_harf_jar_from_l10b(token_id: str, edges: List[Dict], nodes: List[Dict]) -> Optional[str]:
    """If token is majrur (object of preposition), return head_id (the harf jar). Else None."""
    for e in edges:
        if e.get("to_id") == token_id and e.get("relation") == "majrur":
            return e.get("from_id")
    return None


def _prev_token_is_operator_jar(lo: Dict[str, Any], token_index: int, tokens: List[str]) -> bool:
    """True if previous token is operator and harf jar (L4 + L10B strict set)."""
    if token_index <= 0:
        return False
    tr4 = (lo.get("L4_OPERATORS") or {}).get("transformation_result") or {}
    op_words = tr4.get("words") or []
    prev_surface = (tokens[token_index - 1] or "").strip()
    is_op = any((x.get("word") or "").strip() == prev_surface and x.get("operator") for x in op_words)
    if not is_op:
        return False
    # Strict harf jar set (normalized) — same as L10B
    harf_jar_norm = frozenset({"من", "الى", "عن", "على", "في", "رب", "ب", "ك", "ل", "حتى"})
    norm = "".join(c for c in prev_surface if not ("\u064b" <= c <= "\u0652") and c != "\u0670").strip()
    return norm in harf_jar_norm


def _template_suggests_passive(template: str) -> bool:
    """True if wazn suggests passive (فُعِلَ, etc.)."""
    if not template:
        return False
    t = (template or "").strip()
    return "فعل" in t and "فاعل" not in t and "مفعول" not in t and ("فُعل" in t or "فعل" in t)


def _template_suggests_finite_verb(template: str) -> bool:
    """True if wazn suggests finite verb."""
    if not template:
        return False
    t = (template or "").strip()
    if "فاعل" in t or "مفعول" in t:
        return False
    return "فعل" in t or "يفعل" in t


def _build_one_token_reasoning(
    token_id: str,
    surface: str,
    idx: int,
    tokens: List[str],
    l11_results: List[Dict[str, Any]],
    edges: List[Dict],
    nodes: List[Dict],
    main_clause_type: str,
    lo: Dict[str, Any],
    parse_strength: float = 1.0,
    advisory_notes: Optional[List[str]] = None,
) -> Dict[str, Any]:
    """Build one entry for token_i3rab_reasoning. Uses only existing evidence. Respects L10B parse_strength."""
    role = ""
    role_status = "unresolved"
    governing_factor: Optional[str] = None
    case_or_mood: Optional[str] = None
    marker: Optional[str] = None
    reasoning_steps: List[str] = []
    supporting_sources: List[Dict[str, str]] = []
    confidence = CONF_UNRESOLVED
    limitations: List[str] = []

    tr5 = (lo.get("L5_WORD_TYPING") or {}).get("transformation_result") or {}
    tr9 = (lo.get("L9_WAZN_MATCHING") or {}).get("transformation_result") or {}
    words5 = tr5.get("words") or []
    words9 = tr9.get("words") or []
    l11_tok = next((t for t in l11_results if str(t.get("token_id")) == token_id), None)
    i3rab_text = (l11_tok.get("i3rab_text") or "").strip() if l11_tok else ""
    # Prefer L10B relation when present (passive-aware wiring)
    dep_relation = ""
    for n in nodes:
        if str(n.get("token_id")) == token_id and (n.get("relation") or "").strip():
            dep_relation = (n.get("relation") or "").strip()
            break
    if not dep_relation and l11_tok:
        dep_relation = (l11_tok.get("dependency_relation") or "").strip()
    dep_head_id = l11_tok.get("dependency_head_id") if l11_tok else None
    for n in nodes:
        if str(n.get("token_id")) == token_id and n.get("head_id") is not None:
            dep_head_id = n.get("head_id")
            break
    if dep_head_id is None and l11_tok:
        dep_head_id = l11_tok.get("dependency_head_id")

    kind = ""
    w5 = next((w for w in words5 if (w.get("word") or "").strip() == (surface or "").strip()), None)
    if w5:
        kind = (w5.get("kind") or "").strip().lower()
    template = ""
    w9 = next((w for w in words9 if (w.get("word") or "").strip() == (surface or "").strip()), None)
    if w9:
        template = (w9.get("template") or w9.get("word_wazn") or "").strip()

    # Rule A0 — L10B naib_fa'il edge (passive-aware wiring): take precedence
    if not role and (dep_relation == "naib_fa'il" or dep_relation == "naib_fa'il_candidate") and kind in ("noun", "اسم"):
        role = ROLE_NAIB_FAIL
        role_status = "resolved" if parse_strength >= 0.35 else "candidate"
        governing_factor = GOV_MAJHOUL
        case_or_mood = CASE_MARFU
        marker = MARKER_DAMMA
        reasoning_steps.append("L10B dependency: token is نائب فاعل (passive subject); L8B passive evidence.")
        supporting_sources.append({"source": "L10B_DEEP_SYNTAX", "evidence": "dependency_relation=naib_fa'il"})
        supporting_sources.append({"source": "L8B_VERB_BAB_GOVERNANCE", "evidence": "passive voice"})
        confidence = CONF_GOOD if parse_strength >= 0.35 else CONF_CANDIDATE
        if parse_strength < 0.35:
            limitations.append("deep syntax shallow")

    # Rule A — Preposition object (اسم مجرور): L10B resolved majrur OR operator in guarded HARF_JAR_SET + noun
    harf_jar_head = _is_harf_jar_from_l10b(token_id, edges, nodes)
    l10b_majrur_resolved = harf_jar_head is not None and any(
        e.get("to_id") == token_id and e.get("relation") == "majrur" and e.get("status") == "resolved"
        for e in edges
    )
    if harf_jar_head is not None:
        role = ROLE_ISM_MAJRUR
        role_status = "resolved" if (l10b_majrur_resolved and parse_strength >= 0.35) else "candidate"
        governing_factor = GOV_HARF_JAR
        case_or_mood = CASE_MAJRUR
        marker = MARKER_KASRA
        reasoning_steps.append("L10B dependency edge: token is majrur (object of preposition).")
        supporting_sources.append({"source": "L10B_DEEP_SYNTAX", "evidence": "dependency_edges relation=majrur"})
        confidence = CONF_STRONG
        if parse_strength < 0.35:
            role_status = "candidate"
            confidence = min(confidence, CONF_GOOD)
            limitations.append("deep syntax shallow")
    elif _prev_token_is_operator_jar(lo, idx, tokens) and kind in ("noun", "اسم"):
        role = ROLE_ISM_MAJRUR
        role_status = "resolved" if parse_strength >= 0.35 else "candidate"
        governing_factor = GOV_HARF_JAR
        case_or_mood = CASE_MAJRUR
        marker = MARKER_KASRA
        reasoning_steps.append("Previous token is operator and harf jar; current token is noun.")
        supporting_sources.append({"source": "L4_OPERATORS", "evidence": "operator + harf jar set"})
        supporting_sources.append({"source": "L5_WORD_TYPING", "evidence": f"kind={kind}"})
        confidence = CONF_GOOD
        if parse_strength < 0.35:
            limitations.append("deep syntax shallow")
            confidence = CONF_CANDIDATE

    # Rule B — نائب فاعل: passive verb + following noun (L8B or template); L10B edge handled in A0
    if not role and idx >= 1 and dep_relation != "majrur":
        prev_surface = (tokens[idx - 1] or "").strip()
        prev_w9 = next((w for w in words9 if (w.get("word") or "").strip() == prev_surface), None)
        prev_tpl = (prev_w9.get("template") or prev_w9.get("word_wazn") or "").strip() if prev_w9 else ""
        # L8B passive or template suggests passive
        tr8b = (lo.get("L8B_VERB_BAB_GOVERNANCE") or {}).get("transformation_result") or {}
        prev_has_l8b_passive = any(
            (p.get("surface") or "").strip() == prev_surface and (p.get("voice") or "").strip() == "passive"
            for p in (tr8b.get("verb_governance_profiles") or [])
        )
        if (prev_has_l8b_passive or _template_suggests_passive(prev_tpl)) and kind in ("noun", "اسم"):
            role = ROLE_NAIB_FAIL
            role_status = "resolved" if parse_strength >= 0.35 else "candidate"
            governing_factor = GOV_MAJHOUL
            case_or_mood = CASE_MARFU
            marker = MARKER_DAMMA
            if prev_has_l8b_passive:
                reasoning_steps.append("L8B passive verb precedes; noun is نائب فاعل.")
                supporting_sources.append({"source": "L8B_VERB_BAB_GOVERNANCE", "evidence": "voice=passive"})
            else:
                reasoning_steps.append("Verb has passive morphology; following noun is نائب فاعل.")
                supporting_sources.append({"source": "L9_WAZN_MATCHING", "evidence": f"template={prev_tpl}"})
            supporting_sources.append({"source": "L5_WORD_TYPING", "evidence": f"kind={kind}"})
            confidence = CONF_GOOD if parse_strength >= 0.35 else CONF_CANDIDATE
            if parse_strength < 0.35:
                limitations.append("deep syntax shallow" if not prev_has_l8b_passive else "passive evidence strong but dependency support weak")

    # Rule C — فاعل: finite verb + following noun (no stronger constraint)
    if not role and idx >= 1 and kind in ("noun", "اسم") and dep_relation != "majrur":
        prev_surface = (tokens[idx - 1] or "").strip()
        prev_w9 = next((w for w in words9 if (w.get("word") or "").strip() == prev_surface), None)
        prev_tpl = (prev_w9.get("template") or prev_w9.get("word_wazn") or "").strip() if prev_w9 else ""
        if _template_suggests_finite_verb(prev_tpl) and not _template_suggests_passive(prev_tpl):
            role = ROLE_FAIL
            role_status = "resolved" if parse_strength >= 0.35 else "candidate"
            governing_factor = GOV_FAIL
            case_or_mood = CASE_MARFU
            marker = MARKER_DAMMA
            reasoning_steps.append("Finite verb precedes; noun is فاعل.")
            supporting_sources.append({"source": "L9_WAZN_MATCHING", "evidence": f"template={prev_tpl}"})
            confidence = CONF_GOOD if parse_strength >= 0.35 else CONF_CANDIDATE
            if parse_strength < 0.35:
                limitations.append("deep syntax shallow")

    # Rule D — مفعول به: verb + accusative-like noun (after subject position)
    if not role and idx >= 2 and kind in ("noun", "اسم") and dep_relation != "majrur":
        # Simple heuristic: third token after verb+subject can be object
        prev2 = (tokens[idx - 2] or "").strip()
        prev_w9_2 = next((w for w in words9 if (w.get("word") or "").strip() == prev2), None)
        prev_tpl_2 = (prev_w9_2.get("template") or prev_w9_2.get("word_wazn") or "").strip() if prev_w9_2 else ""
        if _template_suggests_finite_verb(prev_tpl_2):
            role = ROLE_MAFUL_BIH
            role_status = "candidate"
            governing_factor = GOV_FAIL
            case_or_mood = CASE_MANSUB
            marker = MARKER_FATHA
            reasoning_steps.append("Finite verb in clause; noun in object position → مفعول به candidate.")
            supporting_sources.append({"source": "L9_WAZN_MATCHING", "evidence": "verb + position"})
            confidence = CONF_CANDIDATE

    # Rule E — Nominal: مبتدأ / خبر
    if not role and main_clause_type == "nominal" and kind in ("noun", "اسم"):
        if idx == 0:
            role = ROLE_MUBTADA
            role_status = "candidate"
            governing_factor = GOV_IBTIDA
            case_or_mood = CASE_MARFU
            marker = MARKER_DAMMA
            reasoning_steps.append("Nominal clause; first noun → مبتدأ candidate.")
            supporting_sources.append({"source": "L10B_DEEP_SYNTAX", "evidence": f"main_clause_type={main_clause_type}"})
            confidence = CONF_CANDIDATE
        elif idx == 1 and len(tokens) >= 2:
            role = ROLE_KHABAR
            role_status = "candidate"
            governing_factor = GOV_IBTIDA
            case_or_mood = CASE_MARFU
            marker = MARKER_DAMMA
            reasoning_steps.append("Nominal clause; second token → خبر candidate.")
            supporting_sources.append({"source": "L10B_DEEP_SYNTAX", "evidence": "main_clause_type=nominal"})
            confidence = CONF_CANDIDATE

    # Rule H — Idafa: L10B idafa → مضاف إليه (only if no stronger passive/verbal evidence — idafa guard)
    if not role and dep_relation == "idafa":
        if _l8b_has_upstream_passive_verb(lo, idx, tokens):
            role = ROLE_NAIB_FAIL
            role_status = "candidate"
            governing_factor = GOV_MAJHOUL
            case_or_mood = CASE_MARFU
            marker = MARKER_DAMMA
            reasoning_steps.append("Weak idafa suppressed; preferred نائب فاعل from upstream passive evidence.")
            supporting_sources.append({"source": "L8B_VERB_BAB_GOVERNANCE", "evidence": "upstream passive verb"})
            confidence = CONF_CANDIDATE
            limitations.append("weak idafa suppressed; preferred نائب فاعل from passive evidence")
        else:
            role = ROLE_MDAF_ILAYH
            role_status = "candidate"
            governing_factor = GOV_FAIL  # مضاف
            case_or_mood = CASE_MAJRUR
            marker = MARKER_KASRA
            reasoning_steps.append("L10B idafa edge → مضاف إليه candidate.")
            supporting_sources.append({"source": "L10B_DEEP_SYNTAX", "evidence": "dependency_relation=idafa"})
            confidence = CONF_CANDIDATE

    # Fallback: use L11 text as weak evidence only
    if not role and i3rab_text:
        role = "منقول من الإعراب النصي"
        role_status = "unresolved"
        governing_factor = None
        case_or_mood = CASE_GHAYR_MAHSUM
        marker = MARKER_GHAYR
        reasoning_steps.append("No strong rule matched; L11 text used as weak hint only.")
        supporting_sources.append({"source": "L11_I3RAB", "evidence": "i3rab_text (text-based)"})
        confidence = CONF_WEAK_TEXT
        limitations.append("Role inferred from text i3rab only; not structurally resolved.")

    if not role:
        role = "—"
        role_status = "unresolved"
        limitations.append("No sufficient evidence for role assignment.")

    # Preserve L10B advisory when parse is shallow
    if (advisory_notes or []) and parse_strength < 0.35:
        for note in advisory_notes or []:
            if note and "dependency parse shallow" in (note or ""):
                if note not in limitations:
                    limitations.append(note)
                break

    confidence = max(0.05, min(0.98, confidence))

    return {
        "token_id": token_id,
        "surface": surface,
        "role": role,
        "role_status": role_status,
        "governing_factor": governing_factor,
        "case_or_mood": case_or_mood,
        "marker": marker,
        "reasoning_steps": reasoning_steps,
        "supporting_sources": supporting_sources,
        "confidence": round(confidence, 2),
        "limitations": limitations,
    }


def _build_causal_i3rab(lo: Dict[str, Any], tokens: List[str]) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    """Build token_i3rab_reasoning list and i3rab_summary from pipeline layer_outputs. Respects L10B parse_strength."""
    l11_results = _l11_token_results(lo)
    edges, nodes, main_clause_type = _l10b_edges_and_nodes(lo)
    parse_strength, advisory_notes = _l10b_parse_strength_and_advisory(lo)

    token_reasoning: List[Dict[str, Any]] = []
    for idx, surface in enumerate(tokens):
        tid = str(idx)
        entry = _build_one_token_reasoning(
            tid, (surface or "").strip(), idx, tokens, l11_results, edges, nodes, main_clause_type, lo,
            parse_strength=parse_strength, advisory_notes=advisory_notes,
        )
        token_reasoning.append(entry)

    resolved = sum(1 for t in token_reasoning if t.get("role_status") == "resolved")
    candidate = sum(1 for t in token_reasoning if t.get("role_status") == "candidate")
    unresolved = sum(1 for t in token_reasoning if t.get("role_status") == "unresolved")
    summary = {
        "resolved_tokens": resolved,
        "candidate_tokens": candidate,
        "unresolved_tokens": unresolved,
    }
    return token_reasoning, summary


class RealL11BCausalI3rab(BaseStage):
    """
    L11B: Causal i3rab — structured role, governing factor, case/mood, marker reasoning.
    Consumes L2, L4, L5, L8, L9, L10, L10B, L11 only. Does not replace L11.
    """

    def __init__(self) -> None:
        super().__init__("L11B_CAUSAL_I3RAB", STAGE_NAMES["L11B_CAUSAL_I3RAB"], 14)

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
                    "token_i3rab_reasoning": [],
                    "i3rab_summary": {"resolved_tokens": 0, "candidate_tokens": 0, "unresolved_tokens": 0},
                },
                raw_module_output={},
                next_input=received,
                warnings=["No tokens; causal i3rab skipped."],
            )

        try:
            token_reasoning, summary = _build_causal_i3rab(lo, tokens)
        except Exception as e:
            return build_layer_output(
                self.layer_id,
                self.layer_name,
                self.stage_index,
                "failed",
                received_input=received,
                transformation_result={
                    "token_i3rab_reasoning": [],
                    "i3rab_summary": {"resolved_tokens": 0, "candidate_tokens": 0, "unresolved_tokens": len(tokens)},
                },
                raw_module_output={},
                next_input=received,
                errors=[str(e)],
            )

        resolved = summary.get("resolved_tokens", 0)
        has_any = resolved > 0 or summary.get("candidate_tokens", 0) > 0
        status = "success" if resolved > 0 else ("partial" if has_any else "partial")

        result = {
            "token_i3rab_reasoning": token_reasoning,
            "i3rab_summary": summary,
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
            reused_module={"file": "orchestrator/l11b_causal_i3rab.py", "symbol": "RealL11BCausalI3rab", "mode": "direct"},
        )
