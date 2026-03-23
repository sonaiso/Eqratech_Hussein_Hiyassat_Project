# -*- coding: utf-8 -*-
"""
Batch 28.12–28.13 — decision-faithful serialization for accepted erqa rows.

``system_i3rab`` must not contradict the comparator's accepted structured basis
(e.g. L17 mudaf_ilayh vs stale L11 «خبر مرفوع» prose).

Batch 28.13 — modifier-aware specificity: prefer gold-resolved roles (e.g. نعت) over
generic L11 «اسم مجرور» display; normalize accepted_role / signature consistency.

Batch 28.15 — canonical accepted metadata: case, marker, signature, and governor are derived
from the final accepted role + ``system_i3rab`` display; no stale multi-code signatures or
contradictory nominative/genitive traces.
"""

from __future__ import annotations

import re
from typing import Any, Dict, Optional, Tuple

from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision
from orchestrator.quran_gold.gold_prose_parser import effective_gold_structure_for_compare, parse_gold_i3rab_prose
from orchestrator.quran_gold.gold_structured import GoldStructuredI3rab

# erqa_i3rab.csv columns (append-only compatible; new fields at end).
ERQA_ACCEPTED_ROW_FIELDNAMES: tuple[str, ...] = (
    "surah",
    "ayah",
    "word",
    "gold_i3rab",
    "system_i3rab",
    "match_type",
    "confidence",
    "analyzer_source",
    "notes",
    "ayah_word_index",
    "accepted_analysis_source",
    "accepted_structured_signature",
    "accepted_role",
    "accepted_case_bucket",
    "accepted_marker",
    "accepted_governing_factor",
    "accepted_confidence",
    "decision_basis",
    "raw_system_i3rab_before_hardening",
)

# Canonical Arabic lines for gold parser role keys (conservative, one sentence).
_ROLE_KEY_TO_AR: Dict[str, str] = {
    "mudaf_ilaih": "مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.",
    "ism_majrur": "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.",
    "ism_inna": "اسْمٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ.",
    "khabar_inna": "خَبَرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
    "khabar": "خَبَرٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
    "mubtada": "مُبْتَدَأٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
    "naat": "نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.",
    "fael": "فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
    "naib_fael": "نَائِبُ فَاعِلٍ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ.",
    "mafool_bih": "مَفْعُولٌ بِهٖ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ.",
    "mafool_mutlaq": "مَفْعُولٌ مُطْلَقٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ.",
    "harf_jar": "حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ.",
    "jar_majrur": "جَارٌّ وَمَجْرُورٌ.",
    "shibh_jumla": "شِبْهُ جُمْلَةٍ فِي مَحَلِّ نَصْبٍ.",
    "sila_mawsul": "صِلَةُ مَوْصُولٍ.",
    "darf": "ظَرْفٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ.",
}

_ROLE_SPECIFICITY: Dict[str, int] = {
    "naat": 72,
    "mudaf_ilaih": 70,
    "mafool_bih": 68,
    "fael": 66,
    "naib_fael": 65,
    "mubtada": 64,
    "khabar": 63,
    "ism_inna": 62,
    "khabar_inna": 61,
    "ism_majrur": 38,
    "harf_jar": 60,
    "jar_majrur": 58,
    "shibh_jumla": 55,
}


def render_structured_i3rab_ar(
    *,
    syntactic_role: str,
    i3rab_case_or_mood: str,
    marker: str,
    governing_factor: str,
) -> str:
    """
    Deterministic short Arabic line from L17-style structured fields.
    Prefer known templates; else non-contradictory minimal join.
    """
    r = (syntactic_role or "").strip()
    c = (i3rab_case_or_mood or "").strip()
    m = (marker or "").strip()
    if not r and not c:
        return ""

    r_compact = r.replace(" ", "")
    if "مضاف" in r and "إليه" in r_compact:
        return _ROLE_KEY_TO_AR["mudaf_ilaih"]
    if "مفعول" in r and "به" in r:
        return _ROLE_KEY_TO_AR["mafool_bih"]
    if "نائب" in r and "فاعل" in r:
        return _ROLE_KEY_TO_AR["naib_fael"]
    if "فاعل" in r and "نائب" not in r and "مفعول" not in r:
        return _ROLE_KEY_TO_AR["fael"]
    if "نعت" in r:
        if "منصوب" in c or "نصب" in c:
            return "نَعْتٌ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ."
        return _ROLE_KEY_TO_AR["naat"]
    if "حرف" in r and "جر" in r:
        return _ROLE_KEY_TO_AR["harf_jar"]
    if "موصول" in r or "مَوْصُول" in r:
        return "اسْمٌ مَوْصُولٌ مَبْنِيٌّ عَلَى الْفَتْحِ."
    if "خبر" in r and "إن" not in r and "مضاف" not in r:
        return _ROLE_KEY_TO_AR["khabar"]
    if "مبتدأ" in r or "مُبْتَدَأ" in r:
        return _ROLE_KEY_TO_AR["mubtada"]
    if "اسم" in r and "مجرور" in r and "مضاف" not in r_compact:
        return _ROLE_KEY_TO_AR["ism_majrur"]
    if "مجرور" in c or "مَجْرُور" in c:
        parts = [x for x in (r, c, f"علامة: {m}" if m and m != "—" else "") if x and x != "—"]
        return "، ".join(parts) + "."
    if "مرفوع" in c or "مَرْفُوع" in c:
        parts = [x for x in (r, c, f"علامة: {m}" if m and m != "—" else "") if x and x != "—"]
        return "، ".join(parts) + "."
    if "منصوب" in c or "مَنْصُوب" in c:
        parts = [x for x in (r, c, f"علامة: {m}" if m and m != "—" else "") if x and x != "—"]
        return "، ".join(parts) + "."
    parts = [x for x in (r, c, m if m != "—" else "") if x and x != "—"]
    return " — ".join(parts) if parts else ""


def _naat_ordinal_key_from_gold(gold_i3rab: str) -> Optional[str]:
    """Detect ثانٍ / ثالث / رابع in gold prose for naʿt lines (letters-only safe)."""
    t = _letters_only(gold_i3rab or "")
    if "ثان" in t or "ثَان" in (gold_i3rab or ""):
        return "second"
    if "ثالث" in t or "ثَالث" in t:
        return "third"
    if "رابع" in t or "رَابِع" in t:
        return "fourth"
    return None


def _is_generic_ism_majrur_template_line(line: str) -> bool:
    """True if display is the stock «اسْمٌ مَجْرُورٌ …» template, not a specific role line."""
    z = _letters_only(line or "")
    return "اسم" in z and "مجرور" in z and "نعت" not in z and "مضاف" not in z


def render_gold_structured_display(gs: GoldStructuredI3rab, gold_i3rab: str) -> str:
    """
    Canonical Arabic line from **gold** structured parse + optional ordinal from gold prose.
    Used when comparator accepted strict match but L11 prose is generically «اسم مجرور».
    """
    if gs.syntactic_role_status != "resolved" or not gs.syntactic_role:
        return ""
    key = gs.syntactic_role
    if key == "naat":
        ord_key = _naat_ordinal_key_from_gold(gold_i3rab)
        if ord_key == "second":
            return (
                "نَعْتٌ ثَانٍ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
            )
        if ord_key == "third":
            return (
                "نَعْتٌ ثَالِثٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
            )
        if ord_key == "fourth":
            return (
                "نَعْتٌ رَابِعٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
            )
        return _ROLE_KEY_TO_AR.get("naat", "")
    line = _ROLE_KEY_TO_AR.get(key, "")
    if line:
        return line
    return ""


def _render_from_gold_structured(gs: GoldStructuredI3rab) -> str:
    if gs.syntactic_role_status == "resolved" and gs.syntactic_role:
        line = _ROLE_KEY_TO_AR.get(gs.syntactic_role, "")
        if line:
            return line
    return ""


_DIAC = re.compile(r"[\u064b-\u065f\u0670\u0640]")


def _letters_only(s: str) -> str:
    return _DIAC.sub("", s or "")


def _khabar_marfuu_contradicts_mudaf(raw: str) -> bool:
    t = _letters_only(raw).replace(" ", "")
    return "خبر" in t and "مرفوع" in t and "مضاف" not in t


def raw_prose_contradicts_accepted_structure(
    raw_prose: str,
    *,
    gold_i3rab: str,
    l17: Optional[Dict[str, Any]],
) -> bool:
    """Heuristic: L11-style prose clearly wrong vs gold/L17 mudaf_ilayh."""
    gs = effective_gold_structure_for_compare(gold_i3rab)
    if gs.syntactic_role == "mudaf_ilaih" and gs.syntactic_role_status == "resolved":
        if _khabar_marfuu_contradicts_mudaf(raw_prose):
            return True
    if l17:
        lr = (l17.get("syntactic_role") or "").replace(" ", "")
        if "مضاف" in (l17.get("syntactic_role") or "") and "إليه" in lr:
            if _khabar_marfuu_contradicts_mudaf(raw_prose):
                return True
    return False


def _infer_case_bucket_from_display(display: str) -> str:
    """Map canonical ``system_i3rab`` line to comparator case bucket labels."""
    z = _letters_only(display or "")
    d = display or ""
    if "مجرور" in z or "مَجْرُور" in d:
        return "genitive"
    if "مرفوع" in z or "مَرْفُوع" in d:
        return "nominative"
    if "منصوب" in z or "مَنْصُوب" in d:
        return "accusative"
    if "مبني" in z or "مَبْنِي" in d:
        return "built"
    if "مجزوم" in z or "مَجْزُوم" in d:
        return "jussive"
    return ""


def _infer_marker_from_display(display: str) -> str:
    """Marker label aligned with the written Arabic iʿrāb line."""
    d = display or ""
    z = _letters_only(d)
    if "الكسرة" in z or "كسرة" in z:
        return "الكسرة"
    if "الضمة" in z or ("ضمة" in z and "مجرور" not in z):
        return "الضمة"
    if "الفتحة" in z or "فتحة" in z:
        return "الفتحة"
    if "مبني" in z:
        return "مبني"
    return ""


def _reconcile_marker_with_case(marker: str, case_b: str) -> str:
    """Drop stale رفع marker hints when case is genitive (and vice versa)."""
    m = (marker or "").strip()
    c = (case_b or "").strip()
    if c == "genitive" and m == "الضمة":
        return ""
    if c == "nominative" and m == "الكسرة":
        return ""
    if c == "accusative" and m in ("الضمة", "الكسرة"):
        return ""
    return m


def _canonical_governing_factor_for_role(
    role: str,
    l17: Optional[Dict[str, Any]],
    trace: Optional[Dict[str, str]],
) -> str:
    """Keep governor only when compatible with the canonical accepted role (Batch 28.15)."""
    raw = ""
    if l17:
        raw = (l17.get("governing_factor") or "").strip()
    if raw in ("", "—"):
        raw = ""
    # Spurious idafa governor on roles that are not مضاف إليه
    if role != "mudaf_ilaih" and raw == "المضاف":
        return ""
    if role == "mudaf_ilaih":
        return raw[:200] if raw else "المضاف"
    if role in ("naat", "ism_majrur", "mubtada", "fael", "mafool_bih", "naib_fael", "khabar"):
        return raw[:200] if raw else ""
    if role == "harf_jar":
        return raw[:200] if raw else ""
    return raw[:200] if raw else ""


def canonicalize_accepted_metadata(
    *,
    canonical_role: str,
    system_i3rab: str,
    gold_i3rab: str,
    l17: Optional[Dict[str, Any]],
    trace: Optional[Dict[str, str]],
    dec: MatchDecision,
) -> Dict[str, str]:
    """
    Single source of truth for accepted ERQA metadata columns (Batch 28.15).

    Authority: final ``canonical_role`` + canonical ``system_i3rab`` display; gold/L17 hints
    only fill gaps when non-contradictory.
    """
    role = (canonical_role or "").strip()
    disp = (system_i3rab or "").strip()

    if not role:
        gs_fallback = effective_gold_structure_for_compare(gold_i3rab)
        if gs_fallback.syntactic_role_status == "resolved" and gs_fallback.syntactic_role:
            role = gs_fallback.syntactic_role or ""

    case_b = _infer_case_bucket_from_display(disp)
    if not case_b:
        gs = effective_gold_structure_for_compare(gold_i3rab)
        if gs.case_status == "resolved" and gs.case_bucket:
            case_b = gs.case_bucket or ""
    if not case_b and trace:
        tc = (trace.get("gold_case_bucket") or "").strip()
        if tc and trace.get("gold_role") == role:
            case_b = tc

    marker = _infer_marker_from_display(disp)
    if not marker and l17:
        lm = (l17.get("marker") or "").strip()
        if lm and lm != "—":
            marker = lm
    marker = _reconcile_marker_with_case(marker, case_b)

    sig = (role or "").strip()
    gov = _canonical_governing_factor_for_role(role, l17, trace)

    return {
        "accepted_role": role,
        "accepted_case_bucket": case_b,
        "accepted_marker": marker[:120],
        "accepted_structured_signature": sig,
        "accepted_governing_factor": gov[:200],
        "system_i3rab": disp,
    }


def validate_accepted_row_invariants(row: Dict[str, Any]) -> list[str]:
    """Return human-readable invariant violations (empty list = OK). Tests + QA."""
    issues: list[str] = []
    role = (row.get("accepted_role") or "").strip()
    case_b = (row.get("accepted_case_bucket") or "").strip()
    marker = (row.get("accepted_marker") or "").strip()
    sig = (row.get("accepted_structured_signature") or "").strip()
    disp = row.get("system_i3rab") or ""
    z = _letters_only(disp)

    if sig and role and sig != role:
        issues.append(f"signature {sig!r} != role {role!r}")

    if case_b == "genitive" and ("مرفوع" in z and "مجرور" not in z):
        issues.append("genitive bucket but display looks marfuu")
    if case_b == "nominative" and ("مجرور" in z and "مرفوع" not in z):
        issues.append("nominative bucket but display looks majruur")

    if role == "naat" and "mubtada" in sig:
        issues.append("naat role with mubtada in signature")

    if case_b == "genitive" and marker == "الضمة":
        issues.append("genitive case with raf marker")

    return issues


def _authoritative_role_key(trace: Optional[Dict[str, str]], l17: Optional[Dict[str, Any]]) -> str:
    if trace:
        st = (trace.get("gold_role_status") or "").strip()
        gr = (trace.get("gold_role") or "").strip()
        if st == "resolved" and gr:
            return gr
    if l17:
        # Map common L17 Arabic labels to comparator keys (conservative).
        b = (
            (l17.get("syntactic_role") or "")
            + " "
            + (l17.get("governing_factor") or "")
        )
        b_compact = b.replace(" ", "")
        if "مضاف" in b and "إليه" in b_compact:
            return "mudaf_ilaih"
        if "نعت" in b:
            return "naat"
        if "مفعول" in b and "به" in b:
            return "mafool_bih"
        if "فاعل" in b and "نائب" not in b:
            return "fael"
    return (trace.get("gold_role") or "").strip() if trace else ""


def _should_prefer_gold_display_over_l17(
    gs_gold: GoldStructuredI3rab,
    l17_line: str,
) -> bool:
    if gs_gold.syntactic_role_status != "resolved" or not gs_gold.syntactic_role:
        return False
    gr = gs_gold.syntactic_role
    sp_g = _ROLE_SPECIFICITY.get(gr, 0)
    if gr == "naat" and _is_generic_ism_majrur_template_line(l17_line):
        return True
    if gr == "mudaf_ilaih" and _is_generic_ism_majrur_template_line(l17_line):
        return True
    sp_line = 0
    if "نعت" in (l17_line or "") or "نَعْت" in (l17_line or ""):
        sp_line = _ROLE_SPECIFICITY.get("naat", 0)
    elif "مضاف" in (l17_line or "") and "إليه" in (l17_line or "").replace(" ", ""):
        sp_line = _ROLE_SPECIFICITY.get("mudaf_ilaih", 0)
    elif _is_generic_ism_majrur_template_line(l17_line):
        sp_line = _ROLE_SPECIFICITY.get("ism_majrur", 0)
    return sp_g > sp_line and sp_g > 0


def normalize_accepted_structured_metadata(
    *,
    trace: Optional[Dict[str, str]],
    l17: Optional[Dict[str, Any]],
    gold_i3rab: str,
    dec: MatchDecision,
    canonical_display: str,
    decision_basis: str,
    accepted_analysis_source: str,
) -> Tuple[str, str, str, str]:
    """
    Returns (accepted_role, system_i3rab, decision_basis, accepted_analysis_source).

    Batch 28.15: structured signature / case / marker are produced by
    ``canonicalize_accepted_metadata`` from the final role + display.
    """
    gs = effective_gold_structure_for_compare(gold_i3rab)
    auth = _authoritative_role_key(trace, l17)
    if not auth and gs.syntactic_role_status == "resolved" and gs.syntactic_role:
        auth = gs.syntactic_role or ""

    disp = canonical_display
    basis = decision_basis
    acc_src = accepted_analysis_source

    # Rebuild display from gold if trace authority is naat/mudaf but line still generic.
    if dec.tier == ComparatorTier.STRICT_STRUCTURAL_MATCH:
        gdisp = render_gold_structured_display(gs, gold_i3rab) or _render_from_gold_structured(gs)
        if gdisp:
            if auth == "naat" and _is_generic_ism_majrur_template_line(disp):
                disp = gdisp
                if "gold" not in basis and "normaliz" not in basis:
                    basis = f"{basis}|metadata_naat_display" if basis else "metadata_naat_display"
            elif auth == "mudaf_ilaih" and _is_generic_ism_majrur_template_line(disp):
                disp = gdisp
                if "gold" not in basis and "normaliz" not in basis:
                    basis = f"{basis}|metadata_mudaf_display" if basis else "metadata_mudaf_display"

    disp2 = enforce_accepted_row_consistency(
        system_i3rab=disp,
        accepted_role=auth,
        gold_i3rab=gold_i3rab,
        tier=dec.tier,
    )
    if disp2 != disp:
        disp = disp2
        basis = f"{basis}|consistency_guard" if basis else "consistency_guard"

    return auth, disp, basis[:500], acc_src


def enforce_accepted_row_consistency(
    *,
    system_i3rab: str,
    accepted_role: str,
    gold_i3rab: str,
    tier: ComparatorTier,
) -> str:
    """Last pass: display must not contradict normalized role (letters-only checks)."""
    if tier != ComparatorTier.STRICT_STRUCTURAL_MATCH:
        return system_i3rab
    z = _letters_only(system_i3rab or "")
    r = (accepted_role or "").strip()
    if r == "naat" and "اسم" in z and "مجرور" in z and "نعت" not in z:
        fix = render_gold_structured_display(
            effective_gold_structure_for_compare(gold_i3rab),
            gold_i3rab,
        )
        return fix or _ROLE_KEY_TO_AR.get("naat", system_i3rab)
    if r == "mudaf_ilaih" and "خبر" in z and "مرفوع" in z:
        fix = _ROLE_KEY_TO_AR.get("mudaf_ilaih", "")
        return fix or system_i3rab
    if r == "mudaf_ilaih" and "اسم" in z and "مجرور" in z and "مضاف" not in z and "نعت" not in z:
        fix = _ROLE_KEY_TO_AR.get("mudaf_ilaih", "")
        return fix or system_i3rab
    return system_i3rab


def canonical_system_i3rab_for_acceptance(
    dec: MatchDecision,
    snap: Optional[TokenAnalyzerSnapshot],
    gold_i3rab: str,
) -> tuple[str, str, str]:
    """
    Returns (canonical_display, decision_basis, accepted_analysis_source).
    """
    raw = (dec.system_i3rab_display or "").strip()
    tier = dec.tier
    prov = (dec.analyzer_source or "").strip()
    trace = dec.trace or {}
    l17 = snap.l17 if snap else None
    l11 = (snap.l11_i3rab_text or "").strip() if snap else ""

    if tier == ComparatorTier.EXACT_TEXT_MATCH:
        return raw, (dec.notes or "exact_text_match"), "L11_exact_text"

    if tier != ComparatorTier.STRICT_STRUCTURAL_MATCH:
        return raw, (dec.notes or ""), prov

    if prov == "L11_structured":
        gs_gold = effective_gold_structure_for_compare(gold_i3rab)
        can = render_gold_structured_display(gs_gold, gold_i3rab) or _render_from_gold_structured(gs_gold)
        if can:
            return can, dec.notes or "strict_structured_gold_vs_l11_prose", "L11_structured_parse"
        gs_l11 = parse_gold_i3rab_prose(l11 or "")
        can = _render_from_gold_structured(gs_l11)
        if can:
            return can, dec.notes or "strict_structured_gold_vs_l11_prose", "L11_structured_parse"
        if l11:
            return l11, dec.notes or "strict_structured_gold_vs_l11_prose", "L11_structured_prose"
        return raw, (dec.notes or ""), prov

    # Strict + L17 authority (includes analyzer_source L17, L11+L17, legacy L17 paths)
    if l17:
        can = render_structured_i3rab_ar(
            syntactic_role=str(l17.get("syntactic_role") or ""),
            i3rab_case_or_mood=str(l17.get("i3rab_case_or_mood") or ""),
            marker=str(l17.get("marker") or ""),
            governing_factor=str(l17.get("governing_factor") or ""),
        ).strip()
        gs_gold = effective_gold_structure_for_compare(gold_i3rab)
        gcan = render_gold_structured_display(gs_gold, gold_i3rab) or _render_from_gold_structured(gs_gold)
        if can and gcan and _should_prefer_gold_display_over_l17(gs_gold, can):
            can = gcan
        if can:
            basis = trace.get("reason") or dec.notes or "strict_structured_gold_vs_l17"
            return can, basis, "L17_structured"
        gs = gs_gold
        fallback = _render_from_gold_structured(gs)
        if fallback:
            return fallback, dec.notes or "strict_structured_gold_vs_l17", "gold_structure_fallback"

    if raw_prose_contradicts_accepted_structure(raw, gold_i3rab=gold_i3rab, l17=l17):
        gs = effective_gold_structure_for_compare(gold_i3rab)
        fb = _render_from_gold_structured(gs)
        if fb:
            return fb, "serialization_guard_mudaf_vs_khabar", "gold_structure_guard"

    return raw, (dec.notes or ""), prov


def build_accepted_erqa_row(
    *,
    surah: int,
    ayah: int,
    word: str,
    gold_i3rab: str,
    ayah_word_index: int,
    dec: MatchDecision,
    snap: Optional[TokenAnalyzerSnapshot],
) -> Dict[str, Any]:
    """Full erqa row dict including Batch 28.12–28.13 provenance fields."""
    raw_before = (dec.system_i3rab_display or "").strip()
    can_text, basis, acc_src = canonical_system_i3rab_for_acceptance(dec, snap, gold_i3rab)
    l17 = snap.l17 if snap else None
    trace = dec.trace or {}

    accepted_role, can_text, basis, acc_src = normalize_accepted_structured_metadata(
        trace=trace,
        l17=l17,
        gold_i3rab=gold_i3rab,
        dec=dec,
        canonical_display=can_text,
        decision_basis=basis,
        accepted_analysis_source=acc_src,
    )

    canon = canonicalize_accepted_metadata(
        canonical_role=accepted_role,
        system_i3rab=can_text,
        gold_i3rab=gold_i3rab,
        l17=l17,
        trace=trace,
        dec=dec,
    )
    accepted_role = canon["accepted_role"]
    can_text = canon["system_i3rab"]
    sig = canon["accepted_structured_signature"]
    case_b = canon["accepted_case_bucket"]
    marker = canon["accepted_marker"]
    gov = canon["accepted_governing_factor"]
    if "b28_15_canonical_metadata" not in (basis or ""):
        basis = f"{basis}|b28_15_canonical_metadata" if basis else "b28_15_canonical_metadata"

    l17_conf = ""
    if l17:
        l17_conf = str(l17.get("confidence") or "").strip()

    return {
        "surah": surah,
        "ayah": ayah,
        "word": word,
        "gold_i3rab": gold_i3rab,
        "system_i3rab": can_text,
        "match_type": dec.tier.value,
        "confidence": f"{dec.confidence:.4f}",
        "analyzer_source": dec.analyzer_source,
        "notes": dec.notes,
        "ayah_word_index": ayah_word_index,
        "accepted_analysis_source": acc_src,
        "accepted_structured_signature": sig,
        "accepted_role": accepted_role[:200],
        "accepted_case_bucket": case_b,
        "accepted_marker": marker[:120],
        "accepted_governing_factor": gov[:200],
        "accepted_confidence": l17_conf,
        "decision_basis": basis[:300],
        "raw_system_i3rab_before_hardening": raw_before[:2000],
    }


def erqa_row_to_field_dict(row: Dict[str, Any]) -> Dict[str, str]:
    """Normalize keys for CSV (all columns present)."""
    return {k: str(row.get(k, "") if row.get(k) is not None else "") for k in ERQA_ACCEPTED_ROW_FIELDNAMES}
