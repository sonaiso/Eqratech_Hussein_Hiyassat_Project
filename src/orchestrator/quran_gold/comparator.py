# -*- coding: utf-8 -*-
"""
Conservative multi-tier iʿrāb comparison (gold CSV vs pipeline analyzers).

Batch 28.3–28.4: Only ``exact_text_match`` and ``strict_structural_match`` may append to
``erqa_i3rab.csv``. Batch 28.4 adds **structured gold prose** vs **L17 facts** (not prose-only).
"""

from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Optional, Set, Tuple

from fvafk.c2b.evaluation.i3rab_loader import I3rabParser

from orchestrator.quran_gold.analyzer_extract import L17_MIN_CONF_CANDIDATE, TokenAnalyzerSnapshot
from orchestrator.quran_gold.alignment import normalize_arabic_surface
from orchestrator.quran_gold.gold_prose_parser import (
    effective_gold_structure_for_compare,
    parse_gold_i3rab_prose,
)
from orchestrator.quran_gold.gold_structured import GoldStructuredI3rab

_PARSER = I3rabParser()


class ComparatorTier(str, Enum):
    EXACT_TEXT_MATCH = "exact_text_match"
    STRICT_STRUCTURAL_MATCH = "strict_structural_match"
    PARTIAL_STRUCTURED_MATCH = "partial_structured_match"
    COARSE_MATCH = "coarse_match"
    MISMATCH = "mismatch"


class MatchLevel(str, Enum):
    EXACT_TEXT = "exact_text_match"
    NORMALIZED_TEXT = "exact_text_match"
    STRUCTURED_ROLE = "strict_structural_match"
    STRUCTURED_CASE_MARKER = "partial_structured_match"
    PARTIAL_SEMANTIC = "coarse_match"
    NONE = "mismatch"


@dataclass(frozen=True)
class MatchDecision:
    tier: ComparatorTier
    confidence: float
    analyzer_source: str
    system_i3rab_display: str
    notes: str
    trace: Optional[Dict[str, str]] = None

    @property
    def level(self) -> MatchLevel:
        m = {
            ComparatorTier.EXACT_TEXT_MATCH: MatchLevel.EXACT_TEXT,
            ComparatorTier.STRICT_STRUCTURAL_MATCH: MatchLevel.STRUCTURED_ROLE,
            ComparatorTier.PARTIAL_STRUCTURED_MATCH: MatchLevel.STRUCTURED_CASE_MARKER,
            ComparatorTier.COARSE_MATCH: MatchLevel.PARTIAL_SEMANTIC,
            ComparatorTier.MISMATCH: MatchLevel.NONE,
        }
        return m[self.tier]


def _nfc(s: str) -> str:
    return unicodedata.normalize("NFC", (s or "").strip())


def _collapse_ws(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip())


def normalize_i3rab_for_exact_compare(s: str) -> str:
    """
    Safe normalization for exact-text checks on gold vs L11 (Batch 28.5):
    NFC, strip ZW/BOM, remove decorative quotes, collapse whitespace.
    """
    t = unicodedata.normalize("NFC", (s or "").strip())
    for z in ("\ufeff", "\u200b", "\u200c", "\u200d", "\u200e", "\u200f"):
        t = t.replace(z, "")
    for q in (
        '"',
        "'",
        "\u201c",
        "\u201d",
        "\u2018",
        "\u2019",
        "\u00ab",
        "\u00bb",
        "«",
        "»",
    ):
        t = t.replace(q, "")
    t = re.sub(r"\s+", " ", t).strip()
    return t


def structured_strict_gold_vs_l11_prose(
    gs: GoldStructuredI3rab, l11: str
) -> Tuple[bool, str]:
    """
    Strict structural agreement between parsed gold and parsed L11 prose (same parser).
    Both sides must have a resolved role; case must match when both resolve it.
    """
    l11_stripped = _collapse_ws(l11)
    if not l11_stripped:
        return False, "empty_l11"
    sy = parse_gold_i3rab_prose(l11_stripped)
    if gs.syntactic_role_status != "resolved" or sy.syntactic_role_status != "resolved":
        return False, "role_unresolved"
    if gs.syntactic_role != sy.syntactic_role:
        # L11 often uses «اسم مجرور» where gold uses «نعت» for adjectival اسم (Batch 28.5).
        if (
            gs.case_bucket == "genitive"
            and sy.case_bucket == "genitive"
            and {gs.syntactic_role, sy.syntactic_role} == {"naat", "ism_majrur"}
        ):
            pass
        # Batch 28.18: gold «حُرُوفٌ مُقَطَّعَة» vs pipeline L11 «حَرْفٌ مَبْنِيٌّ» for Alif-Lam-Mim, etc.
        elif {gs.syntactic_role, sy.syntactic_role} == {"muqatta_huruf", "harf_mabni"}:
            pass
        else:
            return False, "l11_role_mismatch"
    if gs.case_status == "resolved" and sy.case_status == "resolved":
        if gs.case_bucket != sy.case_bucket:
            return False, "case_bucket_mismatch_l11"
    elif gs.case_status == "resolved" and sy.case_status == "absent":
        # Short L11 may state case in words without parser hitting case_bucket (Batch 28.5).
        if gs.case_bucket == "genitive" and ("مجرور" in l11_stripped or "مَجْرُور" in l11_stripped):
            pass
        elif gs.case_bucket == "nominative" and ("مرفوع" in l11_stripped or "مَرْفُوع" in l11_stripped):
            pass
        elif gs.case_bucket == "accusative" and ("منصوب" in l11_stripped or "مَنْصُوب" in l11_stripped):
            pass
        else:
            return False, "l11_case_unparsed"
    elif gs.case_status == "absent" and sy.case_status == "resolved":
        return False, "gold_case_unparsed"
    min_c = min(gs.parser_confidence, sy.parser_confidence)
    if min_c < 0.52:
        return False, "low_pair_confidence"
    if gs.gram_family_status == "resolved" and sy.gram_family_status == "resolved":
        if gs.gram_family != sy.gram_family:
            return False, "family_mismatch_l11"
    return True, "l11_structured_ok"


def _strip_diacritics_ar(s: str) -> str:
    if not s:
        return ""
    return re.sub(r"[\u064B-\u065F\u0670\u0640]", "", _nfc(s))


def _l17_authoritative(snap: TokenAnalyzerSnapshot) -> bool:
    if not snap.l17:
        return False
    st = (snap.l17.get("status") or "").strip()
    conf = float(snap.l17.get("confidence") or 0.0)
    if st == "resolved":
        return True
    if st == "candidate" and conf >= L17_MIN_CONF_CANDIDATE:
        return True
    return False


def _infer_case_bucket_from_l17(l17: Dict[str, Any]) -> Optional[str]:
    blob = (
        (l17.get("i3rab_case_or_mood") or "")
        + " "
        + (l17.get("syntactic_role") or "")
        + " "
        + (l17.get("marker") or "")
    )
    rs = l17.get("reasoning_steps") or []
    if isinstance(rs, list) and rs:
        blob = blob + " " + " ".join(str(x) for x in rs)
    refs = l17.get("gold_rule_refs") or []
    # Fused لِل… (Batch 28.10): gold pairs لام جرّ + اسم الجلالة with genitive اسم analysis — not «built».
    if isinstance(refs, list) and "B28_10_LAM_AL_FUSED" in refs:
        return "genitive"
    # Batch 28.19: simple particles / tools marked مبني (incl. حرف جر منْ، على، في، …) → «built».
    # Must run before genitive heuristics: the substring «جر» inside «حرف جر» falsely matched the old
    # bare «جر» genitive cue (case_bucket_mismatch vs gold «مبني»).
    if re.search(r"مَبْنِيّ|مبني", blob):
        return "built"
    if re.search(r"مَرْفُوع|مرفوع|رفع", blob):
        return "nominative"
    if re.search(r"مَنْصُوب|منصوب|نَصْب|نصب", blob):
        return "accusative"
    if re.search(r"مَجْرُور|مجرور|جَارٌ\s*وَمَجْرُور|جار\s*ومجرور|مَحَلِّ\s*جَرّ|محل\s*جر", blob):
        return "genitive"
    if re.search(r"مَجْزُوم|مجزوم|جَزْم|جزم", blob):
        return "jussive"
    return None


def _l17_blob(l17: Dict[str, Any]) -> str:
    return (
        (l17.get("syntactic_role") or "")
        + " "
        + (l17.get("governing_factor") or "")
        + " "
        + (l17.get("i3rab_case_or_mood") or "")
        + " "
        + (l17.get("marker") or "")
    )


def _l17_role_codes(l17: Dict[str, Any]) -> Set[str]:
    b = _l17_blob(l17)
    codes: Set[str] = set()
    # Batch 28.18: coordinated accusative conjunct (و+إيا…) — L17 «معطوف» = same slot as gold «مفعول به»
    if "معطوف" in b:
        codes.add("mafool_bih")
    if "مفعول" in b and "به" in b:
        codes.add("mafool_bih")
    if "نائب" in b and "فاعل" in b:
        codes.add("naib_fael")
    elif "فاعل" in b and "نائب" not in b:
        codes.add("fael")
    if "مبتدأ" in b or "مُبْتَدَأ" in b:
        codes.add("mubtada")
    if re.search(r"خَبَرُ\s*إِن|خبر\s*إن", b):
        codes.add("khabar_inna")
    elif "خبر" in b:
        codes.add("khabar")
    if "اسم" in b and "إن" in b:
        codes.add("ism_inna")
    if "نعت" in b:
        codes.add("naat")
    if "مضاف" in b and "إليه" in b.replace(" ", ""):
        codes.add("mudaf_ilaih")
    if "اسم" in b and "مجرور" in b and not ("مفعول" in b and "به" in b):
        codes.add("ism_majrur")
    if "جار" in b and "مجرور" in b:
        codes.add("jar_majrur")
    if "حرف" in b and "جر" in b:
        codes.add("harf_jar")
    if "شبه" in b and "جملة" in b:
        codes.add("shibh_jumla")
    if "ظرف" in b or "ظَرْف" in b:
        codes.add("darf")
    return codes


def _l17_infer_family(l17: Dict[str, Any]) -> Optional[str]:
    b = _l17_blob(l17)
    if re.search(r"فِعْل|فعل|مضارع|ماض|أمر|مجزوم", b):
        return "verb"
    if re.search(r"حَرْف|حرف", b) and "مجرور" not in b[:20]:
        return "particle"
    if re.search(
        r"فاعل|مفعول|اسم|خبر|مبتدأ|نعت|ضمير|موصول|مجرور|منصوب|مرفوع|مفعول به",
        b,
    ):
        return "noun"
    return None


def _structured_trace(gs: GoldStructuredI3rab, l17: Dict[str, Any], extra: Dict[str, str]) -> Dict[str, str]:
    lb = _l17_blob(l17)
    return {
        "gold_family": gs.gram_family or "",
        "gold_role": gs.syntactic_role or "",
        "gold_case_bucket": gs.case_bucket or "",
        "gold_marker": gs.marker or "",
        "gold_role_status": gs.syntactic_role_status,
        "parser_confidence": str(gs.parser_confidence),
        "l17_role_blob": (l17.get("syntactic_role") or "")[:120],
        "l17_case_bucket": _infer_case_bucket_from_l17(l17) or "",
        "l17_marker": (l17.get("marker") or "")[:80],
        "l17_family_guess": _l17_infer_family(l17) or "",
        "l17_codes": ",".join(sorted(_l17_role_codes(l17))),
        **extra,
    }


def _structured_strict_agreement(gs: GoldStructuredI3rab, l17: Dict[str, Any]) -> Tuple[bool, str]:
    """Primary grammatical agreement: role + case + family compatibility."""
    codes = _l17_role_codes(l17)
    sys_case = _infer_case_bucket_from_l17(l17)
    lf = _l17_infer_family(l17)

    if gs.gram_family_status == "resolved" and lf and gs.gram_family:
        if gs.gram_family == "verb" and lf != "verb":
            return False, "family_conflict_verb_vs_nonverb"
        if gs.gram_family == "particle" and lf not in ("particle", None):
            # Batch 28.18: fused وَإِيَّاكَ — gold prose begins with «الْوَاوُ حَرْفُ عَطْفٍ» so family=particle,
            # while L17 uses noun-family «معطوف» for the accusative conjunct (Batch 28.17 wiring).
            if (
                gs.syntactic_role == "mafool_bih"
                and lf == "noun"
                and "معطوف" in _l17_blob(l17)
                and (not sys_case or not gs.case_bucket or gs.case_bucket == sys_case)
            ):
                pass
            else:
                return False, "family_conflict_particle"
        if gs.gram_family == "noun" and lf == "verb":
            return False, "family_conflict_noun_vs_verb"

    if gs.syntactic_role_status != "resolved" or not gs.syntactic_role:
        return False, "gold_role_unresolved"

    if gs.syntactic_role not in codes:
        return False, "role_code_mismatch"

    if gs.case_status == "resolved" and sys_case and gs.case_bucket and gs.case_bucket != sys_case:
        return False, "case_bucket_mismatch"

    return True, "structured_ok"


def _structured_partial_agreement(gs: GoldStructuredI3rab, l17: Dict[str, Any]) -> bool:
    """Case agreement without full role strict gate (diagnostic tier)."""
    sys_case = _infer_case_bucket_from_l17(l17)
    codes = _l17_role_codes(l17)
    if not (gs.case_status == "resolved" and sys_case and gs.case_bucket == sys_case):
        return False
    if gs.syntactic_role_status == "resolved" and gs.syntactic_role and gs.syntactic_role in codes:
        return False
    return bool(codes)


def _legacy_strict_structural_match_gold_vs_l17(gold_i3rab: str, l17: Dict[str, Any]) -> bool:
    """Legacy prose heuristic (Batch 28.3) — used only as fallback when structured parse fails."""
    g = _PARSER.parse(gold_i3rab)
    sys_case = _infer_case_bucket_from_l17(l17)
    role = (l17.get("syntactic_role") or "") + " " + (l17.get("governing_factor") or "")
    gold_s = _nfc(gold_i3rab)
    if g.case and sys_case and g.case == sys_case:
        return True
    strong_phrases = (
        "مفعول به",
        "مَفْعُولٌ بِهٖ",
        "فاعل",
        "فَاعِل",
        "نعت",
        "نَعْت",
        "حرف جر",
        "جار ومجرور",
        "شبه الجملة",
        "مبتدأ",
        "خبر",
    )
    for ph in strong_phrases:
        if ph in gold_s or ph.replace(" ", "") in gold_s.replace(" ", ""):
            if ph.split()[0] in role or any(
                x in role for x in ("مفعول", "فاعل", "نعت", "حرف", "جار", "شبه", "مبتدأ", "خبر")
            ):
                if g.pos == "verb" and ("فعل" in gold_s or "فِعْل" in gold_s) and (
                    "فعل" in role or "فِعْل" in role
                ):
                    return True
                if g.pos == "particle" and ("حرف" in gold_s or "حَرْف" in gold_s) and (
                    "حرف" in role or "حَرْف" in role
                ):
                    return True
                if "مفعول" in ph and "مفعول" in role:
                    return True
                if "فاعل" in ph and "فاعل" in role:
                    return True
                if "نعت" in ph and "نعت" in role:
                    return True
    return False


def _loose_structured_hint(gold_i3rab: str, l17: Dict[str, Any]) -> bool:
    """True = L11 exact text is compatible with L17 (do not reject exact L11)."""
    g = _PARSER.parse(gold_i3rab)
    sys_case = _infer_case_bucket_from_l17(l17)
    if g.case and sys_case and g.case == sys_case:
        return True
    role = (l17.get("syntactic_role") or "") + " " + (l17.get("governing_factor") or "")
    if g.pos == "verb" and ("فعل" in role or "فِعْل" in gold_i3rab):
        return True
    if g.pos == "particle" and ("حرف" in gold_i3rab or "حَرْف" in gold_i3rab):
        return True
    gs = parse_gold_i3rab_prose(gold_i3rab)
    lf = _l17_infer_family(l17)
    if gs.gram_family_status == "resolved" and lf and gs.gram_family and gs.gram_family != lf:
        if {gs.gram_family, lf} == {"noun", "verb"}:
            return False
    return True


def compare_token_conservative(
    gold_i3rab: str,
    snap: Optional[TokenAnalyzerSnapshot],
    *,
    repair_pass: int = 0,
) -> MatchDecision:
    gold_use = _collapse_ws(gold_i3rab) if repair_pass > 0 else gold_i3rab

    if snap is None:
        return MatchDecision(
            tier=ComparatorTier.MISMATCH,
            confidence=0.0,
            analyzer_source="none",
            system_i3rab_display="",
            notes="no_analyzer_snapshot",
            trace=None,
        )

    l11 = snap.l11_i3rab_text or ""
    l17 = snap.l17
    l17_auth = _l17_authoritative(snap)

    if l11:
        display = l11
    elif l17:
        display = (
            (l17.get("syntactic_role") or "").strip()
            + " | "
            + (l17.get("i3rab_case_or_mood") or "").strip()
        ).strip(" |")
    else:
        display = ""

    # --- Exact L11 vs gold (Batch 28.5: quote/space normalization + orthographic)
    if l11:
        ng = normalize_i3rab_for_exact_compare(gold_use)
        nl = normalize_i3rab_for_exact_compare(l11)
        exact_norm = ng == nl
        exact_nfc = _nfc(l11) == _nfc(gold_use)
        exact_ortho = normalize_arabic_surface(ng) == normalize_arabic_surface(nl) or (
            normalize_arabic_surface(l11) == normalize_arabic_surface(gold_use)
        )
        if exact_norm or exact_nfc or exact_ortho:
            if l17_auth and l17 and not _loose_structured_hint(gold_use, l17):
                return MatchDecision(
                    tier=ComparatorTier.MISMATCH,
                    confidence=0.0,
                    analyzer_source="L11+L17",
                    system_i3rab_display=display,
                    notes="L11_exact_but_L17_structured_mismatch",
                    trace=None,
                )
            notes = "exact_l11_vs_gold"
            conf = 0.95
            if exact_norm and not exact_nfc:
                notes = "exact_l11_vs_gold_punctuation_normalized"
            elif exact_ortho and not (exact_norm or exact_nfc):
                notes = "normalized_text_L11"
                conf = 0.88
            return MatchDecision(
                tier=ComparatorTier.EXACT_TEXT_MATCH,
                confidence=conf,
                analyzer_source="L11" if not l17_auth else "L11+L17",
                system_i3rab_display=l11,
                notes=notes,
                trace=None,
            )

    gs = effective_gold_structure_for_compare(gold_use)

    # Batch 28.4 — structured gold vs L17 (primary path for strict when L11 differs)
    if l17_auth and l17:
        ok, sreason = _structured_strict_agreement(gs, l17)
        if ok:
            tr = _structured_trace(gs, l17, {"structured_gate": "strict", "reason": sreason})
            return MatchDecision(
                tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
                confidence=min(0.92, max(float(l17.get("confidence") or 0.75), gs.parser_confidence)),
                analyzer_source="L17",
                system_i3rab_display=display,
                notes="strict_structured_gold_vs_l17",
                trace=tr,
            )
        if sreason.startswith("family_conflict") or sreason == "case_bucket_mismatch":
            tr = _structured_trace(gs, l17, {"structured_gate": "reject", "reason": sreason})
            return MatchDecision(
                tier=ComparatorTier.MISMATCH,
                confidence=0.0,
                analyzer_source="L17",
                system_i3rab_display=display,
                notes=sreason,
                trace=tr,
            )

    # Batch 28.5 — structured gold vs L11 prose (same conservative parser on both sides)
    if l11:
        ok11, r11 = structured_strict_gold_vs_l11_prose(gs, l11)
        if ok11:
            if l17_auth and l17 and not _loose_structured_hint(gold_use, l17):
                return MatchDecision(
                    tier=ComparatorTier.MISMATCH,
                    confidence=0.0,
                    analyzer_source="L11+L17",
                    system_i3rab_display=display,
                    notes="L11_structured_but_L17_conflict",
                    trace=None,
                )
            l17_for_trace = l17 or {
                "syntactic_role": "",
                "governing_factor": "",
                "i3rab_case_or_mood": "",
                "marker": "",
            }
            tr = _structured_trace(gs, l17_for_trace, {"structured_gate": "l11_struct", "reason": r11})
            return MatchDecision(
                tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
                confidence=min(0.9, max(gs.parser_confidence, 0.72)),
                analyzer_source="L11_structured",
                system_i3rab_display=l11,
                notes="strict_structured_gold_vs_l11_prose",
                trace=tr,
            )

    # Legacy strict (prose) fallback when structured parse misses a recoverable agreement
    if l17_auth and l17 and _legacy_strict_structural_match_gold_vs_l17(gold_use, l17):
        return MatchDecision(
            tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
            confidence=float(l17.get("confidence") or 0.8),
            analyzer_source="L17",
            system_i3rab_display=display,
            notes="legacy_prose_structural_fallback",
            trace=_structured_trace(gs, l17, {"structured_gate": "legacy_fallback"}),
        )

    if l17 and _structured_partial_agreement(gs, l17):
        tr = _structured_trace(gs, l17, {"structured_gate": "partial"})
        return MatchDecision(
            tier=ComparatorTier.PARTIAL_STRUCTURED_MATCH,
            confidence=0.55,
            analyzer_source="L17",
            system_i3rab_display=display,
            notes="partial_structured_match",
            trace=tr,
        )

    if l17 and _infer_case_bucket_from_l17(l17):
        g = _PARSER.parse(gold_use)
        if g.case and _infer_case_bucket_from_l17(l17) == g.case:
            return MatchDecision(
                tier=ComparatorTier.PARTIAL_STRUCTURED_MATCH,
                confidence=0.5,
                analyzer_source="L17",
                system_i3rab_display=display,
                notes="diagnostic_case_bucket_only",
                trace=_structured_trace(gs, l17, {"structured_gate": "fvafk_case_only"}),
            )

    if l11 and _strip_diacritics_ar(l11) == _strip_diacritics_ar(gold_use):
        return MatchDecision(
            tier=ComparatorTier.COARSE_MATCH,
            confidence=0.35,
            analyzer_source="L11",
            system_i3rab_display=l11,
            notes="stripped_diacritics_coarse",
            trace=None,
        )

    return MatchDecision(
        tier=ComparatorTier.MISMATCH,
        confidence=0.0,
        analyzer_source="L17" if l17 else ("L11" if l11 else "none"),
        system_i3rab_display=display,
        notes="no_match",
        trace=_structured_trace(gs, l17, {"structured_gate": "none"}) if l17 else None,
    )


def strict_acceptance_eligible(decision: MatchDecision) -> bool:
    return decision.tier in (
        ComparatorTier.EXACT_TEXT_MATCH,
        ComparatorTier.STRICT_STRUCTURAL_MATCH,
    )


def erqa_eligible(decision: MatchDecision) -> bool:
    return strict_acceptance_eligible(decision)
