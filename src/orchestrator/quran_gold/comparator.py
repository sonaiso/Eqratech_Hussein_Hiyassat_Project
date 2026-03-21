# -*- coding: utf-8 -*-
"""
Conservative multi-level iʿrāb comparison (gold CSV vs pipeline analyzers).

Levels 1–3 may promote a row to **erqa** (cumulative). Levels 4–5 are diagnostic only.
False positives are worse than false negatives.
"""

from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Optional, Tuple

from fvafk.c2b.evaluation.i3rab_loader import I3rabParser

from orchestrator.quran_gold.analyzer_extract import L17_MIN_CONF_CANDIDATE, TokenAnalyzerSnapshot
from orchestrator.quran_gold.alignment import normalize_arabic_surface

_PARSER = I3rabParser()


class MatchLevel(str, Enum):
    EXACT_TEXT = "exact_text_match"
    NORMALIZED_TEXT = "normalized_text_match"
    STRUCTURED_ROLE = "structured_role_match"
    STRUCTURED_CASE_MARKER = "structured_case_marker_match"
    PARTIAL_SEMANTIC = "partial_semantic_match"
    NONE = "none"


@dataclass(frozen=True)
class MatchDecision:
    level: MatchLevel
    confidence: float
    analyzer_source: str
    system_i3rab_display: str
    notes: str


def _nfc(s: str) -> str:
    return unicodedata.normalize("NFC", (s or "").strip())


def _strip_diacritics_ar(s: str) -> str:
    """Remove Arabic diacritics for loose diagnostic only (level 4–5)."""
    if not s:
        return ""
    # Combining marks in Arabic block
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
    if re.search(r"مَرْفُوع|مرفوع|رفع", blob):
        return "nominative"
    if re.search(r"مَنْصُوب|منصوب|نَصْب|نصب", blob):
        return "accusative"
    if re.search(r"مَجْرُور|مجرور|جَرّ|جر", blob):
        return "genitive"
    if re.search(r"مَجْزُوم|مجزوم|جَزْم|جزم", blob):
        return "jussive"
    return None


def _structured_role_match_gold_vs_l17(gold_i3rab: str, l17: Dict[str, Any]) -> bool:
    """Conservative: gold parser case vs L17-derived case bucket."""
    g = _PARSER.parse(gold_i3rab)
    sys_case = _infer_case_bucket_from_l17(l17)
    if g.case and sys_case and g.case == sys_case:
        return True
    # POS hint: both hint noun/verb/particle
    role = (l17.get("syntactic_role") or "") + " " + (l17.get("governing_factor") or "")
    if g.pos == "verb" and ("فعل" in role or "فِعْل" in gold_i3rab):
        return True
    if g.pos == "particle" and ("حرف" in gold_i3rab or "حَرْف" in gold_i3rab):
        return True
    return False


def compare_token_conservative(
    gold_i3rab: str,
    snap: Optional[TokenAnalyzerSnapshot],
) -> MatchDecision:
    """
    Return best match level. Erqa-eligible: levels 1–3 only when rules satisfied.
    """
    if snap is None:
        return MatchDecision(
            level=MatchLevel.NONE,
            confidence=0.0,
            analyzer_source="none",
            system_i3rab_display="",
            notes="no_analyzer_snapshot",
        )

    l11 = snap.l11_i3rab_text or ""
    l17 = snap.l17
    l17_auth = _l17_authoritative(snap)

    # Display string: prefer L11 prose when present (closest to gold style), else L17 fields
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

    # Level 1 — exact (L11 text only; gold is school prose)
    if l11 and _nfc(l11) == _nfc(gold_i3rab):
        if l17_auth and l17 and not _structured_role_match_gold_vs_l17(gold_i3rab, l17):
            return MatchDecision(
                level=MatchLevel.NONE,
                confidence=0.0,
                analyzer_source="L11+L17",
                system_i3rab_display=display,
                notes="L11_exact_but_L17_structured_mismatch",
            )
        return MatchDecision(
            level=MatchLevel.EXACT_TEXT,
            confidence=0.95,
            analyzer_source="L11" if not l17_auth else "L11+L17",
            system_i3rab_display=l11,
            notes="exact_l11_vs_gold",
        )

    # Level 2 — normalized orthography on L11
    if l11 and normalize_arabic_surface(l11) == normalize_arabic_surface(gold_i3rab):
        if l17_auth and l17 and not _structured_role_match_gold_vs_l17(gold_i3rab, l17):
            return MatchDecision(
                level=MatchLevel.NONE,
                confidence=0.0,
                analyzer_source="L11+L17",
                system_i3rab_display=display,
                notes="normalized_L11_but_L17_conflict",
            )
        return MatchDecision(
            level=MatchLevel.NORMALIZED_TEXT,
            confidence=0.88,
            analyzer_source="L11",
            system_i3rab_display=l11,
            notes="normalized_text_L11",
        )

    # Level 3 — structured (L17 must be authoritative)
    if l17_auth and l17 and _structured_role_match_gold_vs_l17(gold_i3rab, l17):
        return MatchDecision(
            level=MatchLevel.STRUCTURED_ROLE,
            confidence=float(l17.get("confidence") or 0.8),
            analyzer_source="L17",
            system_i3rab_display=display,
            notes="structured_case_pos_gold_vs_L17",
        )

    # Level 4 — case/marker diagnostic (not erqa)
    if l17 and _infer_case_bucket_from_l17(l17):
        g = _PARSER.parse(gold_i3rab)
        if g.case and _infer_case_bucket_from_l17(l17) == g.case:
            return MatchDecision(
                level=MatchLevel.STRUCTURED_CASE_MARKER,
                confidence=0.5,
                analyzer_source="L17",
                system_i3rab_display=display,
                notes="diagnostic_case_only",
            )

    # Level 5 — very loose (diagnostic)
    if l11 and _strip_diacritics_ar(l11) == _strip_diacritics_ar(gold_i3rab):
        return MatchDecision(
            level=MatchLevel.PARTIAL_SEMANTIC,
            confidence=0.35,
            analyzer_source="L11",
            system_i3rab_display=l11,
            notes="stripped_diacritics_match_diagnostic",
        )

    return MatchDecision(
        level=MatchLevel.NONE,
        confidence=0.0,
        analyzer_source="L17" if l17 else ("L11" if l11 else "none"),
        system_i3rab_display=display,
        notes="no_match",
    )


def erqa_eligible(decision: MatchDecision) -> bool:
    return decision.level in (
        MatchLevel.EXACT_TEXT,
        MatchLevel.NORMALIZED_TEXT,
        MatchLevel.STRUCTURED_ROLE,
    )
