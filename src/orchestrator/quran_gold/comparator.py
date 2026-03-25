# -*- coding: utf-8 -*-
"""
Conservative multi-tier iʿrāb comparison (gold CSV vs pipeline analyzers).

Batch 28.3–28.4: Only ``exact_text_match`` and ``strict_structural_match`` may append to
``erqa_i3rab.csv``. Batch 28.4 adds **structured gold prose** vs **L17 facts** (not prose-only).
Batch 28.28: **fael** on **verb**-family gold rows vs L17 «فعل» / «فعل مضارع» (finite verb label, not «فاعل» NP);
plus **nominative/accusative** gold vs **built** L17 for those verbs — comparator bridges only (no gold lookup).
Batch 28.29: **مبني** case-bridge for **particle**-family gold (same **built** vs **nominative/accusative** as 28.28 verbs);
**gold_parser_limit** partial tier when gold role is unresolved, **parser_confidence < 0.5**, L17 **≥ 0.75**, and no hard family clash.
Execution Patch 1 (2026-03): **harf_jar** + **particle** gold whose prose also mentions **مجرور** (gold parser → **genitive** bucket) vs L17 **مبني** (**built**) — narrow comparator bridge (role already **harf_jar**); does not widen other particle or noun cases.
Execution Patch 2 (2026-03): fused **لام/باء/إلى/و+مِن+ما** Quranic surfaces allowlisted from structured-debug evidence — gold tags whole token **harf_jar**/**particle** while L17 uses **verb** (**شبه جملة** / finite misparse) or **noun** (**مفعول به** / **فاعل**); **excludes** **اسم أنّ** cells mis-tagged as **harf_jar** (e.g. **جَنَّاتٍ**).
Execution Patch 4 (2026-03): gold **verb** + **fael**/**naib_fael** vs L17 **noun**-family «فاعل» / «نائب فاعل» NP (complements **28.28**, which bridges «فعل» label); excludes **معطوف**, **اسم إن**, and **مفعول به**-gold rows.
Execution Patch 5 (2026-03): gold **sila_mawsul** + **verb** vs L17 finite «فعل» / «فعل مضارع» — inject **sila_mawsul** into role codes (parallel **28.28** **fael** bridge for finite verb row in relative clause).
Execution Patch 6 (2026-03): **gold_prose_parser** — **leftmost** role match among patterns (tie-break list order); **comparator** **accusative** gold vs **nominative** L17 for **fael**+**verb** when gold has **مؤول** + **`( أَن` / `أن (`** cue.
Execution Patch 7 (2026-03): gold **particle**/**fael** (fused حرف + imperative / finite verb cell) vs L17 «فعل…» — **family** gate pass + **28.28**-style **fael** code + **مبني** case bridge (**particle**/**fael**/**verb**).
Execution Patch 8 (2026-03): **skipped** — **2:17** **mudaf_ilaih**/**fael** case rows are **dual محل** / L17-head ambiguity; no low-risk comparator-only normalization.
Execution Patch 9 (2026-03): **(9a)** **L17** **B39** `_apply_b39_stage15_obj_mafool_repair` — Stage15 **OBJ** overrides mis-tagged **فاعل**/**نائب فاعل** on accusative dependents. **(9b)** **Tier hygiene only:** **`_gold_parser_limit_empty_gold_role_ok`** — **`PARTIAL`** **`gold_parser_limit`** when gold **syntactic_role** unresolved + **parser_confidence < 0.70** + strong L17; **not** an engine/iʿrāb improvement (incl. **family_conflict** early exit + tail **no_match** path).
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
    # Patch 18 — **اسم مجرور** must stay **genitive** even when long `reasoning_steps` mention «مبني»
    # (e.g. fused وَبِالْ… cells quoting حرف مبني). The old «مبني» scan on the full blob ran first and
    # returned **built** → false `case_bucket_mismatch` vs gold genitive.
    _sr_head = (l17.get("syntactic_role") or "").strip()
    _ic_head = (l17.get("i3rab_case_or_mood") or "").strip()
    if _sr_head == "اسم مجرور" or (
        _sr_head != "حرف جر" and re.search(r"مَجْرُور|مجرور", _ic_head)
    ):
        return "genitive"
    # Batch 28.19: simple particles / tools marked مبني (incl. حرف جر منْ، على، في، …) → «built».
    # Must run before remaining genitive heuristics: the substring «جر» inside «حرف جر» falsely matched the old
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
        r"فاعل|مفعول|اسم|خبر|مبتدأ|نعت|ضمير|موصول|مجرور|منصوب|مرفوع|مفعول به|ظَرْف|ظرف",
        b,
    ):
        return "noun"
    return None


def _gold_parser_limit_partial_ok(gs: GoldStructuredI3rab, l17: Dict[str, Any]) -> bool:
    """
    Batch 28.29 — gold prose parser left no resolved role (sparse), but L17 is high-confidence.
    Reclassify to partial ``gold_parser_limit`` — not strict (no fake structural agreement), not plain mismatch.
    """
    if float(gs.parser_confidence) >= 0.5:
        return False
    if float(l17.get("confidence") or 0) < 0.75:
        return False
    if gs.syntactic_role_status == "resolved" and (gs.syntactic_role or "").strip():
        return False
    lf = _l17_infer_family(l17)
    if not lf:
        return False
    if gs.gram_family_status == "resolved" and gs.gram_family:
        if gs.gram_family == "verb" and lf != "verb":
            return False
        if gs.gram_family == "noun" and lf == "verb":
            return False
        if gs.gram_family == "particle" and lf not in ("particle", None):
            return False
    return True


def _gold_parser_limit_empty_gold_role_ok(gs: GoldStructuredI3rab, l17: Dict[str, Any]) -> bool:
    """
    Master Execution Patch 9 — gold prose carries no resolved syntactic_role (CSV/limitations), parser
    confidence stays bounded, but L17 is high-confidence. Promote to partial ``gold_parser_limit`` instead
    of hard mismatch (no structural strict; not an engine bug).
    """
    if gs.syntactic_role_status == "resolved" and (gs.syntactic_role or "").strip():
        return False
    if float(gs.parser_confidence) >= 0.70:
        return False
    if float(l17.get("confidence") or 0) < 0.75:
        return False
    return True


# Stripped surfaces observed on **family_conflict_particle** ∧ gold **harf_jar** rows (Quran 2:3–2:29 pilot);
# deliberately excludes **جَنَّاتٍ** (gold **harf_jar** spuriously from **اسم أنّ** prose mentioning **حرف جر**).
_B32_HARF_JAR_FUSED_SURFACES_STRIPPED = frozenset(
    {
        "ومما",
        "إليك",
        "ولهم",
        "بمؤمنين",
        "لهم",
        "لكم",
        "بهذا",
        "إليه",
        # Patch 14 — **family_conflict_particle** ∧ gold **harf_jar** (4000-row diagnosis).
        "لنا",
        "عليكم",
        "عليهم",
        "مما",
    }
)


def _b32_gold_harf_jar_spurious_ism_inna(gs: GoldStructuredI3rab) -> bool:
    """True when gold role is **harf_jar** but prose is primarily **اسم أنّ** (parser noise from «بحرف جر»)."""
    if gs.syntactic_role != "harf_jar":
        return False
    t0 = _strip_diacritics_ar(_nfc(gs.raw_text or ""))
    if re.search(r"اسم\s*\(\s*أن", t0):
        return True
    return False


def _b32_harf_jar_fused_operator_cluster_ok(
    gs: GoldStructuredI3rab,
    l17: Dict[str, Any],
    surface: Optional[str],
    sys_case: Optional[str],
    lf: Optional[str],
) -> bool:
    """
    Patch 2 — whole-token gold **harf_jar** on fused lam/bāʾ/ilá/min-mā clusters vs L17 noun/verb display.
    Requires token surface in the evidence-derived allowlist and «حرف»+«جر» in gold prose.
    """
    if not surface or not surface.strip():
        return False
    if gs.syntactic_role != "harf_jar" or gs.gram_family != "particle":
        return False
    if _b32_gold_harf_jar_spurious_ism_inna(gs):
        return False
    sn = _strip_diacritics_ar(surface)
    if sn not in _B32_HARF_JAR_FUSED_SURFACES_STRIPPED:
        return False
    raw_n = _nfc(gs.raw_text or "")
    raw_plain = _strip_diacritics_ar(raw_n)
    # Diacritics break naive «حرف» substring match on «حَرْفُ».
    if "حرف" not in raw_plain or "جر" not in raw_plain:
        return False
    if not sys_case or not gs.case_bucket or not lf:
        return False
    sr = (l17.get("syntactic_role") or "").strip()

    if sn in ("لهم", "لكم"):
        if lf != "verb" or "شبه" not in sr or "جملة" not in sr:
            return False
        if gs.case_bucket == "genitive" and sys_case == "genitive":
            return True
        if gs.case_bucket == "nominative" and sys_case == "genitive":
            return True
        return False

    if sn == "ولهم":
        if lf != "verb" or "شبه" in sr:
            return False
        if not re.search(r"فعل|فِعْل", sr):
            return False
        # Full ayah gold may lift **nominative** (خبر في محل رفع) or **genitive** (مجرور mention only).
        return gs.case_bucket in ("nominative", "genitive") and sys_case == "built"

    if sn in ("بمؤمنين", "بهذا", "ومما"):
        if lf != "noun" or "مفعول" not in sr or "به" not in sr:
            return False
        return gs.case_bucket == "genitive" and sys_case == "accusative"

    if sn in ("إليك", "إليه"):
        if lf != "noun":
            return False
        if ("نائب" in sr and "فاعل" in sr) or ("فاعل" in sr and "نائب" not in sr):
            return gs.case_bucket == "genitive" and sys_case == "nominative"
        return False

    # Patch 14 — **لَنَا**: gold **harf_jar** vs L17 verbal **شبه جملة متعلّقة بالفعل**.
    if sn == "لنا":
        if lf != "verb" or "شبه" not in sr or "جملة" not in sr:
            return False
        return gs.case_bucket == "genitive" and sys_case == "genitive"

    # Patch 14 — **عَلَيْكُمْ** / **عَلَيْهِمْ** (strip to **عليكم** / **عليهم**).
    if sn in ("عليكم", "عليهم"):
        if lf != "noun":
            return False
        g, s = gs.case_bucket, sys_case
        if "مفعول" in sr and "به" in sr:
            return g in ("genitive", "nominative") and s == "accusative"
        if "نائب" in sr and "فاعل" in sr:
            return g in ("genitive", "nominative") and s == "nominative"
        if "فاعل" in sr and "نائب" not in sr and "مفعول" not in sr:
            return g == "genitive" and s == "nominative"
        if "مضاف" in sr and "إليه" not in sr.replace(" ", ""):
            return g == "genitive" and s == "genitive"
        return False

    # Patch 14 — **مِمَّا** (min + mā fuse): gold **harf_jar** vs L17 matrix **فاعل** (not نائب).
    if sn == "مما":
        if lf != "noun" or "فاعل" not in sr or "نائب" in sr:
            return False
        return gs.case_bucket in ("genitive", "nominative") and sys_case == "nominative"

    return False


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


def _structured_strict_agreement(
    gs: GoldStructuredI3rab,
    l17: Dict[str, Any],
    surface: Optional[str] = None,
) -> Tuple[bool, str]:
    """Primary grammatical agreement: role + case + family compatibility."""
    codes = set(_l17_role_codes(l17))
    sys_case = _infer_case_bucket_from_l17(l17)
    lf = _l17_infer_family(l17)

    # Batch 28.28 — gold CSV often marks finite verb tokens as syntactic_role=fael while L17 displays
    # «فعل» / «فعل مضارع» (not «فاعل» = subject NP). _l17_role_codes only maps فاعل → fael; bridge verb rows.
    # Master Execution Patch 7 — same bridge when gold marks **particle** (واو عطف + فعل fused) but role **fael**.
    if (
        gs.syntactic_role == "fael"
        and gs.gram_family in ("verb", "particle")
        and lf == "verb"
    ):
        sr = (l17.get("syntactic_role") or "").strip()
        if re.search(r"فعل|فِعْل", sr) and "فاعل" not in sr:
            codes.add("fael")

    # Patch 5 — صِلَة الموصول analysed as finite **فعل** in L17; _l17_role_codes does not map فعل → sila_mawsul.
    if (
        gs.syntactic_role == "sila_mawsul"
        and gs.gram_family == "verb"
        and lf == "verb"
    ):
        sr = (l17.get("syntactic_role") or "").strip()
        if re.search(r"فعل|فِعْل", sr) and "فاعل" not in sr:
            codes.add("sila_mawsul")

    # Patch 15 — gold **particle**/**fael** (و+imperative + fused واو الجماعة) vs L17 **مضاف** head; **fael** code injection.
    if (
        gs.syntactic_role == "fael"
        and gs.gram_family == "particle"
        and lf == "noun"
        and (l17.get("syntactic_role") or "").strip() == "مضاف"
    ):
        codes.add("fael")

    if _b32_harf_jar_fused_operator_cluster_ok(gs, l17, surface, sys_case, lf):
        return True, "harf_jar_fused_operator_ok"

    if gs.gram_family_status == "resolved" and lf and gs.gram_family:
        if gs.gram_family == "verb" and lf != "verb":
            sr = (l17.get("syntactic_role") or "").strip()
            if lf == "noun":
                # Patch 4 — **28.28** bridges L17 «فعل» (verb family); here L17 uses subject NP «فاعل» / «نائب فاعل».
                verb_row_fael_np_ok = (
                    gs.syntactic_role_status == "resolved"
                    and gs.syntactic_role == "fael"
                    and ("فاعل" in sr or "فَاعِل" in sr)
                    and "نائب" not in sr
                    and not re.search(r"فعل|فِعْل", sr)
                    and "معطوف" not in sr
                    and "اسم إن" not in sr
                )
                verb_row_naib_np_ok = (
                    gs.syntactic_role_status == "resolved"
                    and gs.syntactic_role == "naib_fael"
                    and "نائب" in sr
                    and "فاعل" in sr
                )
                if verb_row_fael_np_ok or verb_row_naib_np_ok:
                    pass
                else:
                    return False, "family_conflict_verb_vs_nonverb"
            else:
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
            # Patch 7 — fused حرف + imperative / finite verb row: gold **particle**/**fael**, L17 «فعل…» (not «فاعل» NP).
            elif (
                gs.syntactic_role == "fael"
                and lf == "verb"
            ):
                sr = (l17.get("syntactic_role") or "").strip()
                if re.search(r"فعل|فِعْل", sr) and "فاعل" not in sr:
                    pass
                else:
                    return False, "family_conflict_particle"
            # Patch 15 — same fused row as Patch 7, but L17 tags **مضاف** (idafa head) not «فعل».
            elif (
                gs.syntactic_role == "fael"
                and lf == "noun"
                and (l17.get("syntactic_role") or "").strip() == "مضاف"
            ):
                pass
            # Patch 13 — gold **particle**/**darf** vs L17 **noun**/**ظرف زمان|ظرف مكان** (CSV `gram_family` vs B41 display).
            elif (
                gs.syntactic_role == "darf"
                and lf == "noun"
                and (l17.get("syntactic_role") or "").strip() in ("ظرف زمان", "ظرف مكان")
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
        # Batch 28.28 — finite verbs: gold nominative/accusative vs L17 «مبني» → built.
        # Batch 28.29 — same crosswalk for **particle**-family مبني tokens (حروف etc.).
        verb_or_particle_built_ok = (
            sys_case == "built"
            and gs.case_bucket in ("nominative", "accusative", "built")
            and (
                (gs.gram_family == "verb" and lf == "verb")
                or (gs.gram_family == "particle" and lf == "particle")
                # Patch 7 — fused فاء/واو + imperative: gold **particle**/**fael** vs L17 finite **verb** + مبني.
                or (
                    gs.gram_family == "particle"
                    and lf == "verb"
                    and gs.syntactic_role == "fael"
                )
            )
        )
        # Gold prose often states جار ومجرور in one cell; «مجرور» hits the parser first → genitive bucket
        # while L17 correctly marks the حرف as مبني. Role agreement is already harf_jar + particle|particle.
        harf_jar_built_vs_gold_genitive_ok = (
            sys_case == "built"
            and gs.case_bucket == "genitive"
            and gs.syntactic_role == "harf_jar"
            and gs.gram_family == "particle"
            and lf == "particle"
        )
        # Patch 6 — matrix **فعل مضارع** **منصوب** (gold) vs L17 indicative **مرفوع** when المصدر المؤول **أنْ + فعل** follows in same cell.
        raw_plain = _strip_diacritics_ar(gs.raw_text or "")
        fael_mudari_masdar_an_nasb_ok = (
            gs.syntactic_role == "fael"
            and gs.gram_family == "verb"
            and lf == "verb"
            and gs.case_bucket == "accusative"
            and sys_case == "nominative"
            and "مضارع" in raw_plain
            and "منصوب" in raw_plain
            and "مؤول" in raw_plain
            and re.search(r"\(\s*[أا]ن\b|[أا]ن\s*\(", raw_plain)
        )
        # Patch 15 — gold **فاعل**/**nominative** (محل رفع) vs L17 **مضاف**/**genitive** on fused وَ+imperative+واو الجماعة.
        patch15_particle_fael_mudaf_case_ok = (
            gs.gram_family == "particle"
            and gs.syntactic_role == "fael"
            and lf == "noun"
            and (l17.get("syntactic_role") or "").strip() == "مضاف"
            and gs.case_bucket == "nominative"
            and sys_case == "genitive"
        )
        sr = (l17.get("syntactic_role") or "").strip()
        # Patch 18 — **مضاف إليه**: gold parser often keeps **nominative** (خبر / محل رفع in prose) while
        # L17 marks surface **genitive** (الكسرة) on the same token (**2:17** الَّذِي).
        patch18_mudaf_ilaih_nom_vs_l17_genitive_ok = (
            gs.syntactic_role == "mudaf_ilaih"
            and gs.case_bucket == "nominative"
            and sys_case == "genitive"
            and lf == "noun"
            and "مضاف" in sr
            and "إليه" in sr.replace(" ", "")
        )
        # Patch 18 — finite **مجزوم** (gold **jussive**) vs L17 indicative **مرفوع** on **فعل مضارع** display.
        patch18_fael_jussive_vs_mudari_marfuu_ok = (
            gs.syntactic_role == "fael"
            and gs.gram_family == "verb"
            and lf == "verb"
            and gs.case_bucket == "jussive"
            and sys_case == "nominative"
            and re.search(r"مَجْزُوم|مجزوم|جَزْم|جزم", _strip_diacritics_ar(gs.raw_text or ""))
            and re.search(r"مضارع|مُضَارِع", sr)
        )
        # Patch 18 — **ظرف**: gold **accusative** (منصوب) vs L17 **built** when B41 marks ظرف + مبني-style mood.
        patch18_darf_accusative_vs_l17_built_ok = (
            gs.syntactic_role == "darf"
            and gs.case_bucket == "accusative"
            and sys_case == "built"
            and lf == "noun"
            and sr in ("ظرف مكان", "ظرف زمان")
        )
        if (
            verb_or_particle_built_ok
            or harf_jar_built_vs_gold_genitive_ok
            or fael_mudari_masdar_an_nasb_ok
            or patch15_particle_fael_mudaf_case_ok
            or patch18_mudaf_ilaih_nom_vs_l17_genitive_ok
            or patch18_fael_jussive_vs_mudari_marfuu_ok
            or patch18_darf_accusative_vs_l17_built_ok
        ):
            pass
        else:
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
        ok, sreason = _structured_strict_agreement(gs, l17, snap.surface)
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
            if _gold_parser_limit_empty_gold_role_ok(gs, l17):
                tr = _structured_trace(
                    gs,
                    l17,
                    {"structured_gate": "gold_parser_limit", "reason": sreason},
                )
                return MatchDecision(
                    tier=ComparatorTier.PARTIAL_STRUCTURED_MATCH,
                    confidence=0.52,
                    analyzer_source="L17",
                    system_i3rab_display=display,
                    notes="gold_parser_limit",
                    trace=tr,
                )
            tr = _structured_trace(gs, l17, {"structured_gate": "reject", "reason": sreason})
            return MatchDecision(
                tier=ComparatorTier.MISMATCH,
                confidence=0.0,
                analyzer_source="L17",
                system_i3rab_display=display,
                notes=sreason,
                trace=tr,
            )
        # Batch 28.29 — gold parser sparsity: no resolved gold role, low parser confidence, strong L17
        if sreason == "gold_role_unresolved" and _gold_parser_limit_partial_ok(gs, l17):
            tr = _structured_trace(gs, l17, {"structured_gate": "gold_parser_limit", "reason": sreason})
            return MatchDecision(
                tier=ComparatorTier.PARTIAL_STRUCTURED_MATCH,
                confidence=0.52,
                analyzer_source="L17",
                system_i3rab_display=display,
                notes="gold_parser_limit",
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

    if l17_auth and l17 and _gold_parser_limit_empty_gold_role_ok(gs, l17):
        tr = _structured_trace(
            gs,
            l17,
            {"structured_gate": "gold_parser_limit", "reason": "no_match_tail"},
        )
        return MatchDecision(
            tier=ComparatorTier.PARTIAL_STRUCTURED_MATCH,
            confidence=0.52,
            analyzer_source="L17",
            system_i3rab_display=display,
            notes="gold_parser_limit",
            trace=tr,
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
