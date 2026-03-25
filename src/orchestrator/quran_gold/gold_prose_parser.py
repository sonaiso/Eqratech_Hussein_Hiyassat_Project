# -*- coding: utf-8 -*-
"""
Deterministic conservative parser for gold iʿrāb prose strings (quran_i3rab.csv).

Does not invent facts: unknown fields stay ``absent`` with low confidence.
"""

from __future__ import annotations

import re
import unicodedata
from typing import List, Optional, Tuple

from orchestrator.quran_gold.gold_structured import GoldStructuredI3rab


def _nfc(s: str) -> str:
    return unicodedata.normalize("NFC", (s or "").strip())


def _strip_diacritics(s: str) -> str:
    return re.sub(r"[\u064B-\u065F\u0670\u0640]", "", _nfc(s))


def parse_gold_i3rab_prose(text: str) -> GoldStructuredI3rab:
    t = _nfc(text)
    if not t:
        return GoldStructuredI3rab(
            raw_text=text or "",
            gram_family=None,
            gram_family_status="absent",
            syntactic_role=None,
            syntactic_role_status="absent",
            case_bucket=None,
            case_status="absent",
            marker=None,
            marker_status="absent",
            parser_confidence=0.0,
            limitations=("empty",),
        )

    limitations: List[str] = []
    t_nd = _strip_diacritics(t)

    # --- grammatical family
    gram_family: Optional[str] = None
    fam_stat = "absent"
    if re.search(r"فِعْلٌ\s*مَاض|فِعْلٌ\s*مُضَار|فِعْلٌ\s*أَمْر|فعل\s*ماض|فعل\s*مضار|فعل\s*أمر|فعل\s*الشرط", t):
        gram_family = "verb"
        fam_stat = "resolved"
    elif re.search(
        r"حَرْفٌ|حَرْفُ\s*(عَطْف|نَصْب|جَر|استئناف)|حَرْفُ\s*جَر|حرف\s*عطف|حرف\s*نصب|حرف\s*جر",
        t,
    ) or re.search(
        r"حَرْفٌ|حَرْفُ\s*(عَطْف|نَصْب|جَر|استئناف)|حَرْفُ\s*جَر|حرف\s*عطف|حرف\s*نصب|حرف\s*جر",
        t_nd,
    ):
        gram_family = "particle"
        fam_stat = "resolved"
    elif re.search(r"ضَمِيرٌ|اسْمٌ|اسمٌ|فَاعِلٌ|مَفْعُولٌ|مُبْتَدَأ|خَبَر|نَعْتٌ|مَجْرُور|مَرْفُوع|مَنْصُوب", t):
        gram_family = "noun"
        fam_stat = "candidate"
    elif re.search(r"حُرُوفٌ\s*مُقَطَّع|مُقَطَّعَةٌ|مُقَطَّعَة|مقطعة", t) or re.search(
        r"حُرُوف\s*مقطع|مقطعة", t_nd
    ):
        # Disconnected letters (Alif-Lam-Mim, etc.) — Quranic gold phrasing
        gram_family = "particle"
        fam_stat = "resolved"

    # --- syntactic role (longer phrases first in list; **leftmost match in text** wins)
    role: Optional[str] = None
    role_stat = "absent"
    # List order is tie-break when two patterns match at the same index (rare).
    # Leftmost span beats later ones so: (1) leading «حَرْفُ جَرٍّ» wins over a later «شِبْهُ الْجُمْلَةِ»
    # in compound cells; (2) matrix «فَاعِلٌ» before a trailing «بِحَرْفِ جَرٍّ مَحْذُوفٍ» inside المصدر
    # المؤول still wins (Master Execution Patch 6).
    _pairs: List[Tuple[str, str]] = [
        ("muqatta_huruf", r"حُرُوفٌ\s*مُقَطَّع|مُقَطَّعَةٌ|مُقَطَّعَة|مقطعة|حُرُوف\s*مقطع"),
        ("naib_fael", r"نائب\s*فاعل|نَائِب\s*فَاعِل"),
        ("harf_mabni", r"حَرْفٌ\s*مَبْنِي|حرف\s*مبني"),
        ("harf_jar", r"حَرْفُ\s*جَرّ|حرف\s*جر"),
        ("ism_majrur", r"اسْمٌ\s*مَجْرُور|اسم\s*مجرور|اسْمٌ\s*مَجْرُورٌ"),
        ("jar_majrur", r"جَارٌ\s*وَمَجْرُور|جار\s*ومجرور"),
        ("ism_inna", r"اسْمُ\s*إِنَّ|اسم\s*إن"),
        ("khabar_inna", r"خَبَرُ\s*إِنَّ|خبر\s*إن"),
        ("sila_mawsul", r"صِلَة|صلة\s*الموصول|الْمَوْصُول"),
        ("shibh_jumla", r"شِبْهُ\s*الْجُمْلَة|شبه\s*الجملة"),
        ("mudaf_ilaih", r"مُضَافٌ\s*إِلَيْهِ|مضاف\s*إليه"),
        ("mafool_bih", r"مَفْعُولٌ\s*بِه|مفعول\s*به|مَفْعُول\s*بِه"),
        ("mafool_mutlaq", r"مَفْعُولٌ\s*مُطْلَق|مفعول\s*مطلق"),
        ("mubtada", r"مُبْتَدَأٌ|مبتدأ"),
        ("khabar", r"خَبَرٌ|خبر"),
        ("naat", r"نَعْتٌ|نعت"),
        ("darf", r"ظَرْف|ظرف"),
        ("fael", r"فَاعِلٌ|فاعل"),
    ]
    candidates: List[Tuple[int, int, str]] = []
    for i, (key, pat) in enumerate(_pairs):
        m = re.search(pat, t) or re.search(pat, t_nd)
        if not m:
            continue
        if key == "fael" and ("نائب" in t_nd or "نَائِب" in t):
            continue
        candidates.append((m.start(), i, key))
    if candidates:
        candidates.sort(key=lambda x: (x[0], x[1]))
        role = candidates[0][2]
        role_stat = "resolved"

    # --- case bucket (prefer explicit مَجْرُور before other محل clauses in long prose)
    case_b: Optional[str] = None
    case_stat = "absent"
    if re.search(r"مَجْرُور|مجرور", t) or re.search(r"مَجْرُور|مجرور", t_nd):
        case_b, case_stat = "genitive", "resolved"
    else:
        for label, pat in [
            ("nominative", r"مَرْفُوع|مرفوع|مَحَلِّ\s*رَفْع|محل\s*رفع"),
            ("accusative", r"مَنْصُوب|منصوب|مَحَلِّ\s*نَصْب|محل\s*نصب"),
            ("genitive", r"مَحَلِّ\s*جَرّ|محل\s*جر"),
            ("jussive", r"مَجْزُوم|مجزوم|مَحَلِّ\s*جَزْم"),
            ("built", r"مَبْنِيّ|مبني"),
        ]:
            if re.search(pat, t) or re.search(pat, t_nd):
                case_b = label
                case_stat = "resolved"
                break

    # Hurūf muqaṭṭaʿa are treated as مبني in school grammar; gold prose may omit «مبني».
    if role == "muqatta_huruf" and case_stat == "absent":
        case_b, case_stat = "built", "resolved"

    # --- marker
    marker: Optional[str] = None
    mstat = "absent"
    if re.search(r"الضَّمَّة|الضمة", t):
        marker, mstat = "damma", "resolved"
    elif re.search(r"الْفَتْحَة|الفتحة", t):
        marker, mstat = "fatha", "resolved"
    elif re.search(r"الْكَسْرَة|الكسرة", t):
        marker, mstat = "kasra", "resolved"

    conf = 0.35
    if role_stat == "resolved":
        conf += 0.35
    if case_stat == "resolved":
        conf += 0.15
    if fam_stat == "resolved":
        conf += 0.1
    conf = min(0.95, conf)
    if role_stat == "absent" and case_stat == "absent":
        limitations.append("sparse_role_and_case")
        conf = min(conf, 0.45)

    return GoldStructuredI3rab(
        raw_text=text,
        gram_family=gram_family,
        gram_family_status=fam_stat,
        syntactic_role=role,
        syntactic_role_status=role_stat,
        case_bucket=case_b,
        case_status=case_stat,
        marker=marker,
        marker_status=mstat,
        parser_confidence=round(conf, 3),
        limitations=tuple(limitations),
    )


_HEAD_MAX = 280


def effective_gold_structure_for_compare(text: str) -> GoldStructuredI3rab:
    """
    Prefer the first ~sentence of long gold prose when it carries a clearer
    resolved role than the full string (Batch 28.5). Conservative: only when
    head has a resolved role and beats or replaces an ambiguous full parse.

    If long gold begins with حرف جر analysis but later mentions ``مَفْعُولٌ بِه``
    (شبه جملة), prefer the ``اسْمٌ مَجْرُور`` block that matches short L11.
    """
    t = _nfc(text)
    if not t:
        return parse_gold_i3rab_prose(text)

    m_ism = re.search(r"اسْمٌ\s*مَجْرُور|اسم\s*مجرور", t)
    m_maf = re.search(r"مَفْعُولٌ\s*بِه|مفعول\s*به", t)
    if m_ism and (m_maf is None or m_ism.start() < m_maf.start()) and len(t) > 100:
        lo = max(0, m_ism.start() - 24)
        hi = min(len(t), m_ism.end() + 160)
        sn = parse_gold_i3rab_prose(t[lo:hi])
        if sn.syntactic_role == "ism_majrur" and sn.syntactic_role_status == "resolved":
            return sn

    if len(t) <= _HEAD_MAX:
        return parse_gold_i3rab_prose(text)
    full = parse_gold_i3rab_prose(t)
    head = parse_gold_i3rab_prose(t[:_HEAD_MAX])
    if head.syntactic_role_status == "resolved":
        if full.syntactic_role_status != "resolved":
            return head
        if head.parser_confidence >= full.parser_confidence + 0.02:
            return head
    return full
