# -*- coding: utf-8 -*-
"""
Batch 28.8 — rank blocked pattern families from truth_audit / discovery CSVs (tooling only).
"""

from __future__ import annotations

import csv
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List


def _norm_gold_snip(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "")[:400])


def classify_family(row: Dict[str, Any]) -> str:
    """Map a truth_audit row to a coarse pattern family label."""
    ab = (row.get("audit_bucket") or "").strip()
    g = _norm_gold_snip(row.get("gold_i3rab") or "")
    if ab == "GOLD_LONG_PROSE_L11_CONFLICT":
        return "true_gold_l11_conflict"
    if "حَرْفُ جَرّ" in g or "حرف جر" in g or "حَرْفُ جر" in g:
        return "harf_jar_mabni"
    if "وَاو" in g or "الْوَاوُ" in g or "حَرْفُ عَطْف" in g:
        return "waw_fa_atf"
    if "اسْمٌ مَوْصُول" in g or "موصول" in g or "الَّذِين" in g or "الَّذِي" in g:
        return "ism_mawsul"
    if "ضَمِير" in g and "مَبْنِي" in g:
        return "damir_mabni"
    if "فِعْل" in g and "أَمْر" in g:
        return "fi3l_amr"
    if ab == "GOLD_LONG_PROSE_L17_UNAVAILABLE":
        return "l17_unavailable_other"
    if ab == "ALIGNMENT_OK_BUT_COMPARATOR_REJECTED":
        return "comparator_rejected_other"
    return "other"


def rank_from_discovery_rows_csv(path: Path, *, blocked_only: bool = True) -> Dict[str, Any]:
    """Rank families from discovery_rows (richer than a tiny truth_audit snapshot)."""
    rows: List[Dict[str, Any]] = []
    if not path.is_file():
        return {"error": f"missing_file:{path}", "families": {}, "rows": 0, "blocked_only": blocked_only}
    with open(path, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    fam_counts: Counter[str] = Counter()
    ayah_by_fam: Dict[str, set] = {}
    for r in rows:
        if blocked_only:
            db = (r.get("discovery_bucket") or "").strip()
            req = (r.get("requires_l17_core") or "").strip().lower()
            if db != "blocked_by_l17_or_core_analysis" and req != "true":
                continue
        fam = classify_family(r)
        fam_counts[fam] += 1
        try:
            k = f'{int(r["surah"])}:{int(r["ayah"])}'
        except (KeyError, ValueError):
            continue
        ayah_by_fam.setdefault(fam, set()).add(k)
    ranked = sorted(fam_counts.items(), key=lambda x: (-x[1], x[0]))
    return {
        "rows": sum(fam_counts.values()),
        "blocked_only": blocked_only,
        "ranked_families": [
            {"family": k, "row_count": v, "ayah_count": len(ayah_by_fam.get(k, set()))} for k, v in ranked
        ],
    }


def rank_from_truth_audit_csv(path: Path) -> Dict[str, Any]:
    rows: List[Dict[str, Any]] = []
    if not path.is_file():
        return {"error": f"missing_file:{path}", "families": {}, "rows": 0}
    with open(path, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    fam_counts: Counter[str] = Counter()
    ayah_by_fam: Dict[str, set] = {}
    for r in rows:
        fam = classify_family(r)
        fam_counts[fam] += 1
        try:
            k = f'{int(r["surah"])}:{int(r["ayah"])}'
        except (KeyError, ValueError):
            continue
        ayah_by_fam.setdefault(fam, set()).add(k)
    ranked = sorted(fam_counts.items(), key=lambda x: (-x[1], x[0]))
    return {
        "rows": len(rows),
        "ranked_families": [{"family": k, "row_count": v, "ayah_count": len(ayah_by_fam.get(k, set()))} for k, v in ranked],
    }


def build_pattern_ranking_doc(repo_data: Path) -> Dict[str, Any]:
    ta = repo_data / "quran_i3rab_truth_audit.csv"
    dr = repo_data / "quran_i3rab_discovery_rows.csv"
    base_truth = rank_from_truth_audit_csv(ta)
    base_discovery = rank_from_discovery_rows_csv(dr, blocked_only=True)
    # Prefer discovery-based ranking when it has evidence; keep truth_audit as secondary.
    base = base_discovery if (base_discovery.get("rows") or 0) > 0 else base_truth
    selected = [
        "harf_jar_mabni",
        "waw_fa_atf",
        "ism_mawsul",
    ]
    skipped = [
        {"family": "true_gold_l11_conflict", "reason": "gold vs L11 conflict — out of scope for forced fixes in 28.8"},
        {"family": "damir_mabni", "reason": "pronoun resolution deferred — needs broader model"},
        {"family": "fi3l_amr", "reason": "imperative/dua verbs deferred in this batch"},
    ]
    return {
        "batch": "28.8",
        "inputs": {"truth_audit": str(ta), "discovery_rows": str(dr)},
        "summary_truth_audit_all_rows": base_truth,
        "summary_discovery_blocked_l17_core_rows": base_discovery,
        "summary": base,
        "selected_families_for_implementation": selected,
        "skipped_families": skipped,
        "notes": (
            "Ranked families: from discovery_rows where discovery_bucket=blocked_by_l17_or_core_analysis "
            "or requires_l17_core=true; else from truth_audit. L17 Batch 28.8 rules: harf jar (fused surface), "
            "wa/fa atf particles, ism mawsul surfaces."
        ),
    }


def write_pattern_ranking_json(out_path: Path, repo_root: Path) -> None:
    doc = build_pattern_ranking_doc(repo_root / "data")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, ensure_ascii=False, indent=2), encoding="utf-8")
