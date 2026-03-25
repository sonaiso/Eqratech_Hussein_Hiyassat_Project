#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Batch 28.23V — verify Stage15 SUBJ/OBJ attachment on gold mafool_bih rows (production pipeline).

Reads data/quran_i3rab.csv only (gold_csv); does not use quran-uthmani.txt.
No grammar changes; measurement / reporting only.

Usage:
  PYTHONPATH=src python3 scripts/audit_b28_23v_mafool_stage15.py --max-rows 494
  PYTHONPATH=src python3 scripts/audit_b28_23v_mafool_stage15.py --max-rows 2000
  PYTHONPATH=src python3 scripts/audit_b28_23v_mafool_stage15.py --all-mafool-bih-ayahs --max-ayahs 400
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

# Vendored from `dependency_syntax.builder` so this script can run against an older
# `builder.py` checkout (pre–28.23) without ImportError while still scoring the same
# accusative-surface proxy used in Batch 28.23 analysis.
def _normalize_surface_audit(s: str) -> str:
    if not s or not isinstance(s, str):
        return ""
    result = []
    for c in (s or "").strip():
        if "\u064b" <= c <= "\u0652" or c == "\u0670":
            continue
        result.append(c)
    return "".join(result).strip()


def _surface_accusative_object_likely(surface: str) -> bool:
    raw = (surface or "").strip()
    if not raw:
        return False
    if "\u064b" in raw or raw.endswith(("ًا", "اً")):
        return True
    n = _normalize_surface_audit(raw)
    if len(n) >= 4 and (n.startswith("ال") or n.startswith("وال") or n.startswith("فال")):
        tail = raw[-6:] if len(raw) >= 6 else raw
        tail3 = raw[-3:] if len(raw) >= 3 else raw
        if "\u064f" in tail3:
            return False
        if "\u064e" in tail and "\u064c" not in raw:
            return True
    return False


from orchestrator.pipeline_orchestrator import run_pipeline  # noqa: E402
from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_gold_rows  # noqa: E402
from orchestrator.quran_gold.gold_prose_parser import parse_gold_i3rab_prose  # noqa: E402
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows  # noqa: E402


def _gold_rows_for_ayah(indexed: list, surah: int, ayah: int) -> list:
    cands = [r for r in indexed if r.surah == surah and r.ayah == ayah]
    cands.sort(key=lambda r: r.index_in_ayah)
    return cands


def _relation_for_token(dependency_links: list, token_idx: int) -> str | None:
    tid = str(token_idx)
    for lk in dependency_links or []:
        if str(lk.get("dependent_id")) != tid:
            continue
        rel = (lk.get("relation") or "").strip()
        if rel in ("SUBJ", "OBJ", "NAIB_SUBJ"):
            return rel
    return None


def _ayahs_in_row_window(indexed: list, max_rows: int | None) -> tuple[list[tuple[int, int]], list]:
    """First `max_rows` gold rows (CSV order); return unique ayahs in visit order + row slice."""
    if max_rows is None:
        rows = list(indexed)
    else:
        rows = indexed[: max(0, int(max_rows))]
    seen: set[tuple[int, int]] = set()
    ayahs: list[tuple[int, int]] = []
    for gr in rows:
        k = (gr.surah, gr.ayah)
        if k not in seen:
            seen.add(k)
            ayahs.append(k)
    return ayahs, rows


def _all_ayahs_with_mafool_bih(indexed: list) -> list[tuple[int, int]]:
    seen: set[tuple[int, int]] = set()
    out: list[tuple[int, int]] = []
    for gr in indexed:
        gs = parse_gold_i3rab_prose((gr.i3rab or "").strip())
        if (gs.syntactic_role or "").strip() != "mafool_bih":
            continue
        k = (gr.surah, gr.ayah)
        if k not in seen:
            seen.add(k)
            out.append(k)
    return out


def audit_window(
    indexed: list,
    row_slice: list,
    label: str,
) -> dict:
    """Run pipeline once per ayah; tally Stage15 core relation on gold mafool_bih tokens in row_slice."""
    ayahs_ordered: list[tuple[int, int]] = []
    seen_a: set[tuple[int, int]] = set()
    for gr in row_slice:
        k = (gr.surah, gr.ayah)
        if k not in seen_a:
            seen_a.add(k)
            ayahs_ordered.append(k)

    mafool_rows = []
    for gr in row_slice:
        gs = parse_gold_i3rab_prose((gr.i3rab or "").strip())
        if (gs.syntactic_role or "").strip() != "mafool_bih":
            continue
        mafool_rows.append(gr)

    tallies = Counter()
    acc_cue_subj = 0
    acc_cue_obj = 0
    acc_cue_other = 0
    cache: dict[tuple[int, int], list] = {}

    for surah, ayah in ayahs_ordered:
        if (surah, ayah) not in cache:
            rows_ayah = _gold_rows_for_ayah(indexed, surah, ayah)
            text = reconstruct_ayah_text_from_gold_rows(rows_ayah)
            if not text.strip():
                cache[(surah, ayah)] = []
                continue
            try:
                r = run_pipeline(text)
            except Exception:
                cache[(surah, ayah)] = []
                continue
            dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
            cache[(surah, ayah)] = dsb.get("dependency_links") or []

    # Evaluate mafool_bih rows in this window
    for gr in mafool_rows:
        if (gr.surah, gr.ayah) not in set(ayahs_ordered):
            continue
        links = cache.get((gr.surah, gr.ayah))
        if links is None:
            continue
        rel = _relation_for_token(links, gr.index_in_ayah)
        key = rel or "none_or_other"
        tallies[key] += 1
        surf = (gr.word or "").strip()
        acc = _surface_accusative_object_likely(surf)
        if acc:
            if rel == "SUBJ":
                acc_cue_subj += 1
            elif rel == "OBJ":
                acc_cue_obj += 1
            else:
                acc_cue_other += 1

    return {
        "label": label,
        "max_rows_in_window": len(row_slice),
        "ayahs_visited": len(ayahs_ordered),
        "mafool_bih_rows_in_window": len(mafool_rows),
        "mafool_bih_rows_audited_in_loaded_ayahs": sum(tallies.values()),
        "stage15_relation_tally": dict(tallies),
        "accusative_cue_mafool_SUBJ": acc_cue_subj,
        "accusative_cue_mafool_OBJ": acc_cue_obj,
        "accusative_cue_mafool_other_or_none": acc_cue_other,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Batch 28.23V Stage15 mafool_bih attachment audit")
    ap.add_argument("--gold", type=Path, default=ROOT / "data" / "quran_i3rab.csv")
    ap.add_argument("--max-rows", type=int, default=None, help="First N CSV rows (same cap as comparison --max-rows)")
    ap.add_argument("--all-mafool-bih-ayahs", action="store_true", help="Visit every ayah that contains a mafool_bih row (full CSV)")
    ap.add_argument("--max-ayahs", type=int, default=None, help="Cap ayahs visited (with --all-mafool-bih-ayahs or large windows)")
    args = ap.parse_args()

    indexed = _read_gold_rows(str(args.gold.resolve()))
    max_ayahs = args.max_ayahs

    results: list[dict] = []

    if args.all_mafool_bih_ayahs:
        ayahs = _all_ayahs_with_mafool_bih(indexed)
        if max_ayahs is not None:
            ayahs = ayahs[: int(max_ayahs)]
        row_slice = [gr for gr in indexed if (gr.surah, gr.ayah) in set(ayahs)]
        # Reuse audit with explicit ayah list: simplest is build synthetic row_slice = all rows in those ayahs
        label = f"all_mafool_bih_ayahs_capped_{len(ayahs)}"
        ayahs_ordered = ayahs
        mafool_rows = [gr for gr in row_slice if (parse_gold_i3rab_prose((gr.i3rab or "").strip()).syntactic_role or "").strip() == "mafool_bih"]
        tallies = Counter()
        acc_cue_subj = acc_cue_obj = acc_cue_other = 0
        cache: dict[tuple[int, int], list] = {}
        for surah, ayah in ayahs_ordered:
            rows_ayah = _gold_rows_for_ayah(indexed, surah, ayah)
            text = reconstruct_ayah_text_from_gold_rows(rows_ayah)
            if not text.strip():
                continue
            try:
                r = run_pipeline(text)
            except Exception:
                continue
            dsb = (r.get("layer_outputs") or {}).get("DEPENDENCY_SYNTAX_BUILDER") or {}
            cache[(surah, ayah)] = dsb.get("dependency_links") or []
        for gr in mafool_rows:
            if (gr.surah, gr.ayah) not in set(ayahs_ordered):
                continue
            links = cache.get((gr.surah, gr.ayah), [])
            rel = _relation_for_token(links, gr.index_in_ayah)
            key = rel or "none_or_other"
            tallies[key] += 1
            acc = _surface_accusative_object_likely((gr.word or "").strip())
            if acc:
                if rel == "SUBJ":
                    acc_cue_subj += 1
                elif rel == "OBJ":
                    acc_cue_obj += 1
                else:
                    acc_cue_other += 1
        results.append({
            "label": label,
            "max_rows_in_window": len(row_slice),
            "ayahs_visited": len(ayahs_ordered),
            "mafool_bih_rows_in_window": len(mafool_rows),
            "mafool_bih_rows_audited_in_loaded_ayahs": sum(tallies.values()),
            "stage15_relation_tally": dict(tallies),
            "accusative_cue_mafool_SUBJ": acc_cue_subj,
            "accusative_cue_mafool_OBJ": acc_cue_obj,
            "accusative_cue_mafool_other_or_none": acc_cue_other,
        })
    else:
        if args.max_rows is None:
            print("--max-rows required unless --all-mafool-bih-ayahs", file=sys.stderr)
            return 2
        ayahs, row_slice = _ayahs_in_row_window(indexed, args.max_rows)
        if max_ayahs is not None:
            ayahs = ayahs[: int(max_ayahs)]
        # Restrict row_slice to rows belonging to first max_ayahs... actually audit uses rows in window
        row_set = set(ayahs)
        row_slice_f = [gr for gr in row_slice if (gr.surah, gr.ayah) in row_set]
        results.append(audit_window(indexed, row_slice_f, f"first_{args.max_rows}_rows"))

    print(json.dumps({"batch": "28.23V", "results": results}, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
