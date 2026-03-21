#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Resumable Quran iʿrāb comparison: gold CSV vs pipeline (L17 primary, L11 fallback).

See docs/quran_i3rab_comparison_pipeline.md.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, DefaultDict, Dict, List, Optional, Set, Tuple

# Repo root on PYTHONPATH (script adds src/)
def _project_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _ensure_src_path() -> None:
    root = _project_root()
    src = root / "src"
    if str(src) not in sys.path:
        sys.path.insert(0, str(src))


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _read_gold_indexed(gold_path: Path) -> List[Tuple[int, Any]]:
    from orchestrator.quran_gold.i3rab_compare_pipeline import GoldRow, _read_gold_rows

    rows = _read_gold_rows(str(gold_path))
    return list(enumerate(rows))


def _load_erqa_keys(path: Path) -> Set[Tuple[int, int, int]]:
    from orchestrator.quran_gold.i3rab_compare_pipeline import load_erqa_keys

    if not path.is_file():
        return set()
    return load_erqa_keys(str(path))


def _append_erqa_rows(
    path: Path,
    rows: List[Dict[str, Any]],
    fieldnames: Tuple[str, ...],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    exists = path.is_file() and path.stat().st_size > 0
    with open(path, "a", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fieldnames))
        if not exists:
            w.writeheader()
        for r in rows:
            w.writerow(r)


def _write_wrong(path: Path, rows: List[Dict[str, Any]], fieldnames: Tuple[str, ...]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fieldnames))
        w.writeheader()
        for r in rows:
            w.writerow(r)


def _write_alignment_debug(path: Path, rows: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fn = ("surah", "ayah", "ayah_word_index", "gold_word", "reason", "token_surfaces_head")
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fn))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fn})


def _default_paths(root: Path) -> Dict[str, Path]:
    return {
        "gold": root / "data" / "quran_i3rab.csv",
        "erqa": root / "data" / "erqa_i3rab.csv",
        "wrong": root / "data" / "wrong_i3rab.csv",
        "progress": root / "data" / "quran_i3rab_progress.json",
        "summary": root / "data" / "quran_i3rab_run_summary.json",
        "align_debug": root / "data" / "quran_i3rab_alignment_debug.csv",
    }


def run() -> int:
    _ensure_src_path()
    root = _project_root()
    defaults = _default_paths(root)

    ap = argparse.ArgumentParser(description="Quran i3rab gold vs pipeline comparison")
    ap.add_argument("--gold", type=Path, default=defaults["gold"])
    ap.add_argument("--quran-text", type=Path, default=None, help="Override ayah text file (default: data/quran-uthmani.txt)")
    ap.add_argument("--erqa", type=Path, default=defaults["erqa"])
    ap.add_argument("--wrong", type=Path, default=defaults["wrong"])
    ap.add_argument("--progress", type=Path, default=defaults["progress"])
    ap.add_argument("--summary", type=Path, default=defaults["summary"])
    ap.add_argument("--alignment-debug", type=Path, default=defaults["align_debug"])
    ap.add_argument("--limit", type=int, default=None, help="Max gold rows to process this run")
    ap.add_argument("--resume", action="store_true", help="Continue after last_row_index in progress file")
    ap.add_argument("--dry-run", action="store_true", help="Do not write output CSVs / progress")
    ap.add_argument("--max-wrong-rows", type=int, default=100)
    ap.add_argument("--from-surah", type=int, default=None)
    ap.add_argument("--from-ayah", type=int, default=None)
    ap.add_argument("--alignment-min", type=float, default=0.70, help="Minimum alignment_coverage to allow writes")
    ap.add_argument(
        "--force-below-alignment-threshold",
        action="store_true",
        help="Allow writes even if alignment_coverage < --alignment-min",
    )
    args = ap.parse_args()

    from orchestrator import run_pipeline
    from orchestrator.quran_gold.alignment import (
        AlignmentStatus,
        align_gold_words_to_tokens,
    )
    from orchestrator.quran_gold.analyzer_extract import extract_snapshots, get_token_surfaces
    from orchestrator.quran_gold.ayah_loader import default_quran_text_path, get_ayah_text, load_ayah_text_index
    from orchestrator.quran_gold.comparator import MatchLevel, compare_token_conservative, erqa_eligible
    from orchestrator.quran_gold.i3rab_compare_pipeline import row_key

    text_path = str(args.quran_text) if args.quran_text else default_quran_text_path()
    if not os.path.isfile(text_path):
        print(f"No Quran text source at {text_path}", file=sys.stderr)
        return 2
    load_ayah_text_index(text_path)

    gold_path = args.gold.resolve()
    if not gold_path.is_file():
        print(f"Gold CSV not found: {gold_path}", file=sys.stderr)
        return 2

    indexed = _read_gold_indexed(gold_path)
    total_gold = len(indexed)
    erqa_keys = _load_erqa_keys(args.erqa.resolve())

    progress: Dict[str, Any] = {}
    if args.resume and args.progress.is_file():
        progress = json.loads(args.progress.read_text(encoding="utf-8"))
    start_row = int(progress.get("last_row_index", -1)) + 1 if args.resume else 0

    # Filter global indices to process
    to_process: List[int] = []
    for global_idx, row in indexed:
        if global_idx < start_row:
            continue
        if args.from_surah is not None and (row.surah < args.from_surah):
            continue
        if args.from_surah is not None and row.surah == args.from_surah and args.from_ayah is not None:
            if row.ayah < args.from_ayah:
                continue
        if row_key(row) in erqa_keys:
            continue
        to_process.append(global_idx)
        if args.limit is not None and len(to_process) >= args.limit:
            break

    # Stats (alignment_coverage = rows_aligned / rows_alignment_attempts)
    rows_alignment_attempts = 0
    rows_aligned = 0
    rows_alignment_ambiguous = 0
    rows_matched = 0
    rows_wrong = 0
    alignment_debug_rows: List[Dict[str, Any]] = []
    new_erqa: List[Dict[str, Any]] = []
    wrong_rows: List[Dict[str, Any]] = []

    erqa_fields = (
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
    )
    wrong_fields = (
        "surah",
        "ayah",
        "word",
        "gold_i3rab",
        "system_i3rab",
        "mismatch_reason",
        "alignment_status",
        "analyzer_source",
        "notes",
        "ayah_word_index",
    )

    # Build set of ayahs needed
    needed_ayahs: Set[Tuple[int, int]] = set()
    for gi in to_process:
        row = indexed[gi][1]
        needed_ayahs.add((row.surah, row.ayah))

    # Pre-group global indices by ayah for iteration
    by_ayah: DefaultDict[Tuple[int, int], List[int]] = defaultdict(list)
    for gi in to_process:
        r = indexed[gi][1]
        by_ayah[(r.surah, r.ayah)].append(gi)

    ayah_order: List[Tuple[int, int]] = []
    seen: Set[Tuple[int, int]] = set()
    for gi in to_process:
        r = indexed[gi][1]
        k = (r.surah, r.ayah)
        if k not in seen:
            seen.add(k)
            ayah_order.append(k)

    stop_reason = "completed_batch"
    completed = False
    last_row_done = start_row - 1

    for surah, ayah in ayah_order:
        gidxs = by_ayah[(surah, ayah)]
        ayah_text = get_ayah_text(surah, ayah, text_path=text_path)
        # Full gold word list for this ayah (for alignment), not only pending indices
        full_ayah_rows = [r for _, r in indexed if r.surah == surah and r.ayah == ayah]
        gold_words = [r.word for r in full_ayah_rows]

        if not ayah_text:
            rows_alignment_attempts += len(gidxs)
            rows_alignment_ambiguous += len(gidxs)
            for gi in gidxs:
                last_row_done = max(last_row_done, gi)
                row = indexed[gi][1]
                alignment_debug_rows.append(
                    {
                        "surah": surah,
                        "ayah": ayah,
                        "ayah_word_index": row.index_in_ayah,
                        "gold_word": row.word,
                        "reason": "missing_ayah_text",
                        "token_surfaces_head": "",
                    }
                )
            continue

        pipeline = run_pipeline(
            ayah_text,
            source={"entrypoint": "run_quran_i3rab_comparison", "surah": surah, "ayah": ayah},
        )
        token_surfaces = get_token_surfaces(pipeline)
        snapshots = extract_snapshots(pipeline)
        align_results, _aln_line, _amb_line = align_gold_words_to_tokens(gold_words, token_surfaces)
        head_surfaces = " | ".join(token_surfaces[:12])

        for gi in gidxs:
            last_row_done = max(last_row_done, gi)
            row = indexed[gi][1]
            pos = row.index_in_ayah
            rows_alignment_attempts += 1
            if pos < 0 or pos >= len(align_results):
                rows_alignment_ambiguous += 1
                alignment_debug_rows.append(
                    {
                        "surah": surah,
                        "ayah": ayah,
                        "ayah_word_index": pos,
                        "gold_word": row.word,
                        "reason": "index_out_of_range",
                        "token_surfaces_head": head_surfaces,
                    }
                )
                continue

            ar = align_results[pos]
            if ar.status != AlignmentStatus.ALIGNED:
                rows_alignment_ambiguous += 1
                alignment_debug_rows.append(
                    {
                        "surah": surah,
                        "ayah": ayah,
                        "ayah_word_index": pos,
                        "gold_word": row.word,
                        "reason": ar.reason,
                        "token_surfaces_head": head_surfaces,
                    }
                )
                continue

            rows_aligned += 1
            tok_i = ar.token_index
            assert tok_i is not None
            snap = snapshots[tok_i] if tok_i < len(snapshots) else None
            dec = compare_token_conservative(row.i3rab, snap)

            if erqa_eligible(dec):
                rows_matched += 1
                rk = row_key(row)
                if rk not in erqa_keys:
                    new_erqa.append(
                        {
                            "surah": row.surah,
                            "ayah": row.ayah,
                            "word": row.word,
                            "gold_i3rab": row.i3rab,
                            "system_i3rab": dec.system_i3rab_display,
                            "match_type": dec.level.value,
                            "confidence": f"{dec.confidence:.4f}",
                            "analyzer_source": dec.analyzer_source,
                            "notes": dec.notes,
                            "ayah_word_index": row.index_in_ayah,
                        }
                    )
            elif dec.level in (MatchLevel.STRUCTURED_CASE_MARKER, MatchLevel.PARTIAL_SEMANTIC):
                # Diagnostic only — not wrong, not erqa
                pass
            else:
                rows_wrong += 1
                wrong_rows.append(
                    {
                        "surah": row.surah,
                        "ayah": row.ayah,
                        "word": row.word,
                        "gold_i3rab": row.i3rab,
                        "system_i3rab": dec.system_i3rab_display,
                        "mismatch_reason": dec.notes,
                        "alignment_status": "aligned",
                        "analyzer_source": dec.analyzer_source,
                        "notes": dec.level.value,
                        "ayah_word_index": row.index_in_ayah,
                    }
                )
                if rows_wrong > args.max_wrong_rows:
                    stop_reason = f"max_wrong_rows_exceeded_{args.max_wrong_rows}"
                    break
        if stop_reason.startswith("max_wrong"):
            break

    # Coverage / rates
    alignment_coverage = (
        (rows_aligned / rows_alignment_attempts) if rows_alignment_attempts > 0 else 1.0
    )
    match_rate = (rows_matched / rows_aligned) if rows_aligned > 0 else 0.0

    summary: Dict[str, Any] = {
        "rows_inspected": rows_aligned,
        "rows_aligned": rows_aligned,
        "rows_alignment_ambiguous": rows_alignment_ambiguous,
        "rows_alignment_attempts": rows_alignment_attempts,
        "rows_matched": rows_matched,
        "rows_wrong": rows_wrong,
        "alignment_coverage": round(alignment_coverage, 4),
        "alignment_coverage_percent": round(alignment_coverage * 100, 2),
        "match_rate": round(match_rate, 4),
        "match_rate_percent": round(match_rate * 100, 2),
        "stop_reason": stop_reason,
        "last_row_index": last_row_done,
        "dry_run": args.dry_run,
    }

    print(json.dumps(summary, ensure_ascii=False, indent=2))

    can_write = (not args.dry_run) and (
        args.force_below_alignment_threshold or (alignment_coverage + 1e-9) >= args.alignment_min
    )
    if not args.dry_run and not can_write:
        print(
            f"Refusing to write: alignment_coverage {alignment_coverage:.2%} < {args.alignment_min:.0%}. "
            "Use --force-below-alignment-threshold to override.",
            file=sys.stderr,
        )
        args.summary.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(json.dumps({**summary, "written": False}, ensure_ascii=False, indent=2), encoding="utf-8")
        return 3

    if args.dry_run:
        args.summary.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(json.dumps({**summary, "written": False}, ensure_ascii=False, indent=2), encoding="utf-8")
        return 0

    # Writes
    if can_write and new_erqa:
        _append_erqa_rows(args.erqa.resolve(), new_erqa, erqa_fields)
        for r in new_erqa:
            erqa_keys.add((int(r["surah"]), int(r["ayah"]), int(r["ayah_word_index"])))
    if can_write:
        _write_wrong(args.wrong.resolve(), wrong_rows, wrong_fields)
    if can_write and alignment_debug_rows:
        _write_alignment_debug(args.alignment_debug.resolve(), alignment_debug_rows)

    cumulative_erqa = len(erqa_keys)
    pending_remaining = sum(1 for _, r in indexed if row_key(r) not in erqa_keys)
    completed = pending_remaining == 0 and total_gold > 0

    progress_out = {
        "started_at": progress.get("started_at") or _utc_now_iso(),
        "updated_at": _utc_now_iso(),
        "last_surah": indexed[last_row_done][1].surah if last_row_done >= 0 else None,
        "last_ayah": indexed[last_row_done][1].ayah if last_row_done >= 0 else None,
        "last_row_index": last_row_done,
        "processed_rows": last_row_done + 1,
        "matched_rows_current_total": rows_matched,
        "wrong_rows_current_total": rows_wrong,
        "alignment_ambiguous_count": rows_alignment_ambiguous,
        "cumulative_erqa_rows": cumulative_erqa,
        "stop_reason": stop_reason if not completed else "all_gold_rows_in_erqa",
        "completed": completed,
        "gold_row_count": total_gold,
    }
    if can_write:
        args.progress.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.progress.write_text(json.dumps(progress_out, ensure_ascii=False, indent=2), encoding="utf-8")
        args.summary.write_text(
            json.dumps({**summary, "written": True, "progress": progress_out}, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(run())
