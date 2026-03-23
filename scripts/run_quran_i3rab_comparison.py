#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Quran iʿrāb comparison: gold CSV vs pipeline (Batch 28.3 — ayah-bounded, strict comparator).

See docs/quran_i3rab_comparison_pipeline.md.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
import uuid
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

# Repo root on PYTHONPATH (script adds src/)


def _project_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _ensure_src_path() -> None:
    root = _project_root()
    src = root / "src"
    if str(src) not in sys.path:
        sys.path.insert(0, str(src))


def _utc_now_iso() -> str:
    from datetime import datetime, timezone

    return datetime.now(timezone.utc).isoformat()


def _read_gold_indexed(gold_path: Path) -> List[Tuple[int, Any]]:
    from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows

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


def _write_alignment_debug(path: Path, rows: List[Dict[str, Any]], fields: Tuple[str, ...]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(fields))
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in fields})


def _default_paths(root: Path) -> Dict[str, Path]:
    return {
        "gold": root / "data" / "quran_i3rab.csv",
        "erqa": root / "data" / "erqa_i3rab.csv",
        "wrong": root / "data" / "wrong_i3rab.csv",
        "progress": root / "data" / "progress_state.json",
        "batch_summary": root / "data" / "batch_summary.json",
        "align_debug": root / "data" / "quran_i3rab_alignment_debug.csv",
        "ayah_audit": root / "data" / "quran_i3rab_ayah_audit.csv",
        "ayah_token_debug": root / "data" / "quran_i3rab_ayah_token_debug.csv",
        "structured_debug": root / "data" / "quran_i3rab_structured_debug.csv",
        "repair_log": root / "data" / "repair_log.csv",
        "ayah_review_queue": root / "data" / "ayah_review_queue.csv",
        "truth_audit": root / "data" / "quran_i3rab_truth_audit.csv",
        "unlockable_ayahs": root / "data" / "quran_i3rab_unlockable_ayahs.csv",
        "real_accept_preview": root / "data" / "quran_i3rab_real_accept_preview.csv",
        "pass_strict_candidates": root / "data" / "quran_i3rab_pass_strict_candidates.csv",
        "pass_strict_scan_summary": root / "data" / "quran_i3rab_pass_strict_scan_summary.json",
        "discovery_rows": root / "data" / "quran_i3rab_discovery_rows.csv",
        "discovery_ayah_summary": root / "data" / "quran_i3rab_discovery_ayah_summary.csv",
        "trapped_strict_rows": root / "data" / "quran_i3rab_trapped_strict_rows.csv",
    }


def _ayah_text_for_comparison(
    indexed: List[Tuple[int, Any]],
    surah: int,
    ayah: int,
    *,
    use_gold_csv_ayah: bool,
    text_path: str,
) -> str:
    if use_gold_csv_ayah:
        from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed

        return reconstruct_ayah_text_from_indexed(indexed, surah, ayah)
    from orchestrator.quran_gold.ayah_loader import get_ayah_text

    return get_ayah_text(surah, ayah, text_path=text_path) or ""


def _git_branch() -> str:
    try:
        p = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=str(_project_root()),
            capture_output=True,
            text=True,
            timeout=5,
        )
        if p.returncode == 0:
            return p.stdout.strip() or "unknown"
    except OSError:
        pass
    return "unknown"


ALIGNMENT_DEBUG_FIELDS = (
    "row_index",
    "surah",
    "ayah",
    "gold_word",
    "gold_word_normalized",
    "ayah_text",
    "ayah_token_index",
    "ayah_token_surface",
    "ayah_token_normalized",
    "alignment_status",
    "alignment_reason",
    "occurrence_rank_gold",
    "occurrence_rank_ayah",
    "comparator_decision",
)


def _all_ayah_keys_sorted(indexed: List[Tuple[int, Any]]) -> List[Tuple[int, int]]:
    return sorted({(r.surah, r.ayah) for _, r in indexed})


PASS_STRICT_SCAN_KEY = "pass_strict_scan_last_completed_ayah"
PASS_STRICT_WRITE_BATCH_KEY = "pass_strict_write_batch_id"
PASS_STRICT_WRITE_LAST_KEY = "pass_strict_write_last_completed_ayah"


def _isolated_batch_under_root(batch_dir: Path, root: Path) -> bool:
    wb = (root / "data" / "write_batches").resolve()
    try:
        batch_dir.resolve().relative_to(wb)
        return True
    except ValueError:
        return False


def _first_n_by_status(
    rows: List[Dict[str, Any]],
    *,
    predicate: Callable[[Dict[str, Any]], bool],
    n: int,
) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    for r in sorted(rows, key=lambda x: (int(x.get("surah") or 0), int(x.get("ayah") or 0))):
        if predicate(r):
            try:
                out.append((int(r["surah"]), int(r["ayah"])))
            except (KeyError, ValueError):
                continue
        if len(out) >= n:
            break
    return out


def _run_scan_pass_strict(args, root: Path, defaults: Dict[str, Path]) -> int:
    from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
    from orchestrator.quran_gold.ayah_loader import default_quran_text_path, get_ayah_text, load_ayah_text_index
    from orchestrator.quran_gold.batch_quarantine import load_progress_state, write_progress_state
    from orchestrator.quran_gold.pass_strict_batch import (
        build_discovery_summary,
        discovery_row_from_result,
        load_candidates_csv_as_dict,
        rank_ayahs_by_metric,
        write_json,
        write_pass_strict_candidates_csv,
    )

    if args.pass_strict_candidates_out is None:
        args.pass_strict_candidates_out = defaults["pass_strict_candidates"]
    if args.pass_strict_scan_summary_out is None:
        args.pass_strict_scan_summary_out = defaults["pass_strict_scan_summary"]

    use_gold_csv_ayah = getattr(args, "canonical_ayah_source", "uthmani") == "gold_csv"
    text_path = ""
    if not use_gold_csv_ayah:
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
    erqa_keys = _load_erqa_keys(args.erqa.resolve())

    max_rows = args.max_rows if args.max_rows is not None else args.limit

    full_progress = load_progress_state(args.progress.resolve())
    prev = full_progress if args.resume_scan else {}
    resume_after: Optional[Tuple[int, int]] = None
    if args.resume_scan and prev.get(PASS_STRICT_SCAN_KEY):
        la = prev[PASS_STRICT_SCAN_KEY]
        if isinstance(la, list) and len(la) == 2:
            resume_after = (int(la[0]), int(la[1]))

    ayah_keys = _all_ayah_keys_sorted(indexed)
    to_visit = _filter_ayah_keys(
        ayah_keys,
        from_surah=args.from_surah,
        from_ayah=args.from_ayah,
        max_ayahs=args.max_ayahs,
        resume_after=resume_after,
    )

    merged = load_candidates_csv_as_dict(args.pass_strict_candidates_out.resolve())
    rows_used = 0

    for surah, ayah in to_visit:
        n_in_ayah = sum(1 for _, r in indexed if r.surah == surah and r.ayah == ayah)
        if max_rows is not None and rows_used + n_in_ayah > max_rows:
            break
        rows_used += n_in_ayah

        if use_gold_csv_ayah:
            from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed

            ayah_text = reconstruct_ayah_text_from_indexed(indexed, surah, ayah)
        else:
            ayah_text = get_ayah_text(surah, ayah, text_path=text_path) or ""
        final_res = None
        for attempt in range(args.max_repair_attempts):
            res = evaluate_ayah(
                surah,
                ayah,
                indexed,
                erqa_keys,
                ayah_text or "",
                repair_pass=attempt,
                require_strict_comparator=args.require_strict_comparator,
            )
            final_res = res
            if res.decision == AyahDecision.PASS_STRICT:
                break

        assert final_res is not None
        ar = final_res
        row = discovery_row_from_result(ar, surah, ayah)
        merged[(surah, ayah)] = row

        scan_state = dict(full_progress)
        scan_state[PASS_STRICT_SCAN_KEY] = [surah, ayah]
        scan_state["updated_at"] = _utc_now_iso()
        write_progress_state(args.progress.resolve(), scan_state)

    sorted_rows = sorted(merged.values(), key=lambda r: (int(r["surah"]), int(r["ayah"])))
    write_pass_strict_candidates_csv(args.pass_strict_candidates_out.resolve(), sorted_rows)

    def _unlockable(r: Dict[str, Any]) -> bool:
        return int(r.get("rows_unlockable_now") or 0) > 0

    def _pass_strict(r: Dict[str, Any]) -> bool:
        return (r.get("decision_status") or "") == AyahDecision.PASS_STRICT.value

    first_ps = _first_n_by_status(sorted_rows, predicate=_pass_strict, n=10)
    first_un = _first_n_by_status(sorted_rows, predicate=_unlockable, n=10)
    top_l17 = rank_ayahs_by_metric(sorted_rows, "rows_blocked_by_l17_core", 10)
    top_cf = rank_ayahs_by_metric(sorted_rows, "rows_blocked_by_true_conflict", 10)

    summary = build_discovery_summary(
        sorted_rows,
        ayahs_scanned=len(sorted_rows),
        first_10_pass_strict=first_ps,
        first_10_unlockable=first_un,
        top_l17=top_l17,
        top_conflict=top_cf,
    )
    write_json(args.pass_strict_scan_summary_out.resolve(), summary)
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0


def _run_write_pass_strict_only(args, root: Path, defaults: Dict[str, Path]) -> int:
    from orchestrator.quran_gold.accepted_row_serializer import ERQA_ACCEPTED_ROW_FIELDNAMES
    from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
    from orchestrator.quran_gold.ayah_loader import default_quran_text_path, get_ayah_text, load_ayah_text_index
    from orchestrator.quran_gold.batch_quarantine import append_repair_log, load_progress_state, write_progress_state
    from orchestrator.quran_gold.pass_strict_batch import (
        ensure_fresh_batch_dir,
        load_pass_strict_ayah_keys,
        write_json,
        write_review_sample_csv,
    )

    if args.candidate_source is None:
        args.candidate_source = defaults["pass_strict_candidates"]

    cand_path = args.candidate_source.resolve()
    if not cand_path.is_file():
        print(f"Candidate file not found: {cand_path}", file=sys.stderr)
        return 2

    pass_keys = load_pass_strict_ayah_keys(cand_path)
    if not pass_keys:
        print("No PASS_STRICT ayahs in candidate file; refusing write.", file=sys.stderr)
        return 2

    use_gold_csv_ayah = getattr(args, "canonical_ayah_source", "uthmani") == "gold_csv"
    text_path = ""
    if not use_gold_csv_ayah:
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
    main_erqa_keys = _load_erqa_keys(args.erqa.resolve())

    batch_root = args.write_batch_root if args.write_batch_root is not None else root / "data" / "write_batches"
    batch_root = batch_root.resolve()

    full_progress = load_progress_state(args.progress.resolve())
    batch_id = args.write_batch_id
    if batch_id is None:
        batch_id = full_progress.get(PASS_STRICT_WRITE_BATCH_KEY) if args.resume_write else None
    if batch_id is None:
        batch_id = f"batch_{_utc_now_iso().replace(':', '').split('.')[0]}_{uuid.uuid4().hex[:8]}"

    batch_dir = batch_root / batch_id
    if not args.allow_non_isolated_output and not _isolated_batch_under_root(batch_dir, root):
        print(
            f"Refusing non-isolated batch directory {batch_dir}. "
            f"Use data/write_batches/... or --allow-non-isolated-output.",
            file=sys.stderr,
        )
        return 2

    erqa_path = batch_dir / "erqa_i3rab.csv"
    wrong_path = batch_dir / "wrong_i3rab.csv"
    repair_path = batch_dir / "repair_log.csv"
    summary_path = batch_dir / "batch_summary.json"
    accepted_ayahs_path = batch_dir / "accepted_ayahs.csv"
    rejected_ayahs_path = batch_dir / "rejected_ayahs.csv"
    manifest_path = batch_dir / "manifest.json"
    review_path = batch_dir / "review_sample.csv"

    if not args.dry_run:
        if args.resume_write:
            if not batch_dir.is_dir():
                print(f"Resume write: batch directory missing: {batch_dir}", file=sys.stderr)
                return 2
        else:
            batch_dir.mkdir(parents=True, exist_ok=True)
            try:
                ensure_fresh_batch_dir(batch_dir)
            except FileExistsError as e:
                print(str(e), file=sys.stderr)
                return 2

    batch_erqa_keys = _load_erqa_keys(erqa_path) if not args.dry_run else set()
    erqa_keys: Set[Tuple[int, int, int]] = set(main_erqa_keys) | set(batch_erqa_keys)

    resume_after: Optional[Tuple[int, int]] = None
    if args.resume_write and full_progress.get(PASS_STRICT_WRITE_LAST_KEY):
        la = full_progress[PASS_STRICT_WRITE_LAST_KEY]
        if isinstance(la, list) and len(la) == 2:
            resume_after = (int(la[0]), int(la[1]))

    keys_to_process: List[Tuple[int, int]] = []
    for k in pass_keys:
        if resume_after is not None and k <= resume_after:
            continue
        keys_to_process.append(k)
        if args.max_write_ayahs is not None and len(keys_to_process) >= args.max_write_ayahs:
            break

    if not keys_to_process:
        print(json.dumps({"message": "no_ayahs_to_process", "batch_id": batch_id}, ensure_ascii=False, indent=2))
        return 0

    erqa_fields = ERQA_ACCEPTED_ROW_FIELDNAMES
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

    ts_start = _utc_now_iso()
    repair_rows: List[Dict[str, Any]] = []
    wrong_accum: List[Dict[str, Any]] = []
    accepted_ayah_rows: List[Dict[str, Any]] = []
    rejected_ayah_rows: List[Dict[str, Any]] = []
    accepted_row_accum: List[Dict[str, Any]] = []
    rejected_sample_pool: List[Dict[str, Any]] = []

    if args.resume_write and not args.dry_run:
        if accepted_ayahs_path.is_file():
            with open(accepted_ayahs_path, encoding="utf-8-sig") as f:
                accepted_ayah_rows = list(csv.DictReader(f))
        if rejected_ayahs_path.is_file():
            with open(rejected_ayahs_path, encoding="utf-8-sig") as f:
                rejected_ayah_rows = list(csv.DictReader(f))
        if wrong_path.is_file():
            with open(wrong_path, encoding="utf-8-sig") as f:
                wrong_accum = list(csv.DictReader(f))

    ayahs_processed = 0
    ayahs_passed = 0
    ayahs_rejected = 0
    accepted_rows_written = 0
    wrong_rows_written = 0

    for surah, ayah in keys_to_process:
        ayahs_processed += 1
        if use_gold_csv_ayah:
            from orchestrator.quran_gold.gold_csv_ayah import reconstruct_ayah_text_from_indexed

            ayah_text = reconstruct_ayah_text_from_indexed(indexed, surah, ayah)
        else:
            ayah_text = get_ayah_text(surah, ayah, text_path=text_path) or ""
        final_res = None
        for attempt in range(args.max_repair_attempts):
            res = evaluate_ayah(
                surah,
                ayah,
                indexed,
                erqa_keys,
                ayah_text or "",
                repair_pass=attempt,
                require_strict_comparator=args.require_strict_comparator,
            )
            repair_rows.append(
                {
                    "timestamp": ts_start,
                    "surah": surah,
                    "ayah": ayah,
                    "row_index": "",
                    "word": "",
                    "issue_type": res.decision.value,
                    "attempt_no": str(attempt + 1),
                    "action_taken": "evaluate_ayah",
                    "result_status": (res.reason or "")[:200],
                    "notes": f"repair_pass={attempt}",
                }
            )
            final_res = res
            if res.decision == AyahDecision.PASS_STRICT:
                break

        assert final_res is not None
        ar = final_res

        rt = ar.rows_total or 1
        align_cov = (rt - ar.rows_skipped_alignment) / rt
        if ar.decision != AyahDecision.PASS_STRICT:
            rejected_ayah_rows.append(
                {
                    "surah": surah,
                    "ayah": ayah,
                    "reason": f"reeval_not_pass_strict:{ar.decision.value}:{ar.reason}",
                }
            )
            rejected_sample_pool.extend(ar.wrong_payloads[:5])
            ayahs_rejected += 1
            wr_state = dict(full_progress)
            wr_state[PASS_STRICT_WRITE_LAST_KEY] = [surah, ayah]
            wr_state[PASS_STRICT_WRITE_BATCH_KEY] = batch_id
            wr_state["updated_at"] = _utc_now_iso()
            write_progress_state(args.progress.resolve(), wr_state)
            full_progress = wr_state
            continue

        if not args.force_below_alignment_threshold and (align_cov + 1e-9) < args.alignment_min:
            rejected_ayah_rows.append(
                {
                    "surah": surah,
                    "ayah": ayah,
                    "reason": f"alignment_coverage_below_min:{align_cov:.4f}",
                }
            )
            ayahs_rejected += 1
            wr_state = dict(full_progress)
            wr_state[PASS_STRICT_WRITE_LAST_KEY] = [surah, ayah]
            wr_state[PASS_STRICT_WRITE_BATCH_KEY] = batch_id
            wr_state["updated_at"] = _utc_now_iso()
            write_progress_state(args.progress.resolve(), wr_state)
            full_progress = wr_state
            continue

        new_rows = []
        for er in ar.new_erqa_payloads:
            rk = (int(er["surah"]), int(er["ayah"]), int(er["ayah_word_index"]))
            if rk in erqa_keys:
                continue
            new_rows.append(er)

        if not args.dry_run:
            if new_rows:
                _append_erqa_rows(erqa_path, new_rows, erqa_fields)
                for er in new_rows:
                    rk = (int(er["surah"]), int(er["ayah"]), int(er["ayah_word_index"]))
                    erqa_keys.add(rk)
                    accepted_rows_written += 1
            if ar.wrong_payloads:
                wrong_accum.extend(ar.wrong_payloads)
                wrong_rows_written += len(ar.wrong_payloads)

        accepted_row_accum.extend(ar.new_erqa_payloads)
        accepted_ayah_rows.append(
            {
                "surah": surah,
                "ayah": ayah,
                "new_rows": str(len(new_rows)),
                "decision": AyahDecision.PASS_STRICT.value,
            }
        )
        ayahs_passed += 1

        wr_state = dict(full_progress)
        wr_state[PASS_STRICT_WRITE_LAST_KEY] = [surah, ayah]
        wr_state[PASS_STRICT_WRITE_BATCH_KEY] = batch_id
        wr_state["updated_at"] = _utc_now_iso()
        write_progress_state(args.progress.resolve(), wr_state)
        full_progress = wr_state

    ts_end = _utc_now_iso()

    if not args.dry_run:
        append_repair_log(repair_path, repair_rows)
        _write_wrong(wrong_path, wrong_accum, wrong_fields)
        with open(accepted_ayahs_path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=["surah", "ayah", "new_rows", "decision"])
            w.writeheader()
            for r in accepted_ayah_rows:
                w.writerow(r)
        with open(rejected_ayahs_path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=["surah", "ayah", "reason"])
            w.writeheader()
            for r in rejected_ayah_rows:
                w.writerow(r)

    if not args.dry_run and erqa_path.is_file():
        with open(erqa_path, encoding="utf-8-sig") as f:
            accepted_rows_written = sum(1 for _ in csv.DictReader(f))
    if not args.dry_run and wrong_path.is_file():
        with open(wrong_path, encoding="utf-8-sig") as f:
            wrong_rows_written = sum(1 for _ in csv.DictReader(f))

    review_accepted: List[Dict[str, Any]] = []
    if not args.dry_run and erqa_path.is_file():
        with open(erqa_path, encoding="utf-8-sig") as f:
            review_accepted = list(csv.DictReader(f))
    else:
        for er in accepted_row_accum:
            review_accepted.append({**er, "match_type": er.get("match_type", "")})
    rej_sample = rejected_sample_pool[:15]
    if not args.dry_run:
        write_review_sample_csv(review_path, review_accepted, rej_sample)

    batch_summary = {
        "batch_id": batch_id,
        "timestamp": ts_end,
        "ayahs_processed": ayahs_processed,
        "ayahs_passed": ayahs_passed,
        "ayahs_rejected": ayahs_rejected,
        "accepted_rows_written": accepted_rows_written,
        "wrong_rows_this_batch": wrong_rows_written,
        "dry_run": args.dry_run,
        "write_mode": True,
        "candidate_source": str(cand_path),
    }
    if not args.dry_run:
        write_json(summary_path, batch_summary)

    manifest = {
        "batch_id": batch_id,
        "source_candidate_file": str(cand_path),
        "ayahs_requested": len(keys_to_process),
        "ayahs_processed": ayahs_processed,
        "ayahs_passed": ayahs_passed,
        "ayahs_rejected": ayahs_rejected,
        "accepted_rows_written": accepted_rows_written,
        "wrong_rows_written": wrong_rows_written,
        "started_from": ts_start,
        "ended_at": ts_end,
        "dry_run": args.dry_run,
        "write_mode": "pass_strict_only",
        "quarantine_policy": "full_ayah_PASS_STRICT_only",
        "acceptance_policy": "exact_text_match_or_strict_structural_match_only",
        "notes": "Batch 28.6 isolated write; main data/erqa_i3rab.csv not modified unless shared via --erqa reads.",
    }
    if not args.dry_run:
        write_json(manifest_path, manifest)

    print(json.dumps({**batch_summary, "batch_dir": str(batch_dir)}, ensure_ascii=False, indent=2))
    return 0


def _filter_ayah_keys(
    keys: List[Tuple[int, int]],
    *,
    from_surah: Optional[int],
    from_ayah: Optional[int],
    max_ayahs: Optional[int],
    resume_after: Optional[Tuple[int, int]],
) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    for k in keys:
        s, a = k
        if from_surah is not None and s < from_surah:
            continue
        if from_surah is not None and s == from_surah and from_ayah is not None and a < from_ayah:
            continue
        if resume_after is not None and (s, a) <= resume_after:
            continue
        out.append(k)
        if max_ayahs is not None and len(out) >= max_ayahs:
            break
    return out


def run() -> int:
    _ensure_src_path()
    root = _project_root()
    defaults = _default_paths(root)

    ap = argparse.ArgumentParser(description="Quran i3rab gold vs pipeline comparison (ayah-bounded)")
    ap.add_argument("--gold", type=Path, default=defaults["gold"])
    ap.add_argument("--quran-text", type=Path, default=None, help="Ayah text file (default: data/quran-uthmani.txt)")
    ap.add_argument("--erqa", type=Path, default=defaults["erqa"])
    ap.add_argument("--wrong", type=Path, default=defaults["wrong"])
    ap.add_argument("--progress", type=Path, default=defaults["progress"])
    ap.add_argument("--batch-summary", type=Path, default=defaults["batch_summary"])
    ap.add_argument("--summary", type=Path, default=None, help="Alias for --batch-summary")
    ap.add_argument("--alignment-debug", type=Path, default=defaults["align_debug"])
    ap.add_argument("--ayah-audit", type=Path, default=defaults["ayah_audit"])
    ap.add_argument("--ayah-token-debug", type=Path, default=defaults["ayah_token_debug"])
    ap.add_argument("--structured-debug", type=Path, default=defaults["structured_debug"])
    ap.add_argument("--repair-log", type=Path, default=defaults["repair_log"])
    ap.add_argument("--ayah-review-queue", type=Path, default=defaults["ayah_review_queue"])
    ap.add_argument("--truth-audit", type=Path, default=defaults["truth_audit"])
    ap.add_argument("--unlockable-ayahs", type=Path, default=defaults["unlockable_ayahs"])
    ap.add_argument("--real-accept-preview", type=Path, default=defaults["real_accept_preview"])
    ap.add_argument("--limit", type=int, default=None, help="Deprecated alias for --max-rows")
    ap.add_argument("--max-rows", type=int, default=None, help="Max gold rows to process (ayahs are not split)")
    ap.add_argument("--max-ayahs", type=int, default=None, help="Max ayahs to process this run")
    ap.add_argument("--resume", action="store_true", help="Resume from --progress state")
    ap.add_argument("--dry-run", action="store_true", help="No erqa/wrong/repair writes; debug/summary may still write")
    ap.add_argument(
        "--write-mode",
        action="store_true",
        help="Append accepted rows to erqa; required for erqa writes (otherwise quarantine only)",
    )
    ap.add_argument("--max-wrong-rows", type=int, default=100)
    ap.add_argument("--from-surah", type=int, default=None)
    ap.add_argument("--from-ayah", type=int, default=None)
    ap.add_argument("--alignment-min", type=float, default=0.70, help="Minimum alignment_coverage to allow erqa writes")
    ap.add_argument("--force-below-alignment-threshold", action="store_true")
    ap.add_argument("--max-repair-attempts", type=int, default=2)
    ap.add_argument("--stop-on-first-unsafe-ayah", action="store_true", default=True)
    ap.add_argument("--no-stop-on-first-unsafe-ayah", action="store_false", dest="stop_on_first_unsafe_ayah")
    ap.add_argument("--require-strict-comparator", action="store_true", default=True)
    ap.add_argument("--no-require-strict-comparator", action="store_false", dest="require_strict_comparator")
    ap.add_argument(
        "--scan-pass-strict",
        action="store_true",
        help="Dry-run ayah scan: write pass_strict candidates CSV + scan summary JSON (no erqa writes)",
    )
    ap.add_argument(
        "--resume-scan",
        action="store_true",
        help="With --scan-pass-strict: resume after pass_strict_scan_last_completed_ayah in --progress",
    )
    ap.add_argument(
        "--pass-strict-candidates-out",
        type=Path,
        default=None,
        help="Output CSV for --scan-pass-strict (default: data/quran_i3rab_pass_strict_candidates.csv)",
    )
    ap.add_argument(
        "--pass-strict-scan-summary-out",
        type=Path,
        default=None,
        help="Output JSON for --scan-pass-strict (default: data/quran_i3rab_pass_strict_scan_summary.json)",
    )
    ap.add_argument(
        "--write-mode-pass-strict-only",
        action="store_true",
        help="Bounded write: only ayahs with PASS_STRICT in candidate CSV; isolated batch outputs by default",
    )
    ap.add_argument(
        "--candidate-source",
        type=Path,
        default=None,
        help="CSV from --scan-pass-strict (default: data/quran_i3rab_pass_strict_candidates.csv)",
    )
    ap.add_argument("--max-write-ayahs", type=int, default=None, help="Cap ayahs processed in pass-strict write mode")
    ap.add_argument(
        "--resume-write",
        action="store_true",
        help="Continue pass-strict write batch from --progress (same batch_id, no duplicate rows)",
    )
    ap.add_argument(
        "--write-batch-id",
        type=str,
        default=None,
        help="Subdirectory under data/write_batches/ for isolated outputs",
    )
    ap.add_argument(
        "--write-batch-root",
        type=Path,
        default=None,
        help="Parent directory for batch folders (default: data/write_batches)",
    )
    ap.add_argument(
        "--allow-non-isolated-output",
        action="store_true",
        help="Allow --write-batch-root outside data/write_batches (unsafe; for explicit overrides)",
    )
    ap.add_argument(
        "--discovery-only",
        action="store_true",
        help="Batch 28.7: gold-CSV-only ayah text, emit discovery CSVs, force dry-run (no uthmani)",
    )
    ap.add_argument(
        "--emit-discovery-csvs",
        action="store_true",
        help="Emit discovery row/ayah/trapped/unlockable-ranked CSVs (uses gold CSV ayah reconstruction)",
    )
    ap.add_argument(
        "--discovery-limit",
        type=int,
        default=None,
        help="Max gold rows to process (overrides --limit / --max-rows)",
    )
    ap.add_argument(
        "--canonical-ayah-source",
        choices=("uthmani", "gold_csv"),
        default="uthmani",
        help="Ayah string for pipeline: uthmani file vs gold CSV word join (Batch 28.7)",
    )
    ap.add_argument(
        "--discovery-rows-out",
        type=Path,
        default=None,
        help="Override path for quran_i3rab_discovery_rows.csv",
    )
    ap.add_argument(
        "--discovery-ayah-summary-out",
        type=Path,
        default=None,
        help="Override path for quran_i3rab_discovery_ayah_summary.csv",
    )
    ap.add_argument(
        "--trapped-strict-rows-out",
        type=Path,
        default=None,
        help="Override path for quran_i3rab_trapped_strict_rows.csv",
    )
    args = ap.parse_args()
    if args.summary is not None:
        args.batch_summary = args.summary

    if args.discovery_only:
        args.emit_discovery_csvs = True
        args.canonical_ayah_source = "gold_csv"
        args.dry_run = True

    if args.scan_pass_strict:
        return _run_scan_pass_strict(args, root, defaults)
    if args.write_mode_pass_strict_only:
        return _run_write_pass_strict_only(args, root, defaults)

    from orchestrator.quran_gold.ayah_batch_runner import AyahDecision, evaluate_ayah
    from orchestrator.quran_gold.ayah_loader import default_quran_text_path, load_ayah_text_index
    from orchestrator.quran_gold.batch_quarantine import (
        append_repair_log,
        git_head_short,
        load_progress_state,
        upsert_ayah_review_queue,
        write_batch_summary,
        write_progress_state,
    )
    from orchestrator.quran_gold.i3rab_compare_pipeline import row_key
    from orchestrator.quran_gold.segmentation_audit import (
        AyahAuditRow,
        build_token_inventory_rows,
        summarize_ayah_reason,
        write_ayah_audit_csv,
        write_ayah_token_debug_csv,
    )
    from orchestrator.quran_gold.truth_audit import (
        aggregate_batch_28_5_counters,
        summarize_ayah_unlockability,
        write_real_accept_preview_csv,
        write_truth_audit_csv,
        write_unlockable_ayahs_csv,
    )
    from orchestrator.quran_gold.accepted_row_serializer import ERQA_ACCEPTED_ROW_FIELDNAMES

    use_gold_csv_ayah = (
        args.canonical_ayah_source == "gold_csv"
        or args.discovery_only
        or args.emit_discovery_csvs
    )
    emit_discovery = bool(args.discovery_only or args.emit_discovery_csvs)

    text_path = ""
    if not use_gold_csv_ayah:
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

    max_rows = args.max_rows if args.max_rows is not None else args.limit
    if args.discovery_limit is not None:
        max_rows = args.discovery_limit

    prev = load_progress_state(args.progress.resolve()) if args.resume else {}
    resume_after: Optional[Tuple[int, int]] = None
    if args.resume and prev.get("last_completed_ayah"):
        la = prev["last_completed_ayah"]
        if isinstance(la, list) and len(la) == 2:
            resume_after = (int(la[0]), int(la[1]))

    ayah_keys = _all_ayah_keys_sorted(indexed)
    to_visit = _filter_ayah_keys(
        ayah_keys,
        from_surah=args.from_surah,
        from_ayah=args.from_ayah,
        max_ayahs=args.max_ayahs,
        resume_after=resume_after,
    )

    batch_id = str(uuid.uuid4())
    ts = _utc_now_iso()

    erqa_fields = ERQA_ACCEPTED_ROW_FIELDNAMES
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

    alignment_debug_accum: List[Dict[str, Any]] = []
    ayah_audit_rows: List[AyahAuditRow] = []
    ayah_token_debug_accum: List[Dict[str, Any]] = []
    wrong_batch: List[Dict[str, Any]] = []
    new_erqa_batch: List[Dict[str, Any]] = []
    repair_rows: List[Dict[str, Any]] = []
    review_rows: List[Dict[str, Any]] = []
    structured_debug_accum: List[Dict[str, Any]] = []
    truth_audit_accum: List[Dict[str, Any]] = []
    unlockable_ayah_accum: List[Dict[str, Any]] = []
    real_accept_preview_accum: List[Dict[str, Any]] = []
    discovery_rows_accum: List[Dict[str, Any]] = []
    discovery_ayah_accum: List[Dict[str, Any]] = []
    trapped_strict_accum: List[Dict[str, Any]] = []
    batch_28_9_blocker_rows: List[Dict[str, Any]] = []
    batch_28_9_near_pass_rows: List[Dict[str, Any]] = []
    batch_28_9_unlock_preview: List[Dict[str, Any]] = []
    batch_28_9_best_write: List[Dict[str, Any]] = []
    trapped_strict_rows_total = 0
    trapped_strict_ayahs_total = 0
    pass_strict_ayahs = 0
    tier_counts: Dict[str, int] = {}
    per_ayah_snapshots: List[Dict[str, Any]] = []

    rows_alignment_attempts = 0
    rows_aligned = 0
    stop_reason = "completed_batch"
    accepted_rows_total = int(prev.get("accepted_rows_total", 0))
    rejected_rows_total = int(prev.get("rejected_rows_total", 0))
    skipped_alignment_total = int(prev.get("skipped_alignment_total", 0))
    last_row_done = int(prev.get("last_processed_row_index", -1))
    rows_used = 0
    last_completed_ayah: Optional[Tuple[int, int]] = None

    if emit_discovery:
        from orchestrator.quran_gold.discovery_reporting import (
            build_discovery_rows_for_ayah,
            collect_trapped_strict_rows,
            per_ayah_discovery_summary,
        )
        from orchestrator.quran_gold.gold_csv_ayah import word_index_to_global_index

    from orchestrator.quran_gold.discovery_reporting import collect_trapped_strict_rows as collect_trapped_strict_rows_b29
    from orchestrator.quran_gold.gold_csv_ayah import word_index_to_global_index as word_index_to_global_index_b29
    from orchestrator.quran_gold import ayah_unlock_ranker as batch_29_unlock

    for surah, ayah in to_visit:
        n_in_ayah = sum(1 for _, r in indexed if r.surah == surah and r.ayah == ayah)
        if max_rows is not None and rows_used + n_in_ayah > max_rows:
            stop_reason = "max_rows_cap"
            break
        rows_used += n_in_ayah

        ayah_text = _ayah_text_for_comparison(
            indexed, surah, ayah, use_gold_csv_ayah=use_gold_csv_ayah, text_path=text_path
        )
        final_res = None
        for attempt in range(args.max_repair_attempts):
            res = evaluate_ayah(
                surah,
                ayah,
                indexed,
                erqa_keys,
                ayah_text or "",
                repair_pass=attempt,
                require_strict_comparator=args.require_strict_comparator,
            )
            repair_rows.append(
                {
                    "timestamp": ts,
                    "surah": surah,
                    "ayah": ayah,
                    "row_index": "",
                    "word": "",
                    "issue_type": res.decision.value,
                    "attempt_no": str(attempt + 1),
                    "action_taken": "evaluate_ayah",
                    "result_status": res.reason[:200],
                    "notes": f"repair_pass={attempt}",
                }
            )
            final_res = res
            if res.decision == AyahDecision.PASS_STRICT:
                break

        assert final_res is not None
        ar = final_res

        # Segmentation audit row (lightweight)
        gold_words = [r.word for _, r in indexed if r.surah == surah and r.ayah == ayah]
        g_rc = len(gold_words)
        aligned_ct = ar.rows_total - ar.rows_skipped_alignment
        missing_ct = ar.rows_skipped_alignment
        amb_ct = 0
        token_counts_differ = False
        order_drift = False
        reason_summary = summarize_ayah_reason(token_counts_differ, order_drift, missing_ct, amb_ct)
        reason_summary = f"{ar.decision.value}|{reason_summary}"
        ayah_audit_rows.append(
            AyahAuditRow(
                surah=surah,
                ayah=ayah,
                gold_row_count=g_rc,
                pipeline_token_count=g_rc,
                aligned_count=max(0, aligned_ct),
                missing_count=missing_ct,
                ambiguous_count=amb_ct,
                token_counts_differ=token_counts_differ,
                order_drift=order_drift,
                reason_summary=reason_summary,
            )
        )

        alignment_debug_accum.extend(ar.alignment_debug_rows)
        structured_debug_accum.extend(ar.structured_debug_rows)
        truth_audit_accum.extend(ar.truth_audit_rows)
        per_ayah_snapshots.append(
            {
                "surah": surah,
                "ayah": ayah,
                "decision": ar.decision.value,
                "truth_audit_rows": list(ar.truth_audit_rows),
                "structured_debug_rows": list(ar.structured_debug_rows),
            }
        )

        wi_to_gi_b29 = word_index_to_global_index_b29(indexed, surah, ayah)
        ts_b29 = collect_trapped_strict_rows_b29(
            surah,
            ayah,
            ar.decision.value,
            ar.structured_debug_rows,
            ar.reason or ar.decision.value,
            wi_to_gi_b29,
        )
        trapped_strict_rows_total += len(ts_b29)
        if ts_b29:
            trapped_strict_ayahs_total += 1
        if ar.decision != AyahDecision.PASS_STRICT:
            batch_28_9_blocker_rows.append(
                batch_29_unlock.build_ayah_blocker_ranking_row(
                    surah, ayah, ar.decision, ar.truth_audit_rows, ar.reason or ""
                )
            )
        batch_28_9_near_pass_rows.append(
            batch_29_unlock.build_near_pass_ayah_row(
                surah, ayah, ar.decision, ar.truth_audit_rows, ar.reason or ""
            )
        )
        batch_28_9_unlock_preview.extend(
            batch_29_unlock.build_unlock_preview_rows(
                surah, ayah, ar.decision, ar.truth_audit_rows, ar.structured_debug_rows, wi_to_gi_b29
            )
        )
        bwc = batch_29_unlock.build_best_write_candidate_row(surah, ayah, ar.decision, ar.truth_audit_rows)
        if bwc:
            batch_28_9_best_write.append(bwc)
        for pr in ar.preview_candidate_rows:
            pc = dict(pr)
            pc["safe_to_accept_now"] = str(ar.decision == AyahDecision.PASS_STRICT).lower()
            real_accept_preview_accum.append(pc)
        if emit_discovery:
            wi_to_gi = word_index_to_global_index(indexed, surah, ayah)
            discovery_rows_accum.extend(
                build_discovery_rows_for_ayah(
                    surah,
                    ayah,
                    ar.truth_audit_rows,
                    ar.structured_debug_rows,
                    ar.alignment_debug_rows,
                    wi_to_gi,
                )
            )
            discovery_ayah_accum.append(
                per_ayah_discovery_summary(surah, ayah, ar.truth_audit_rows, ar.decision.value)
            )
            trapped_strict_accum.extend(
                collect_trapped_strict_rows(
                    surah,
                    ayah,
                    ar.decision.value,
                    ar.structured_debug_rows,
                    ar.reason or ar.decision.value,
                    wi_to_gi,
                )
            )
        else:
            urow: Dict[str, Any] = {"surah": surah, "ayah": ayah}
            urow.update(summarize_ayah_unlockability(ar.truth_audit_rows, ar.decision.value))
            unlockable_ayah_accum.append(urow)
        for sd in ar.structured_debug_rows:
            t = sd.get("comparator_tier", "")
            if t:
                tier_counts[t] = tier_counts.get(t, 0) + 1
        if ar.decision == AyahDecision.PASS_STRICT:
            pass_strict_ayahs += 1
        for row_d in ar.alignment_debug_rows:
            if row_d.get("row_index") != "":
                try:
                    last_row_done = max(last_row_done, int(row_d["row_index"]))
                except ValueError:
                    pass

        rows_alignment_attempts += ar.rows_total
        rows_aligned += ar.rows_total - ar.rows_skipped_alignment

        if ar.decision != AyahDecision.PASS_STRICT:
            skipped_alignment_total += ar.rows_skipped_alignment
            wrong_batch.extend(ar.wrong_payloads)
            review_rows.append(
                {
                    "surah": surah,
                    "ayah": ayah,
                    "status": ar.decision.value,
                    "reason": ar.reason,
                    "rows_total": str(ar.rows_total),
                    "rows_accepted": str(ar.rows_strict_accepted),
                    "rows_rejected": str(ar.rows_rejected_comparator),
                    "rows_skipped_alignment": str(ar.rows_skipped_alignment),
                    "repair_attempts": str(args.max_repair_attempts),
                    "last_action": "batch_eval",
                }
            )
            if ar.decision in (AyahDecision.FAIL_ALIGNMENT, AyahDecision.FAIL_ANALYSIS):
                pass
            if ar.wrong_payloads:
                rejected_rows_total += len(ar.wrong_payloads)

        if ar.decision == AyahDecision.PASS_STRICT and ar.new_erqa_payloads:
            for er in ar.new_erqa_payloads:
                rk = (int(er["surah"]), int(er["ayah"]), int(er["ayah_word_index"]))
                if rk not in erqa_keys:
                    new_erqa_batch.append(er)
                    accepted_rows_total += 1

        if ar.decision != AyahDecision.PASS_STRICT and (aligned_ct < g_rc or ar.rows_rejected_comparator):
            by_wi: Dict[int, int] = {}
            for gix, r0 in indexed:
                if r0.surah == surah and r0.ayah == ayah:
                    by_wi[int(r0.index_in_ayah)] = gix
            ggi = [by_wi.get(i) for i in range(len(gold_words))]
            from orchestrator import run_pipeline
            from orchestrator.quran_gold.alignment import align_gold_words_to_pipeline_tokens
            from orchestrator.quran_gold.analyzer_extract import get_token_surfaces

            if ayah_text:
                pl = run_pipeline(
                    ayah_text,
                    source={"entrypoint": "run_quran_i3rab_comparison", "surah": surah, "ayah": ayah},
                )
                tsurf = get_token_surfaces(pl)
            else:
                tsurf = []
            ayah_token_debug_accum.extend(
                build_token_inventory_rows(surah, ayah, gold_words, ggi, tsurf)
            )

        unsafe = ar.decision != AyahDecision.PASS_STRICT
        if unsafe and args.stop_on_first_unsafe_ayah:
            stop_reason = f"unsafe_ayah_{surah}_{ayah}_{ar.decision.value}"
            break

        if len(wrong_batch) > args.max_wrong_rows:
            stop_reason = f"max_wrong_rows_exceeded_{args.max_wrong_rows}"
            break

        last_completed_ayah = (surah, ayah)

    alignment_coverage = (
        (rows_aligned / rows_alignment_attempts) if rows_alignment_attempts > 0 else 1.0
    )

    b285 = aggregate_batch_28_5_counters(truth_audit_accum)
    b285["candidate_real_pass_strict_ayahs"] = pass_strict_ayahs

    b29_summary = batch_29_unlock.build_batch_28_9_summary_dict(
        batch_28_9_near_pass_rows,
        trapped_strict_rows_total,
        trapped_strict_ayahs_total,
        batch_28_9_best_write,
    )

    from orchestrator.quran_gold import batch_28_10_reporting as b210rep

    b210_summary = b210rep.build_batch_28_10_summary(
        comparator_tier_counts=tier_counts,
        batch_28_5=b285,
        pass_strict_ayahs=pass_strict_ayahs,
        batch_28_9=b29_summary,
        truth_audit_rows=truth_audit_accum,
    )

    from orchestrator.quran_gold import ayah_completion_ranker as acr
    from orchestrator.quran_gold import batch_28_11_reporting as b311rep

    ranking_rows = acr.build_ranking_rows_from_snapshots(per_ayah_snapshots)
    truth_by_ayah: Dict[Tuple[int, int], List[Dict[str, Any]]] = {}
    for sn in per_ayah_snapshots:
        truth_by_ayah[(int(sn["surah"]), int(sn["ayah"]))] = sn.get("truth_audit_rows") or []
    targets = acr.select_target_ayahs(ranking_rows, max_targets=5)
    acr.enrich_target_rows_with_blocker_words(targets, truth_by_ayah)
    snap_by_key = {(int(s["surah"]), int(s["ayah"])): s for s in per_ayah_snapshots}
    promoted_ayah_rows = acr.build_promoted_ayah_rows(b311rep.BATCH_28_11_BASELINE_AYAH_STATUS, per_ayah_snapshots)
    still_blocked_targets = acr.build_still_blocked_target_rows(targets, snap_by_key)
    blocker_token_examples = acr.build_blocker_token_examples(targets, snap_by_key)

    b311_summary = b311rep.build_batch_28_11_summary(
        batch_28_5=b285,
        batch_28_9=b29_summary,
        pass_strict_ayahs=pass_strict_ayahs,
        alignment_coverage=alignment_coverage,
        target_ayahs=targets,
        promoted_ayah_rows=promoted_ayah_rows,
        still_blocked_targets=still_blocked_targets,
    )

    summary: Dict[str, Any] = {
        "batch_id": batch_id,
        "timestamp": ts,
        "rows_alignment_attempts": rows_alignment_attempts,
        "rows_aligned_counter": rows_aligned,
        "alignment_coverage": round(alignment_coverage, 4),
        "accepted_rows_this_batch": len(new_erqa_batch),
        "wrong_rows_this_batch": len(wrong_batch),
        "stop_reason": stop_reason,
        "dry_run": args.dry_run,
        "write_mode": args.write_mode,
        "ayahs_processed": len(ayah_audit_rows),
        "pass_strict_ayahs": pass_strict_ayahs,
        "comparator_tier_counts": tier_counts,
        "batch_28_5": b285,
        "batch_28_9": b29_summary,
        "batch_28_10": b210_summary,
        "batch_28_11": b311_summary,
    }
    if emit_discovery:
        from orchestrator.quran_gold.discovery_reporting import aggregate_discovery_counts

        dcounts = aggregate_discovery_counts(discovery_rows_accum)
        dcounts["trapped_strict_rows"] = len(trapped_strict_accum)
        summary["batch_28_7_discovery"] = {
            **dcounts,
            "ayah_summary_rows": len(discovery_ayah_accum),
            "canonical_ayah_source": "gold_csv" if use_gold_csv_ayah else "uthmani",
        }

    print(json.dumps(summary, ensure_ascii=False, indent=2))

    can_write_erqa = (
        args.write_mode
        and (not args.dry_run)
        and (args.force_below_alignment_threshold or (alignment_coverage + 1e-9) >= args.alignment_min)
    )

    if args.write_mode and not args.dry_run and not can_write_erqa and not args.force_below_alignment_threshold:
        print(
            f"Refusing erqa writes: alignment_coverage {alignment_coverage:.2%} < {args.alignment_min:.0%}.",
            file=sys.stderr,
        )

    # Always write batch summary + progress state (for traceability)
    progress_state = {
        "current_surah": last_completed_ayah[0] if last_completed_ayah else None,
        "current_ayah": last_completed_ayah[1] if last_completed_ayah else None,
        "last_processed_row_index": last_row_done,
        "last_completed_ayah": [last_completed_ayah[0], last_completed_ayah[1]] if last_completed_ayah else prev.get("last_completed_ayah"),
        "accepted_rows_total": accepted_rows_total,
        "rejected_rows_total": rejected_rows_total,
        "skipped_alignment_total": skipped_alignment_total,
        "review_queue_ayahs_total": len(review_rows),
        "current_branch": _git_branch(),
        "last_commit_if_available": git_head_short(),
        "batch_id": batch_id,
        "updated_at": ts,
    }
    write_batch_summary(args.batch_summary.resolve(), {**summary, "progress": progress_state})
    write_progress_state(args.progress.resolve(), progress_state)

    append_repair_log(args.repair_log.resolve(), repair_rows)
    if review_rows:
        upsert_ayah_review_queue(args.ayah_review_queue.resolve(), review_rows)

    args.alignment_debug.resolve().parent.mkdir(parents=True, exist_ok=True)
    _write_alignment_debug(args.alignment_debug.resolve(), alignment_debug_accum, ALIGNMENT_DEBUG_FIELDS)
    write_ayah_audit_csv(str(args.ayah_audit.resolve()), ayah_audit_rows)
    write_ayah_token_debug_csv(str(args.ayah_token_debug.resolve()), ayah_token_debug_accum)
    from orchestrator.quran_gold.batch_quarantine import write_structured_debug_csv

    write_structured_debug_csv(args.structured_debug.resolve(), structured_debug_accum)
    write_truth_audit_csv(args.truth_audit.resolve(), truth_audit_accum)

    _root = _project_root()
    _d9 = _root / "data"
    batch_29_unlock.write_csv(
        _d9 / "quran_i3rab_batch_28_9_ayah_blocker_ranking.csv",
        batch_29_unlock.BLOCKER_RANKING_FIELDS,
        batch_28_9_blocker_rows,
    )
    batch_29_unlock.write_csv(
        _d9 / "quran_i3rab_batch_28_9_near_pass_ayahs.csv",
        batch_29_unlock.NEAR_PASS_AYAH_FIELDS,
        batch_28_9_near_pass_rows,
    )
    batch_29_unlock.write_csv(
        _d9 / "quran_i3rab_batch_28_9_unlock_preview.csv",
        batch_29_unlock.UNLOCK_PREVIEW_FIELDS,
        batch_28_9_unlock_preview,
    )
    batch_29_unlock.write_csv(
        _d9 / "quran_i3rab_batch_28_9_best_write_candidates.csv",
        batch_29_unlock.BEST_WRITE_FIELDS,
        batch_28_9_best_write,
    )

    b210rep.write_pattern_selection(_root)
    b210rep.write_before_after_json(_root, summary.get("batch_28_10") or {})
    b210rep.write_family_effects_csv(_d9 / "quran_i3rab_batch_28_10_family_effects.csv")
    b210rep.write_promoted_examples_csv(_d9 / "quran_i3rab_batch_28_10_promoted_examples.csv", truth_audit_accum)
    b210rep.write_still_blocked_examples_csv(_d9 / "quran_i3rab_batch_28_10_still_blocked_examples.csv", truth_audit_accum)

    acr.write_csv(
        _d9 / "quran_i3rab_batch_28_11_ayah_completion_ranking.csv",
        acr.AYAH_COMPLETION_RANKING_FIELDS,
        ranking_rows,
    )
    acr.write_csv(_d9 / "quran_i3rab_batch_28_11_target_ayahs.csv", acr.TARGET_AYAHS_FIELDS, targets)
    b311rep.write_before_after_json(_root, b311_summary)
    acr.write_csv(_d9 / "quran_i3rab_batch_28_11_promoted_ayahs.csv", acr.PROMOTED_AYAHS_FIELDS, promoted_ayah_rows)
    acr.write_csv(
        _d9 / "quran_i3rab_batch_28_11_still_blocked_ayahs.csv",
        acr.STILL_BLOCKED_AYAHS_FIELDS,
        still_blocked_targets,
    )
    acr.write_csv(
        _d9 / "quran_i3rab_batch_28_11_blocker_token_examples.csv",
        acr.BLOCKER_TOKEN_EXAMPLES_FIELDS,
        blocker_token_examples,
    )

    if emit_discovery:
        from orchestrator.quran_gold.discovery_reporting import (
            rank_unlockable_ayahs,
            write_discovery_ayah_summary_csv,
            write_discovery_ranked_unlockable_csv,
            write_discovery_rows_csv,
            write_trapped_strict_rows_csv,
        )

        dr_out = args.discovery_rows_out or defaults["discovery_rows"]
        das_out = args.discovery_ayah_summary_out or defaults["discovery_ayah_summary"]
        ts_out = args.trapped_strict_rows_out or defaults["trapped_strict_rows"]
        write_discovery_rows_csv(dr_out, discovery_rows_accum)
        write_discovery_ayah_summary_csv(das_out, discovery_ayah_accum)
        ranked = rank_unlockable_ayahs(discovery_ayah_accum)
        write_discovery_ranked_unlockable_csv(args.unlockable_ayahs.resolve(), ranked)
        write_trapped_strict_rows_csv(ts_out, trapped_strict_accum)
    else:
        write_unlockable_ayahs_csv(args.unlockable_ayahs.resolve(), unlockable_ayah_accum)
    write_real_accept_preview_csv(args.real_accept_preview.resolve(), real_accept_preview_accum)

    if can_write_erqa and new_erqa_batch:
        _append_erqa_rows(args.erqa.resolve(), new_erqa_batch, erqa_fields)
        for r in new_erqa_batch:
            erqa_keys.add((int(r["surah"]), int(r["ayah"]), int(r["ayah_word_index"])))

    if args.write_mode and not args.dry_run:
        _write_wrong(args.wrong.resolve(), wrong_batch, wrong_fields)

    return 0


if __name__ == "__main__":
    raise SystemExit(run())
