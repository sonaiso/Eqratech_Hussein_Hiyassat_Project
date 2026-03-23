# -*- coding: utf-8 -*-
"""Batch 28.6 — PASS_STRICT discovery + isolated write-mode (focused)."""

import csv
import json
import os
import subprocess
import sys
from pathlib import Path

from orchestrator.quran_gold.pass_strict_batch import (
    build_discovery_summary,
    load_candidates_csv_as_dict,
    load_pass_strict_ayah_keys,
    rank_ayahs_by_metric,
    write_json,
    write_pass_strict_candidates_csv,
    write_review_sample_csv,
)


def test_discovery_csv_columns_and_summary_json(tmp_path):
    rows = [
        {
            "surah": 1,
            "ayah": 1,
            "decision_status": "PASS_STRICT",
            "accepted_row_count": 1,
            "wrong_row_count": 0,
            "alignment_coverage": 1.0,
            "strict_tier_count": 1,
            "exact_tier_count": 0,
            "rows_blocked_by_l17_core": 0,
            "rows_blocked_by_true_conflict": 0,
            "rows_unlockable_now": 0,
            "reason_summary": "x",
        }
    ]
    p = tmp_path / "c.csv"
    write_pass_strict_candidates_csv(p, rows)
    with open(p, encoding="utf-8-sig") as f:
        hdr = next(csv.reader(f))
    assert "decision_status" in hdr
    assert "rows_blocked_by_l17_core" in hdr
    summ = build_discovery_summary(
        rows,
        ayahs_scanned=1,
        first_10_pass_strict=[(1, 1)],
        first_10_unlockable=[],
        top_l17=[],
        top_conflict=[],
    )
    j = tmp_path / "s.json"
    write_json(j, summ)
    data = json.loads(j.read_text(encoding="utf-8"))
    assert data["ayahs_scanned"] == 1
    assert data["pass_strict_ayahs"] == 1
    assert data["first_10_pass_strict_ayahs"][0]["surah"] == 1
    assert "top_10_blocked_by_l17_core" in data


def test_load_pass_strict_filters_only_pass_strict(tmp_path):
    p = tmp_path / "c.csv"
    p.write_text(
        "surah,ayah,decision_status,accepted_row_count,wrong_row_count,alignment_coverage,"
        "strict_tier_count,exact_tier_count,rows_blocked_by_l17_core,rows_blocked_by_true_conflict,"
        "rows_unlockable_now,reason_summary\n"
        "1,1,FAIL_COMPARATOR,0,1,0.5,0,0,0,0,0,x\n"
        "52,1,PASS_STRICT,1,0,1.0,1,0,0,0,0,y\n",
        encoding="utf-8-sig",
    )
    keys = load_pass_strict_ayah_keys(p)
    assert keys == [(52, 1)]


def test_rank_ayahs_by_metric():
    rows = [
        {"surah": 1, "ayah": 1, "rows_blocked_by_l17_core": 3},
        {"surah": 1, "ayah": 2, "rows_blocked_by_l17_core": 5},
    ]
    r = rank_ayahs_by_metric(rows, "rows_blocked_by_l17_core", 10)
    assert r[0]["ayah"] == 2


def test_review_sample_csv(tmp_path):
    p = tmp_path / "r.csv"
    write_review_sample_csv(
        p,
        [{"surah": 1, "ayah": 1, "word": "w", "gold_i3rab": "g", "system_i3rab": "s", "match_type": "exact_text_match", "analyzer_source": "L11", "notes": ""}],
        [{"surah": 1, "ayah": 2, "word": "x", "gold_i3rab": "g", "system_i3rab": "s", "notes": "mismatch", "mismatch_reason": "bad", "analyzer_source": "L11"}],
    )
    with open(p, encoding="utf-8-sig") as f:
        lines = f.readlines()
    assert len(lines) >= 3


def test_load_candidates_merge(tmp_path):
    p = tmp_path / "c.csv"
    write_pass_strict_candidates_csv(
        p,
        [
            {
                "surah": 1,
                "ayah": 1,
                "decision_status": "FAIL_COMPARATOR",
                "accepted_row_count": 0,
                "wrong_row_count": 1,
                "alignment_coverage": 0.5,
                "strict_tier_count": 0,
                "exact_tier_count": 0,
                "rows_blocked_by_l17_core": 0,
                "rows_blocked_by_true_conflict": 0,
                "rows_unlockable_now": 0,
                "reason_summary": "a",
            }
        ],
    )
    d = load_candidates_csv_as_dict(p)
    assert (1, 1) in d


def test_cli_scan_and_write_subprocess(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    cand = tmp_path / "out.csv"
    summ = tmp_path / "out.json"
    prog = tmp_path / "prog.json"
    erqa = tmp_path / "erqa.csv"
    erqa.write_text("", encoding="utf-8")
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd_scan = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--scan-pass-strict",
        "--from-surah",
        "52",
        "--from-ayah",
        "1",
        "--max-ayahs",
        "1",
        "--pass-strict-candidates-out",
        str(cand),
        "--pass-strict-scan-summary-out",
        str(summ),
        "--progress",
        str(prog),
        "--erqa",
        str(erqa),
    ]
    subprocess.run(cmd_scan, cwd=str(repo), env=env, check=True)
    assert cand.is_file() and summ.is_file()
    batch_root = tmp_path / "wb"
    cmd_write = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--write-mode-pass-strict-only",
        "--candidate-source",
        str(cand),
        "--max-write-ayahs",
        "1",
        "--write-batch-root",
        str(batch_root),
        "--allow-non-isolated-output",
        "--write-batch-id",
        "tbatch",
        "--progress",
        str(tmp_path / "wprog.json"),
        "--erqa",
        str(erqa),
    ]
    subprocess.run(cmd_write, cwd=str(repo), env=env, check=True)
    bdir = batch_root / "tbatch"
    assert (bdir / "erqa_i3rab.csv").is_file()
    assert (bdir / "manifest.json").is_file()
    assert (bdir / "review_sample.csv").is_file()
    assert (bdir / "wrong_i3rab.csv").is_file()


def test_non_isolated_batch_dir_refused_without_flag(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    cand = tmp_path / "cand.csv"
    cand.write_text(
        "surah,ayah,decision_status,accepted_row_count,wrong_row_count,alignment_coverage,"
        "strict_tier_count,exact_tier_count,rows_blocked_by_l17_core,rows_blocked_by_true_conflict,"
        "rows_unlockable_now,reason_summary\n"
        "52,1,PASS_STRICT,1,0,1.0,1,0,0,0,0,y\n",
        encoding="utf-8-sig",
    )
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    p = subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--write-mode-pass-strict-only",
            "--candidate-source",
            str(cand),
            "--write-batch-root",
            str(tmp_path / "outside"),
            "--write-batch-id",
            "bad",
            "--progress",
            str(tmp_path / "p.json"),
            "--erqa",
            str(tmp_path / "e.csv"),
        ],
        cwd=str(repo),
        env=env,
        capture_output=True,
        text=True,
    )
    assert p.returncode == 2
    assert "non-isolated" in (p.stderr or "").lower()


def test_write_refuses_zero_pass_strict(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    bad = tmp_path / "bad.csv"
    bad.write_text(
        "surah,ayah,decision_status,accepted_row_count,wrong_row_count,alignment_coverage,"
        "strict_tier_count,exact_tier_count,rows_blocked_by_l17_core,rows_blocked_by_true_conflict,"
        "rows_unlockable_now,reason_summary\n"
        "1,1,FAIL_COMPARATOR,0,1,0.5,0,0,0,0,0,x\n",
        encoding="utf-8-sig",
    )
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    p = subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--write-mode-pass-strict-only",
            "--candidate-source",
            str(bad),
            "--write-batch-root",
            str(tmp_path / "wb"),
            "--allow-non-isolated-output",
            "--write-batch-id",
            "x",
            "--progress",
            str(tmp_path / "p.json"),
            "--erqa",
            str(tmp_path / "e.csv"),
        ],
        cwd=str(repo),
        env=env,
        capture_output=True,
        text=True,
    )
    assert p.returncode == 2


def test_resume_scan_no_duplicate_ayah(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    cand = tmp_path / "cand.csv"
    summ = tmp_path / "summ.json"
    prog = tmp_path / "prog.json"
    erqa = tmp_path / "erqa.csv"
    erqa.write_text("", encoding="utf-8")
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--scan-pass-strict",
            "--from-surah",
            "52",
            "--from-ayah",
            "1",
            "--max-ayahs",
            "1",
            "--pass-strict-candidates-out",
            str(cand),
            "--pass-strict-scan-summary-out",
            str(summ),
            "--progress",
            str(prog),
            "--erqa",
            str(erqa),
        ],
        cwd=str(repo),
        env=env,
        check=True,
    )
    subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--scan-pass-strict",
            "--resume-scan",
            "--from-surah",
            "52",
            "--from-ayah",
            "1",
            "--max-ayahs",
            "2",
            "--pass-strict-candidates-out",
            str(cand),
            "--pass-strict-scan-summary-out",
            str(summ),
            "--progress",
            str(prog),
            "--erqa",
            str(erqa),
        ],
        cwd=str(repo),
        env=env,
        check=True,
    )
    with open(cand, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    keys_52_1 = [r for r in rows if r.get("surah") == "52" and r.get("ayah") == "1"]
    assert len(keys_52_1) == 1
    assert len(rows) >= 2


def test_resume_write_skips_completed_ayah(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    cand = tmp_path / "cand.csv"
    cand.write_text(
        "surah,ayah,decision_status,accepted_row_count,wrong_row_count,alignment_coverage,"
        "strict_tier_count,exact_tier_count,rows_blocked_by_l17_core,rows_blocked_by_true_conflict,"
        "rows_unlockable_now,reason_summary\n"
        "52,1,PASS_STRICT,1,0,1.0,1,0,0,0,0,y\n",
        encoding="utf-8-sig",
    )
    erqa = tmp_path / "erqa.csv"
    erqa.write_text("", encoding="utf-8")
    wprog = tmp_path / "wprog.json"
    batch_root = tmp_path / "wb"
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--write-mode-pass-strict-only",
            "--candidate-source",
            str(cand),
            "--max-write-ayahs",
            "1",
            "--write-batch-root",
            str(batch_root),
            "--allow-non-isolated-output",
            "--write-batch-id",
            "rw",
            "--progress",
            str(wprog),
            "--erqa",
            str(erqa),
        ],
        cwd=str(repo),
        env=env,
        check=True,
    )
    subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
            "--write-mode-pass-strict-only",
            "--resume-write",
            "--candidate-source",
            str(cand),
            "--max-write-ayahs",
            "1",
            "--write-batch-root",
            str(batch_root),
            "--allow-non-isolated-output",
            "--write-batch-id",
            "rw",
            "--progress",
            str(wprog),
            "--erqa",
            str(erqa),
        ],
        cwd=str(repo),
        env=env,
        check=True,
    )
    with open(batch_root / "rw" / "erqa_i3rab.csv", encoding="utf-8-sig") as f:
        n = sum(1 for _ in csv.DictReader(f))
    assert n == 1
