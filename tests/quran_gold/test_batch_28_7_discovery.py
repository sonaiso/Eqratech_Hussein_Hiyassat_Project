# -*- coding: utf-8 -*-
"""Batch 28.7 — CSV-only ayah reconstruction and discovery reporting."""

import csv
import os
import subprocess
import sys
from pathlib import Path

from orchestrator.quran_gold.discovery_reporting import (
    classify_discovery_bucket,
    rank_unlockable_ayahs,
    write_discovery_rows_csv,
)
from orchestrator.quran_gold.gold_csv_ayah import (
    occurrence_ranks_by_surface,
    reconstruct_ayah_text_from_indexed,
    word_index_to_global_index,
)
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def test_reconstruct_ayah_joins_csv_word_order():
    root = Path(__file__).resolve().parents[2]
    gold = str(root / "data" / "quran_i3rab.csv")
    rows = _read_gold_rows(gold)
    indexed = list(enumerate(rows))
    t = reconstruct_ayah_text_from_indexed(indexed, 1, 1)
    words = [r.word for r in rows if r.surah == 1 and r.ayah == 1]
    assert t == " ".join(words)


def test_occurrence_ranks_repeated_surface():
    class R:
        def __init__(self, w):
            self.word = w
            self.index_in_ayah = 0

    ranks = occurrence_ranks_by_surface([R("مِن"), R("مِن")])
    assert ranks == [1, 2]


def test_word_index_to_global_index():
    root = Path(__file__).resolve().parents[2]
    rows = _read_gold_rows(str(root / "data" / "quran_i3rab.csv"))
    indexed = list(enumerate(rows))
    m = word_index_to_global_index(indexed, 1, 1)
    assert 0 in m
    assert m[0] >= 0


def test_discovery_bucket_alignment_first():
    truth = {
        "audit_bucket": "ALIGNMENT_FAILED",
        "comparator_tier_current": "mismatch",
        "potentially_unlockable_without_l17_core": "false",
    }
    assert classify_discovery_bucket(truth) == "blocked_by_alignment_or_segmentation"


def test_rank_unlockable_sorts_by_score():
    rows = [
        {
            "surah": 1,
            "ayah": 1,
            "total_rows": 2,
            "strict_acceptable_rows_now": 0,
            "tooling_unlockable_rows": 1,
            "core_blocked_rows": 0,
            "true_conflict_rows": 0,
            "gold_prose_blocked_rows": 0,
            "alignment_blocked_rows": 0,
            "recommended_action": "TOOLING_ONLY_NEXT",
        },
        {
            "surah": 1,
            "ayah": 2,
            "total_rows": 2,
            "strict_acceptable_rows_now": 2,
            "tooling_unlockable_rows": 0,
            "core_blocked_rows": 0,
            "true_conflict_rows": 0,
            "gold_prose_blocked_rows": 0,
            "alignment_blocked_rows": 0,
            "recommended_action": "PASS_NOW",
        },
    ]
    r = rank_unlockable_ayahs(rows)
    assert int(r[0]["ayah"]) == 2


def test_emit_discovery_runs_without_uthmani_file(tmp_path):
    """With --emit-discovery-csvs the runner uses gold CSV ayah text only; missing uthmani path is OK."""
    repo = Path(__file__).resolve().parents[2]
    missing_text = tmp_path / "no_uthmani_here.txt"
    gold = tmp_path / "mini.csv"
    gold.write_text(
        "surah,ayah,word,i3rab\n"
        "1,1,بِسْمِ,جار مجرور\n"
        "1,1,الرَّحْمَٰنِ,مجرور\n",
        encoding="utf-8",
    )
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--quran-text",
        str(missing_text),
        "--gold",
        str(gold),
        "--emit-discovery-csvs",
        "--discovery-limit",
        "10",
        "--dry-run",
        "--no-stop-on-first-unsafe-ayah",
        "--discovery-rows-out",
        str(tmp_path / "dr.csv"),
        "--discovery-ayah-summary-out",
        str(tmp_path / "das.csv"),
        "--trapped-strict-rows-out",
        str(tmp_path / "tr.csv"),
        "--truth-audit",
        str(tmp_path / "ta.csv"),
        "--unlockable-ayahs",
        str(tmp_path / "ua.csv"),
        "--batch-summary",
        str(tmp_path / "bs.json"),
        "--progress",
        str(tmp_path / "ps.json"),
        "--alignment-debug",
        str(tmp_path / "ad.csv"),
        "--ayah-audit",
        str(tmp_path / "aa.csv"),
        "--ayah-token-debug",
        str(tmp_path / "at.csv"),
        "--structured-debug",
        str(tmp_path / "sd.csv"),
        "--repair-log",
        str(tmp_path / "rp.csv"),
        "--ayah-review-queue",
        str(tmp_path / "rq.csv"),
        "--real-accept-preview",
        str(tmp_path / "rap.csv"),
        "--erqa",
        str(tmp_path / "erqa.csv"),
    ]
    subprocess.run(cmd, cwd=str(repo), env=env, check=True)
    assert (tmp_path / "dr.csv").is_file()


def test_discovery_rows_csv_roundtrip(tmp_path):
    rows = [
        {
            "row_index": 0,
            "surah": 1,
            "ayah": 1,
            "word": "x",
            "gold_i3rab": "g",
            "current_system_i3rab": "",
            "current_match_tier": "mismatch",
            "alignment_status": "aligned",
            "discovery_bucket": "needs_manual_review",
            "likely_unlockable_without_l17_core": "false",
            "likely_unlockable_without_pipeline_changes": "false",
            "requires_l17_core": "false",
            "requires_manual_review": "true",
            "evidence_summary": "",
            "blocking_reason": "",
            "recommended_next_action": "MANUAL_REVIEW",
        }
    ]
    p = tmp_path / "d.csv"
    write_discovery_rows_csv(p, rows)
    with open(p, encoding="utf-8-sig") as f:
        assert "discovery_bucket" in next(csv.reader(f))
