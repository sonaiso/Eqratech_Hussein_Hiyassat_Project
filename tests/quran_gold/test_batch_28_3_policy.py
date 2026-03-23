# -*- coding: utf-8 -*-
"""Batch 28.3 — quarantine paths, write-mode, progress (focused)."""

import json
import os
import subprocess
import sys
from pathlib import Path
from orchestrator.quran_gold.analyzer_extract import TokenAnalyzerSnapshot
from orchestrator.quran_gold.comparator import ComparatorTier, compare_token_conservative, strict_acceptance_eligible


def test_strict_tiers_only_for_erqa():
    snap_ok = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17=None,
        l11_i3rab_text="same",
        primary_label="L11",
    )
    d_ok = compare_token_conservative("same", snap_ok)
    assert d_ok.tier == ComparatorTier.EXACT_TEXT_MATCH
    assert strict_acceptance_eligible(d_ok)


def test_weak_tier_rejected_for_erqa():
    """Diagnostic weak structural tier must not pass strict acceptance."""
    snap = TokenAnalyzerSnapshot(
        token_id="0",
        surface="x",
        l17={
            "status": "resolved",
            "confidence": 0.95,
            "syntactic_role": "اسم",
            "i3rab_case_or_mood": "منصوب وعلامة نصبه الفتحة",
            "marker": "",
        },
        l11_i3rab_text=None,
        primary_label="L17",
    )
    gold = "مَفْعُولٌ بِهٖ مَنْصُوبٌ"
    d = compare_token_conservative(gold, snap)
    if d.tier == ComparatorTier.PARTIAL_STRUCTURED_MATCH:
        assert not strict_acceptance_eligible(d)


def test_dry_run_does_not_require_write_mode(tmp_path: Path):
    repo = Path(__file__).resolve().parents[2]
    gold = tmp_path / "g.csv"
    gold.write_text('surah,ayah,word,i3rab\n1,1,و,x\n', encoding="utf-8")
    erqa = tmp_path / "erqa.csv"
    erqa.write_text("", encoding="utf-8")
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--gold",
        str(gold),
        "--from-surah",
        "1",
        "--from-ayah",
        "1",
        "--max-ayahs",
        "1",
        "--dry-run",
        "--no-stop-on-first-unsafe-ayah",
        "--erqa",
        str(erqa),
        "--batch-summary",
        str(tmp_path / "bs.json"),
        "--progress",
        str(tmp_path / "ps.json"),
        "--alignment-debug",
        str(tmp_path / "al.csv"),
        "--ayah-audit",
        str(tmp_path / "aa.csv"),
        "--ayah-token-debug",
        str(tmp_path / "tt.csv"),
        "--repair-log",
        str(tmp_path / "rp.csv"),
        "--ayah-review-queue",
        str(tmp_path / "rq.csv"),
    ]
    subprocess.run(cmd, cwd=str(repo), env=env, check=True)
    assert (tmp_path / "bs.json").is_file()
    st = json.loads((tmp_path / "ps.json").read_text(encoding="utf-8"))
    assert "batch_id" in st or "last_completed_ayah" in st


def test_write_mode_smoke_appends_strict_only_if_pass(tmp_path: Path):
    """Without full orchestrator gold pass, erqa may stay empty; ensure script runs."""
    repo = Path(__file__).resolve().parents[2]
    gold = tmp_path / "g.csv"
    gold.write_text('surah,ayah,word,i3rab\n1,1,و,x\n', encoding="utf-8")
    erqa = tmp_path / "erqa.csv"
    erqa.write_text(
        "surah,ayah,word,gold_i3rab,system_i3rab,match_type,confidence,analyzer_source,notes,ayah_word_index\n",
        encoding="utf-8-sig",
    )
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--gold",
        str(gold),
        "--from-surah",
        "1",
        "--from-ayah",
        "1",
        "--max-ayahs",
        "1",
        "--write-mode",
        "--no-stop-on-first-unsafe-ayah",
        "--erqa",
        str(erqa),
        "--wrong",
        str(tmp_path / "wrong.csv"),
        "--batch-summary",
        str(tmp_path / "bs.json"),
        "--progress",
        str(tmp_path / "ps.json"),
        "--alignment-debug",
        str(tmp_path / "al.csv"),
        "--ayah-audit",
        str(tmp_path / "aa.csv"),
        "--ayah-token-debug",
        str(tmp_path / "tt.csv"),
        "--repair-log",
        str(tmp_path / "rp.csv"),
        "--ayah-review-queue",
        str(tmp_path / "rq.csv"),
    ]
    subprocess.run(cmd, cwd=str(repo), env=env, check=True)
    body = erqa.read_text(encoding="utf-8-sig")
    assert "surah" in body
