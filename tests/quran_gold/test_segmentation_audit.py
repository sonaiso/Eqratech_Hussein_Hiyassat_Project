# -*- coding: utf-8 -*-
"""Segmentation audit CSV helpers and alignment diagnostics (Batch 28.2)."""

import csv
import os
import subprocess
import sys
from pathlib import Path

from orchestrator.quran_gold.alignment import (
    SEG_NO_FORWARD,
    SEG_TOKEN_COUNT_MISMATCH,
    align_gold_words_to_pipeline_tokens,
)
from orchestrator.quran_gold.segmentation_audit import (
    AyahAuditRow,
    build_token_inventory_rows,
    summarize_ayah_reason,
    write_ayah_audit_csv,
    write_ayah_token_debug_csv,
)


def test_same_surface_different_occurrence_aligns_in_order():
    """Duplicate surfaces in one ayah: order preserved by occurrence index."""
    gold = ["ما", "ذَا", "ما"]
    tok = ["ما", "ذَا", "ما"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert all(x.token_index == i for i, x in enumerate(r))


def test_prefixed_wa_token_aligns():
    gold = ["إِيَّاكَ"]
    tok = ["وَإِيَّاكَ"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].token_index == 0
    assert r[0].outcome.value.startswith("aligned")


def test_split_merge_two_tokens_one_gold():
    gold = ["مِنْ"]
    tok = ["مِ", "نْ"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].pipeline_span == 2
    assert r[0].reason == "likely_split_merge_mismatch"


def test_unsafe_split_merge_still_skipped():
    """No spurious merge when pair does not equal gold (equal token counts)."""
    gold = ["زَيْتٌ", "ثَانٍ"]
    tok = ["مِن", "ق"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].token_index is None
    assert r[0].reason == SEG_NO_FORWARD


def test_token_count_mismatch_reason_on_failure():
    gold = ["أ", "ب", "ج"]
    tok = ["أ", "ب"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[2].reason == SEG_TOKEN_COUNT_MISMATCH
    assert r[2].segmentation_reason == SEG_TOKEN_COUNT_MISMATCH


def test_write_ayah_audit_and_token_debug(tmp_path: Path):
    audit_path = tmp_path / "ayah_audit.csv"
    dbg_path = tmp_path / "tok.csv"
    rows = [
        AyahAuditRow(1, 1, 2, 2, 2, 0, 0, False, False, "ok"),
    ]
    write_ayah_audit_csv(str(audit_path), rows)
    inv = build_token_inventory_rows(1, 1, ["a", "b"], [10, 11], ["a", "b"])
    write_ayah_token_debug_csv(str(dbg_path), inv)
    assert audit_path.is_file() and dbg_path.is_file()
    with open(audit_path, encoding="utf-8-sig") as f:
        rdr = csv.DictReader(f)
        row = next(iter(rdr))
        assert row["surah"] == "1" and row["token_counts_differ"] == "false"
    text = dbg_path.read_text(encoding="utf-8-sig")
    assert "gold_word" in text and "pipeline_token" in text


def test_summarize_ayah_reason():
    assert "token_count" in summarize_ayah_reason(True, False, 0, 0)
    assert "order" in summarize_ayah_reason(False, True, 0, 0)


def test_dry_run_script_writes_ayah_audit_files(tmp_path: Path):
    repo = Path(__file__).resolve().parents[2]
    gold = tmp_path / "mini_gold.csv"
    gold.write_text(
        'surah,ayah,word,i3rab\n1,1,بِسْمِ,"x"\n1,1,اللَّهِ,"y"\n',
        encoding="utf-8",
    )
    audit = tmp_path / "ayah_audit.csv"
    tokdbg = tmp_path / "ayah_tok.csv"
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--gold",
        str(gold),
        "--max-rows",
        "2",
        "--from-surah",
        "1",
        "--from-ayah",
        "1",
        "--max-ayahs",
        "1",
        "--dry-run",
        "--no-stop-on-first-unsafe-ayah",
        "--ayah-audit",
        str(audit),
        "--ayah-token-debug",
        str(tokdbg),
        "--alignment-debug",
        str(tmp_path / "align.csv"),
        "--batch-summary",
        str(tmp_path / "sum.json"),
        "--progress",
        str(tmp_path / "progress_state.json"),
    ]
    subprocess.run(cmd, cwd=str(repo), env=env, check=True)
    assert audit.is_file() and tokdbg.is_file()
    assert audit.stat().st_size > 50
