# -*- coding: utf-8 -*-
"""Tests for quran_gold.i3rab_compare_pipeline."""

from __future__ import annotations

import csv
from pathlib import Path

from orchestrator.quran_gold.i3rab_compare_pipeline import (
    GoldRow,
    i3rab_matches,
    load_erqa_keys,
    normalize_i3rab_text,
    run_compare_pass,
    row_key,
)


def test_normalize_and_match():
    assert normalize_i3rab_text("  abc  ") == "abc"
    assert i3rab_matches("x", "x")
    assert not i3rab_matches("x", "y")


def test_run_compare_pass_all_match(tmp_path: Path):
    gold = tmp_path / "g.csv"
    gold.write_text(
        "surah,ayah,word,i3rab\n"
        "1,1,أ,a1\n"
        "1,1,ب,b1\n",
        encoding="utf-8",
    )
    erqa = tmp_path / "erqa.csv"
    wrong = tmp_path / "wrong.csv"

    def sys_fn(s: int, a: int, words: list[str]):
        if s == 1 and a == 1 and words == ["أ", "ب"]:
            return ["a1", "b1"]
        return [None] * len(words)

    r = run_compare_pass(str(gold), str(erqa), str(wrong), sys_fn, max_wrong_run=100)
    assert r["new_matches"] == 2
    assert r["wrong_this_run"] == 0
    assert r["covered_all_gold"]
    assert erqa.is_file()
    with open(erqa, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == 2
    assert rows[0]["ayah_word_index"] == "0"
    assert rows[1]["ayah_word_index"] == "1"


def test_run_compare_pass_wrong_and_stop(tmp_path: Path):
    gold = tmp_path / "g.csv"
    gold.write_text(
        "surah,ayah,word,i3rab\n"
        "1,1,أ,gold1\n"
        "1,1,ب,gold2\n"
        "1,2,ت,gold3\n",
        encoding="utf-8",
    )
    erqa = tmp_path / "erqa.csv"
    wrong = tmp_path / "wrong.csv"

    def sys_fn(s: int, a: int, words: list[str]):
        return ["bad"] * len(words)

    r = run_compare_pass(str(gold), str(erqa), str(wrong), sys_fn, max_wrong_run=1)
    assert r["wrong_this_run"] == 2
    assert "exceeds" in r["stopped_reason"]
    with open(wrong, encoding="utf-8-sig") as f:
        wrows = list(csv.DictReader(f))
    assert len(wrows) == 2


def test_cumulative_erqa_skips_matched(tmp_path: Path):
    gold = tmp_path / "g.csv"
    gold.write_text(
        "surah,ayah,word,i3rab\n"
        "1,1,أ,ok\n"
        "1,1,ب,expected_b\n",
        encoding="utf-8",
    )
    erqa = tmp_path / "erqa.csv"
    erqa.write_text(
        "surah,ayah,word,i3rab,ayah_word_index\n"
        "1,1,أ,ok,0\n",
        encoding="utf-8-sig",
    )
    wrong = tmp_path / "wrong.csv"

    def sys_fn(s: int, a: int, words: list[str]):
        assert words == ["أ", "ب"]
        return ["ok", "wrong_sys"]

    r = run_compare_pass(str(gold), str(erqa), str(wrong), sys_fn, max_wrong_run=100)
    assert r["pending_before"] == 1
    assert r["new_matches"] == 0
    assert r["wrong_this_run"] == 1


def test_row_key_stable():
    r = GoldRow(2, 3, "w", "g", 1)
    assert row_key(r) == (2, 3, 1)


def test_load_erqa_keys_explicit_index(tmp_path: Path):
    p = tmp_path / "e.csv"
    p.write_text(
        "surah,ayah,word,i3rab,ayah_word_index\n"
        "1,1,x,ix,5\n",
        encoding="utf-8-sig",
    )
    assert load_erqa_keys(str(p)) == {(1, 1, 5)}
