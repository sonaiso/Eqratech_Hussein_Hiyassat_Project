# -*- coding: utf-8 -*-
"""Batch 28.15 — accepted ERQA metadata canonicalization (single decisive signature, display-aligned case/marker)."""

import csv
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from orchestrator.quran_gold.accepted_row_serializer import (
    canonicalize_accepted_metadata,
    validate_accepted_row_invariants,
)
from orchestrator.quran_gold.comparator import ComparatorTier, MatchDecision


def _dec() -> MatchDecision:
    return MatchDecision(
        tier=ComparatorTier.STRICT_STRUCTURAL_MATCH,
        confidence=0.9,
        analyzer_source="L17",
        system_i3rab_display="",
        notes="test",
        trace=None,
    )


def test_genitive_display_cannot_retain_nominative_case_bucket():
    disp = "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    tr = {"gold_case_bucket": "nominative", "gold_role": "ism_majrur"}
    can = canonicalize_accepted_metadata(
        canonical_role="ism_majrur",
        system_i3rab=disp,
        gold_i3rab=disp,
        l17=None,
        trace=tr,
        dec=_dec(),
    )
    assert can["accepted_case_bucket"] == "genitive"
    assert can["accepted_marker"] in ("", "الكسرة")


def test_naat_row_cannot_retain_mubtada_in_signature():
    disp = "نَعْتٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    can = canonicalize_accepted_metadata(
        canonical_role="naat",
        system_i3rab=disp,
        gold_i3rab=disp,
        l17={"syntactic_role": "مبتدأ", "governing_factor": "", "marker": "", "i3rab_case_or_mood": ""},
        trace={"l17_codes": "mubtada,naat"},
        dec=_dec(),
    )
    assert can["accepted_structured_signature"] == "naat"
    assert "mubtada" not in can["accepted_structured_signature"]


def test_mudaf_ilaih_no_contradictory_union_signature():
    disp = "مُضَافٌ إِلَيْهِ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    l17 = {
        "syntactic_role": "مضاف إليه",
        "governing_factor": "المضاف",
        "i3rab_case_or_mood": "مجرور",
        "marker": "الكسرة",
    }
    can = canonicalize_accepted_metadata(
        canonical_role="mudaf_ilaih",
        system_i3rab=disp,
        gold_i3rab=disp,
        l17=l17,
        trace=None,
        dec=_dec(),
    )
    assert can["accepted_structured_signature"] == "mudaf_ilaih"
    assert "," not in can["accepted_structured_signature"]


def test_ism_majrur_row_stays_valid_when_final_role():
    disp = "اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ."
    can = canonicalize_accepted_metadata(
        canonical_role="ism_majrur",
        system_i3rab=disp,
        gold_i3rab=disp,
        l17=None,
        trace=None,
        dec=_dec(),
    )
    assert can["accepted_structured_signature"] == "ism_majrur"
    assert can["accepted_case_bucket"] == "genitive"
    assert validate_accepted_row_invariants(
        {
            "accepted_role": can["accepted_role"],
            "accepted_case_bucket": can["accepted_case_bucket"],
            "accepted_marker": can["accepted_marker"],
            "accepted_structured_signature": can["accepted_structured_signature"],
            "system_i3rab": can["system_i3rab"],
        }
    ) == []


def _run_write_subprocess(tmp_path: Path, *, from_ayah: int, max_ayahs: int) -> dict:
    repo = Path(__file__).resolve().parents[2]
    out = tmp_path / f"w_{from_ayah}_{max_ayahs}"
    out.mkdir(parents=True)
    erqa = out / "erqa_i3rab.csv"
    erqa.write_text("", encoding="utf-8")
    summ = out / "batch_summary.json"
    env = {**os.environ, "PYTHONPATH": str(repo / "src")}
    cmd = [
        sys.executable,
        str(repo / "scripts" / "run_quran_i3rab_comparison.py"),
        "--from-surah",
        "1",
        "--from-ayah",
        str(from_ayah),
        "--max-ayahs",
        str(max_ayahs),
        "--write-mode",
        "--max-wrong-rows",
        "500",
        "--canonical-ayah-source",
        "gold_csv",
        "--erqa",
        str(erqa),
        "--wrong",
        str(out / "wrong_i3rab.csv"),
        "--ayah-review-queue",
        str(out / "ayah_review_queue.csv"),
        "--progress",
        str(out / "progress_state.json"),
        "--batch-summary",
        str(summ),
    ]
    subprocess.run(cmd, cwd=str(repo), env=env, check=True)
    return json.loads(summ.read_text(encoding="utf-8"))


@pytest.mark.slow
def test_isolated_write_1_1_counts(tmp_path):
    s = _run_write_subprocess(tmp_path, from_ayah=1, max_ayahs=1)
    assert s["accepted_rows_this_batch"] == 4
    assert s["wrong_rows_this_batch"] == 0
    assert s["pass_strict_ayahs"] == 1


@pytest.mark.slow
def test_isolated_write_1_2_counts(tmp_path):
    s = _run_write_subprocess(tmp_path, from_ayah=2, max_ayahs=1)
    assert s["accepted_rows_this_batch"] == 4
    assert s["wrong_rows_this_batch"] == 0
    assert s["pass_strict_ayahs"] == 1


@pytest.mark.slow
def test_isolated_write_1_3_counts(tmp_path):
    s = _run_write_subprocess(tmp_path, from_ayah=3, max_ayahs=1)
    assert s["accepted_rows_this_batch"] == 2
    assert s["wrong_rows_this_batch"] == 0
    assert s["pass_strict_ayahs"] == 1


@pytest.mark.slow
def test_connected_write_1_1_to_1_3_counts(tmp_path):
    s = _run_write_subprocess(tmp_path, from_ayah=1, max_ayahs=3)
    assert s["accepted_rows_this_batch"] == 10
    assert s["wrong_rows_this_batch"] == 0
    assert s["pass_strict_ayahs"] == 3


@pytest.mark.slow
def test_connected_erqa_rows_no_contradictory_metadata(tmp_path):
    _run_write_subprocess(tmp_path, from_ayah=1, max_ayahs=3)
    out = tmp_path / "w_1_3"
    erqa = out / "erqa_i3rab.csv"
    with erqa.open(encoding="utf-8", newline="") as f:
        for row in csv.DictReader(f):
            issues = validate_accepted_row_invariants(row)
            assert issues == [], issues
            sig = (row.get("accepted_structured_signature") or "").strip()
            if (row.get("match_type") or "") == "strict_structural_match" and sig:
                assert "," not in sig
