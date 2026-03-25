# -*- coding: utf-8 -*-
"""Partition A: ``verify_erqa_integrity`` / ``--verify-erqa`` (exact ERQA ayah set, not contiguous prefix)."""

from __future__ import annotations

import csv
from pathlib import Path

import pytest

from orchestrator.quran_gold.ayah_batch_runner import verify_erqa_integrity
from orchestrator.quran_gold.i3rab_compare_pipeline import _read_gold_rows


def _indexed_rows(gold_path: Path):
    rows = _read_gold_rows(str(gold_path))
    return list(enumerate(rows))


@pytest.fixture
def gold_path(project_root: Path) -> Path:
    p = project_root / "data" / "quran_i3rab.csv"
    if not p.is_file():
        pytest.skip("data/quran_i3rab.csv not present")
    return p


@pytest.fixture
def project_root() -> Path:
    return Path(__file__).resolve().parents[2]


def test_verify_erqa_empty_file_passes(tmp_path: Path, gold_path: Path) -> None:
    erqa = tmp_path / "empty.csv"
    erqa.write_text("surah,ayah,word\n", encoding="utf-8-sig")
    indexed = _indexed_rows(gold_path)

    def txt(s: int, a: int) -> str:
        return ""

    rep = verify_erqa_integrity(str(erqa), indexed, txt, max_repair_attempts=1)
    assert rep.total_finished_rows == 0
    assert rep.status == "PASS"


def test_verify_erqa_duplicate_key_fails(tmp_path: Path, gold_path: Path) -> None:
    erqa = tmp_path / "dup.csv"
    with erqa.open("w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(
            f,
            fieldnames=["surah", "ayah", "word", "ayah_word_index", "gold_i3rab", "system_i3rab", "match_type"],
        )
        w.writeheader()
        row = {
            "surah": "1",
            "ayah": "1",
            "word": "x",
            "ayah_word_index": "0",
            "gold_i3rab": "y",
            "system_i3rab": "y",
            "match_type": "strict_structural_match",
        }
        w.writerow(row)
        w.writerow(dict(row))

    indexed = _indexed_rows(gold_path)

    rep = verify_erqa_integrity(str(erqa), indexed, lambda s, a: "", max_repair_attempts=1)
    assert rep.duplicate_key_rows == 1
    assert rep.corrupted_rows >= 1
    assert rep.status == "FAIL"
    assert any(f.get("reason") == "duplicate_erqa_key" for f in rep.failures)


def test_verify_erqa_fatiha_subset_passes(tmp_path: Path, gold_path: Path, project_root: Path) -> None:
    """Copy a few real ERQA rows (1:1–1:2) — must still strict-match current pipeline."""
    src = project_root / "data" / "erqa_i3rab.csv"
    if not src.is_file():
        pytest.skip("data/erqa_i3rab.csv not present")
    lines = src.read_text(encoding="utf-8-sig").splitlines()
    if len(lines) < 8:
        pytest.skip("erqa too small")
    out = tmp_path / "slice.csv"
    out.write_text("\n".join(lines[:8]) + "\n", encoding="utf-8-sig")

    from orchestrator.quran_gold.ayah_loader import default_quran_text_path, load_ayah_text_index

    text_path = default_quran_text_path()
    if not Path(text_path).is_file():
        pytest.skip("quran text missing")
    load_ayah_text_index(text_path)
    indexed = _indexed_rows(gold_path)

    def ayah_text_fn(surah: int, ayah: int) -> str:
        from orchestrator.quran_gold.ayah_loader import get_ayah_text

        return get_ayah_text(surah, ayah, text_path=text_path) or ""

    rep = verify_erqa_integrity(str(out), indexed, ayah_text_fn, max_repair_attempts=2)
    assert rep.total_finished_ayahs >= 1
    assert rep.status == "PASS", rep.failures[:3]
