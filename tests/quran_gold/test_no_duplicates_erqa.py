# -*- coding: utf-8 -*-
import csv
from pathlib import Path

from orchestrator.quran_gold.i3rab_compare_pipeline import GoldRow, load_erqa_keys, row_key


def test_duplicate_append_same_key_not_double(tmp_path: Path):
    erqa = tmp_path / "e.csv"
    from orchestrator.quran_gold.i3rab_compare_pipeline import _append_erqa_rows

    r = GoldRow(1, 1, "w", "g", 0)
    _append_erqa_rows(
        str(erqa),
        [r],
        ("surah", "ayah", "word", "i3rab", "ayah_word_index"),
    )
    _append_erqa_rows(
        str(erqa),
        [r],
        ("surah", "ayah", "word", "i3rab", "ayah_word_index"),
    )
    with open(erqa, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == 2
    keys = load_erqa_keys(str(erqa))
    assert keys == {(1, 1, 0)}
