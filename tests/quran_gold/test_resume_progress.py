# -*- coding: utf-8 -*-
import json
from pathlib import Path

from orchestrator.quran_gold.i3rab_compare_pipeline import GoldRow, row_key
from orchestrator.quran_gold.i3rab_compare_pipeline import load_erqa_keys as load_erqa_keys_legacy


def test_progress_schema_roundtrip(tmp_path: Path):
    p = tmp_path / "quran_i3rab_progress.json"
    doc = {
        "started_at": "t0",
        "updated_at": "t1",
        "last_surah": 1,
        "last_ayah": 2,
        "last_row_index": 10,
        "processed_rows": 11,
        "matched_rows_current_total": 3,
        "wrong_rows_current_total": 1,
        "alignment_ambiguous_count": 0,
        "cumulative_erqa_rows": 5,
        "stop_reason": "completed_batch",
        "completed": False,
        "gold_row_count": 100,
    }
    p.write_text(json.dumps(doc), encoding="utf-8")
    back = json.loads(p.read_text(encoding="utf-8"))
    assert back["last_row_index"] == 10


def test_erqa_key_roundtrip(tmp_path: Path):
    erqa = tmp_path / "e.csv"
    erqa.write_text(
        "surah,ayah,word,i3rab,ayah_word_index\n"
        "1,1,w,g,0\n",
        encoding="utf-8-sig",
    )
    keys = load_erqa_keys_legacy(str(erqa))
    r = GoldRow(1, 1, "w", "g", 0)
    assert row_key(r) in keys
