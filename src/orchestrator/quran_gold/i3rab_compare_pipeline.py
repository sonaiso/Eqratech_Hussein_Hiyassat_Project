# -*- coding: utf-8 -*-
"""
Compare pipeline gold (`data/quran_i3rab.csv`) to system iʿrāb strings.

- `erqa_i3rab.csv`: cumulative rows where system text matches gold (append, deduped).
- `wrong_i3rab.csv`: rows that failed in the **current run only** (overwrite each run).

Stop when every gold row is in erqa, or when current-run wrong count exceeds `max_wrong_run`.
"""

from __future__ import annotations

import csv
import os
import unicodedata
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

RowKey = Tuple[int, int, int]  # surah, ayah, index within ayah (CSV order)


@dataclass(frozen=True)
class GoldRow:
    surah: int
    ayah: int
    word: str
    i3rab: str
    index_in_ayah: int


def normalize_i3rab_text(s: str) -> str:
    """NFC + strip; use for equality checks."""
    if s is None:
        return ""
    return unicodedata.normalize("NFC", (s or "").strip())


def i3rab_matches(gold: str, system: str) -> bool:
    return normalize_i3rab_text(gold) == normalize_i3rab_text(system)


def extract_l11_i3rab_sequence(pipeline: Dict[str, Any], token_count: int) -> List[Optional[str]]:
    """Read L11 `i3rab_text` per token in pipeline token order (index-aligned to gold words)."""
    lo = pipeline.get("layer_outputs") or {}
    tr = (lo.get("L11_I3RAB") or {}).get("transformation_result") or {}
    results = tr.get("token_results") or []
    out: List[Optional[str]] = []
    for i in range(int(token_count)):
        if i >= len(results):
            out.append(None)
            continue
        t = results[i]
        txt = (t.get("i3rab_text") or "").strip()
        out.append(txt if txt else None)
    return out


def _read_gold_rows(csv_path: str) -> List[GoldRow]:
    rows: List[GoldRow] = []
    with open(csv_path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        per_ayah: Dict[Tuple[int, int], int] = {}
        for row in reader:
            try:
                surah = int((row.get("surah") or "").strip())
                ayah = int((row.get("ayah") or "").strip())
            except (TypeError, ValueError):
                continue
            word = (row.get("word") or "").strip()
            i3rab = (row.get("i3rab") or "").strip()
            if not word:
                continue
            k = (surah, ayah)
            idx = per_ayah.get(k, 0)
            per_ayah[k] = idx + 1
            rows.append(GoldRow(surah=surah, ayah=ayah, word=word, i3rab=i3rab, index_in_ayah=idx))
    return rows


def row_key(r: GoldRow) -> RowKey:
    return (r.surah, r.ayah, r.index_in_ayah)


def load_erqa_keys(erqa_path: str) -> Set[RowKey]:
    if not os.path.isfile(erqa_path):
        return set()
    out: Set[RowKey] = set()
    with open(erqa_path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        per_ayah_fallback: Dict[Tuple[int, int], int] = {}
        for row in reader:
            try:
                surah = int((row.get("surah") or "").strip())
                ayah = int((row.get("ayah") or "").strip())
            except (TypeError, ValueError):
                continue
            raw_idx = (row.get("ayah_word_index") or "").strip()
            if raw_idx != "":
                try:
                    idx = int(raw_idx)
                except ValueError:
                    continue
            else:
                k = (surah, ayah)
                idx = per_ayah_fallback.get(k, 0)
                per_ayah_fallback[k] = idx + 1
            out.add((surah, ayah, idx))
    return out


def _append_erqa_rows(erqa_path: str, new_rows: Sequence[GoldRow], fieldnames: Sequence[str]) -> None:
    file_exists = os.path.isfile(erqa_path) and os.path.getsize(erqa_path) > 0
    with open(erqa_path, "a", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=list(fieldnames))
        if not file_exists:
            writer.writeheader()
        for r in new_rows:
            writer.writerow(
                {
                    "surah": r.surah,
                    "ayah": r.ayah,
                    "word": r.word,
                    "i3rab": r.i3rab,
                    "ayah_word_index": r.index_in_ayah,
                }
            )


def _write_wrong_rows(wrong_path: str, rows: Sequence[dict]) -> None:
    fieldnames = ["surah", "ayah", "word", "i3rab", "system_i3rab", "ayah_word_index"]
    with open(wrong_path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for row in rows:
            w.writerow(row)


SystemAyahFn = Callable[[int, int, Sequence[str]], Sequence[Optional[str]]]


def run_compare_pass(
    gold_csv_path: str,
    erqa_csv_path: str,
    wrong_csv_path: str,
    system_i3rab_for_ayah: SystemAyahFn,
    *,
    max_wrong_run: int = 100,
    gold_rows: Optional[Sequence[GoldRow]] = None,
) -> dict:
    """
    One pass: extend erqa with new matches; write wrong_csv with **this run's** failures only.

    Returns a summary dict: pending_before, new_matches, wrong_this_run, stopped_reason,
    covered_all_gold.
    """
    gold_list = list(gold_rows) if gold_rows is not None else _read_gold_rows(gold_csv_path)
    total = len(gold_list)
    erqa_keys = load_erqa_keys(erqa_csv_path)
    pending = {row_key(r) for r in gold_list if row_key(r) not in erqa_keys}

    wrong_out: List[dict] = []
    new_erqa: List[GoldRow] = []
    wrong_run = 0
    stopped_reason = "completed_scan"

    pending_start = len(pending)

    # Group gold rows by (surah, ayah) preserving global order
    by_ayah: Dict[Tuple[int, int], List[GoldRow]] = {}
    order: List[Tuple[int, int]] = []
    for r in gold_list:
        k = (r.surah, r.ayah)
        if k not in by_ayah:
            by_ayah[k] = []
            order.append(k)
        by_ayah[k].append(r)

    for k in order:
        ayah_rows = by_ayah[k]
        if not any(row_key(r) in pending for r in ayah_rows):
            continue

        words = [r.word for r in ayah_rows]
        try:
            system_seq = system_i3rab_for_ayah(ayah_rows[0].surah, ayah_rows[0].ayah, words)
        except Exception:
            system_seq = [None] * len(words)

        if len(system_seq) < len(words):
            system_seq = list(system_seq) + [None] * (len(words) - len(system_seq))

        for i, r in enumerate(ayah_rows):
            if row_key(r) not in pending:
                continue

            sys_text = system_seq[i] if i < len(system_seq) else None
            gold_text = r.i3rab

            match = sys_text is not None and i3rab_matches(gold_text, sys_text)
            if match:
                new_erqa.append(r)
                erqa_keys.add(row_key(r))
                pending.discard(row_key(r))
            else:
                wrong_run += 1
                wrong_out.append(
                    {
                        "surah": r.surah,
                        "ayah": r.ayah,
                        "word": r.word,
                        "i3rab": gold_text,
                        "system_i3rab": (sys_text or ""),
                        "ayah_word_index": r.index_in_ayah,
                    }
                )
                if wrong_run > max_wrong_run:
                    stopped_reason = f"wrong_run_exceeds_{max_wrong_run}"
                    break

        if wrong_run > max_wrong_run:
            break

    if new_erqa:
        _append_erqa_rows(
            erqa_csv_path,
            new_erqa,
            ("surah", "ayah", "word", "i3rab", "ayah_word_index"),
        )

    _write_wrong_rows(wrong_csv_path, wrong_out)

    covered_all = total > 0 and len(pending) == 0
    if covered_all and stopped_reason == "completed_scan":
        stopped_reason = "all_gold_rows_in_erqa"

    return {
        "gold_row_count": total,
        "pending_before": pending_start,
        "new_matches": len(new_erqa),
        "wrong_this_run": wrong_run,
        "stopped_reason": stopped_reason,
        "covered_all_gold": covered_all,
        "remaining_pending": len(pending),
    }
