from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

# Do not strip/normalize diacritics. Only structural logic.

MAX_TYPES_PER_OPERATOR = 5
MAX_EVIDENCE_PER_TYPE = 2

# Prefixes that may attach to particles in Quran "word" column
PREFIX_CHARS: Tuple[str, ...] = ("و", "ف", "ب", "ك", "ل", "س")

# Operators that commonly appear as clitics at the start of a word (بِسْمِ, لِلَّهِ, وَاللَّهِ, كَالْ...)
CLITIC_STARTSWITH_OK: Set[str] = {"بِ", "لِ", "كَ", "وَ", "فَ", "سَ"}


# Ordered type rules: first match wins priority when we must cut to MAX_TYPES_PER_OPERATOR.
TYPE_RULES: List[Tuple[str, Tuple[str, ...]]] = [
    ("QASAM", ("حَرْفُ قَسَم", "وَقَسَم")),
    ("JAR", ("حَرْفُ جَر", "حَرْفُ جَرّ")),
    ("ATAF", ("حَرْفُ عَطْف",)),
    ("TAWKID_NASB", ("حَرْفُ تَوْكِيد", "حَرْفُ تَوكِيد", "حَرْفُ تَوْكِيدٍ")),
    ("NAFY", ("نَافِيَة", "نَفْي")),
    ("ISTITHNA", ("اسْتِثْنَاء",)),
    ("NIDA", ("نِدَاء",)),
    ("SHART", ("شَرْط",)),
    ("JAZM", ("جَزْم",)),
    ("NASB_ADAT", ("أَدَاةُ نَصْب", "أَدَاةُ نَصْبٍ", "مَصْدَر")),
    ("TARJI_TAMANNI", ("تَرَج", "تَمَن")),
    # Below: avoid falling back to OTHER where possible
    ("IBTIDA", ("حَرْفُ ابْتِدَاء",)),
    ("GHAYA", ("حَرْفُ غَايَة",)),
    ("ZAAID", ("زَائِد",)),
    ("TAFSIR", ("حَرْفُ تَفْسِير",)),
    ("TANBIH", ("حَرْفُ تَنْبِيه",)),
    ("ISTIFHAM", ("أَدَاةُ اسْتِفْهَام", "اسْتِفْهَام",)),
    ("TAHRID", ("حَرْفُ تَحْرِيض",)),
    ("RAD", ("حَرْفُ رَدْع",)),
]


@dataclass(frozen=True)
class QuranRow:
    surah: str
    ayah: str
    word: str
    i3rab: str


def _iter_quran_rows(path: Path) -> Iterable[QuranRow]:
    with path.open("r", encoding="utf-8-sig", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            yield QuranRow(
                surah=(row.get("surah") or "").strip(),
                ayah=(row.get("ayah") or "").strip(),
                word=(row.get("word") or "").strip(),
                i3rab=(row.get("i3rab") or "").strip(),
            )


def _candidate_words_for_operator(op: str) -> List[str]:
    # operator itself + prefixed variants up to 2 prefixes (no diacritics inserted)
    cands = [op]
    for p in PREFIX_CHARS:
        cands.append(p + op)
    for p1 in PREFIX_CHARS:
        for p2 in PREFIX_CHARS:
            cands.append(p1 + p2 + op)
    return cands


def _is_prefixed_form(word: str, op: str) -> bool:
    """
    Accept only forms like:
      و + op
      ف + op
      (optionally) 2 prefixes: وف + op, فل + op, ...
    Reject arbitrary 'endswith(op)' like: الْمَغْضُوبِ endswith بِ
    """
    if not word or not op:
        return False
    if word == op:
        return False
    if not word.endswith(op):
        return False
    prefix = word[: -len(op)]
    if not prefix:
        return False
    if len(prefix) > 2:
        return False
    return all(ch in PREFIX_CHARS for ch in prefix)


def _detect_types(i3rab: str) -> List[str]:
    """
    Returns ordered list of matched type codes based on TYPE_RULES priority.
    """
    if not i3rab:
        return []
    matched: List[str] = []
    for code, needles in TYPE_RULES:
        for n in needles:
            if n and n in i3rab:
                matched.append(code)
                break
    return matched


def _format_evidence(qr: QuranRow) -> str:
    return f"{qr.surah}:{qr.ayah}:{qr.word} -> {qr.i3rab}"


def build_evidence(
    operators_csv: Path,
    quran_csv: Path,
    out_csv: Path,
    out_jsonl: Path,
) -> None:
    with operators_csv.open("r", encoding="utf-8-sig", newline="") as f:
        op_reader = csv.DictReader(f)
        op_rows = list(op_reader)
        op_fieldnames = op_reader.fieldnames or []
        if not op_fieldnames:
            raise ValueError("operators CSV has no header")

    # Ensure evidence column exists in output
    if "project_quran_evidence_phrases" not in op_fieldnames:
        op_fieldnames.append("project_quran_evidence_phrases")

    quran_by_word: Dict[str, List[QuranRow]] = {}
    for qr in _iter_quran_rows(quran_csv):
        if qr.word:
            quran_by_word.setdefault(qr.word, []).append(qr)

    jsonl_records: List[dict] = []

    for row in op_rows:
        op = (row.get("Operator") or "").strip()
        if not op:
            continue

        # type -> evidences
        evid_by_type: Dict[str, List[str]] = {}
        types_order: List[str] = []

        def add_evidence(qr: QuranRow) -> None:
            types = _detect_types(qr.i3rab)
            # If no type matched, we can skip or put under OTHER.
            if not types:
                types = ["OTHER"]

            for t in types:
                if t not in evid_by_type:
                    evid_by_type[t] = []
                    types_order.append(t)

                if len(evid_by_type[t]) >= MAX_EVIDENCE_PER_TYPE:
                    continue

                s = _format_evidence(qr)
                if s not in evid_by_type[t]:
                    evid_by_type[t].append(s)

        # 1) exact/candidate matches (best)
        for w in _candidate_words_for_operator(op):
            for qr in quran_by_word.get(w, []):
                add_evidence(qr)
            # Early stop if we already have enough type coverage and filled each
            if len(types_order) >= MAX_TYPES_PER_OPERATOR and all(
                len(evid_by_type[t]) >= MAX_EVIDENCE_PER_TYPE for t in types_order[:MAX_TYPES_PER_OPERATOR]
            ):
                break

        # 1.5) clitic attached forms (e.g., بِسْمِ, لِلَّهِ, وَاللَّهِ, كَالْ...)
        if len(types_order) < MAX_TYPES_PER_OPERATOR and op in CLITIC_STARTSWITH_OK:
            for w, qrs in quran_by_word.items():
                if w.startswith(op) and len(w) > len(op):
                    for qr in qrs:
                        add_evidence(qr)
                if len(types_order) >= MAX_TYPES_PER_OPERATOR and all(
                    len(evid_by_type[t]) >= MAX_EVIDENCE_PER_TYPE for t in types_order[:MAX_TYPES_PER_OPERATOR]
                ):
                    break

        # 2) fallback: strict prefix+op endswith
        if len(types_order) < MAX_TYPES_PER_OPERATOR:
            for w, qrs in quran_by_word.items():
                if _is_prefixed_form(w, op):
                    for qr in qrs:
                        add_evidence(qr)
                if len(types_order) >= MAX_TYPES_PER_OPERATOR and all(
                    len(evid_by_type[t]) >= MAX_EVIDENCE_PER_TYPE for t in types_order[:MAX_TYPES_PER_OPERATOR]
                ):
                    break

        # Limit to max types
        kept_types = types_order[:MAX_TYPES_PER_OPERATOR]
        tagged_items: List[str] = []
        for t in kept_types:
            for s in evid_by_type.get(t, [])[:MAX_EVIDENCE_PER_TYPE]:
                tagged_items.append(f"TYPE={t}::{s}")

        row["project_quran_evidence_phrases"] = " | ".join(tagged_items)

        # JSONL record (structured)
        rec = dict(row)
        rec["project_quran_evidence_by_type"] = {t: evid_by_type[t][:MAX_EVIDENCE_PER_TYPE] for t in kept_types}
        jsonl_records.append(rec)

    out_csv.parent.mkdir(parents=True, exist_ok=True)
    with out_csv.open("w", encoding="utf-8", newline="") as g:
        w = csv.DictWriter(g, fieldnames=op_fieldnames)
        w.writeheader()
        w.writerows(op_rows)
    print("Wrote:", out_csv)

    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as f:
        for rec in jsonl_records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print("Wrote:", out_jsonl)


def main() -> None:
    build_evidence(
        operators_csv=Path("data/operators_catalog_split_project.csv"),
        quran_csv=Path("data/quran_i3rab.csv"),
        out_csv=Path("data/operators_catalog_split_project_with_evidence.csv"),
        out_jsonl=Path("data/operators_catalog_split_project_with_evidence.jsonl"),
    )


if __name__ == "__main__":
    main()
