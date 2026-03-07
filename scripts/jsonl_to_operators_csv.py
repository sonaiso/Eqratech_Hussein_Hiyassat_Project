from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

BASE = [
    "Group Number",
    "Arabic Group Name",
    "English Group Name",
    "Operator",
    "Purpose/Usage",
    "Example",
    "Note",
]

PROJECT = [
    "project_effect_signature",
    "project_usage_universal_ar",
    "project_i3rab_template",
    "project_quran_evidence_phrases",
    "project_modules",
]

# Effect signature taxonomy: usage + i3rab template per signature.
DEFAULTS_BY_SIGNATURE: Dict[str, Dict[str, str]] = {
    "GEN": {
        "project_usage_universal_ar": "حَرْفُ جَرٍّ: يُفِيدُ جَرَّ الِاسْمِ بَعْدَهُ وَيُسَمَّى مَا بَعْدَهُ (اسْمًا مَجْرُورًا).",
        "project_i3rab_template": "حَرْفُ جَرٍّ، وَ( {NOUN} ) : اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ الظَّاهِرَةُ.",
    },
    "OATH_GEN": {
        "project_usage_universal_ar": "حَرْفُ قَسَمٍ: يُفِيدُ القَسَمَ وَيَجُرُّ مَا بَعْدَهُ.",
        "project_i3rab_template": "حَرْفُ قَسَمٍ، وَ( {NOUN} ) : اسْمٌ مَجْرُورٌ وَعَلَامَةُ جَرِّهِ الْكَسْرَةُ.",
    },
    "CONJ": {
        "project_usage_universal_ar": "حَرْفُ عَطْفٍ: يَرْبِطُ بَيْنَ مَعْطُوفٍ وَمَعْطُوفٍ عَلَيْهِ.",
        "project_i3rab_template": "حَرْفُ عَطْفٍ، وَ( {NOUN} ) : مَعْطُوفٌ ...",
    },
    "ISTITHNA": {
        "project_usage_universal_ar": "أَدَاةُ اسْتِثْنَاءٍ: تُسْتَثْنَى بِهَا مِنَ الْجُمْلَةِ.",
        "project_i3rab_template": "أَدَاةُ اسْتِثْنَاءٍ، وَ( {NOUN} ) : مُسْتَثْنًى ...",
    },
    "ACC_TAWKID": {
        "project_usage_universal_ar": "حَرْفُ تَوْكِيدٍ وَنَصْبٍ: يَنْصِبُ الِاسْمَ وَيَرْفَعُ الْخَبَرَ.",
        "project_i3rab_template": "حَرْفُ تَوْكِيدٍ وَنَصْبٍ، وَ( {NOUN} ) : اسْمُهَا مَنْصُوبٌ، وَ( {NOUN2} ) : خَبَرُهَا مَرْفُوعٌ.",
    },
    "NEG": {
        "project_usage_universal_ar": "أَدَاةُ نَفْيٍ: تُفِيدُ نَفْيَ الْمَعْنَى عَلَى حَسَبِ السِّيَاقِ.",
        "project_i3rab_template": "أَدَاةُ نَفْيٍ ...",
    },
    "COND": {
        "project_usage_universal_ar": "أَدَاةُ شَرْطٍ جَازِمَةٍ: تَجْزِمُ فِعْلَيْنِ (فِعْلَ الشَّرْطِ وَجَوَابَهُ).",
        "project_i3rab_template": "أَدَاةُ شَرْطٍ جَازِمَةٍ، وَ( {VERB1} ) : فِعْلُ الشَّرْطِ مَجْزُومٌ، وَ( {VERB2} ) : جَوَابُ الشَّرْطِ مَجْزُومٌ.",
    },
    "NIDA": {
        "project_usage_universal_ar": "أَدَاةُ نِدَاءٍ: تُسْتَعْمَلُ لِنِدَاءِ الْمُنَادَى.",
        "project_i3rab_template": "أَدَاةُ نِدَاءٍ، وَ( {NOUN} ) : مُنَادًى ...",
    },
    "NASB": {
        "project_usage_universal_ar": "أَدَاةٌ تُفِيدُ النَّصْبَ حَسَبَ بَابِهَا (تَمْيِيز/مَفْعُول/...).",
        "project_i3rab_template": "أَدَاةُ نَصْبٍ، وَ( {NOUN} ) : مَنْصُوبٌ ...",
    },
    "JAZM": {
        "project_usage_universal_ar": "أَدَاةُ جَزْمٍ: تَجْزِمُ الْفِعْلَ الْمُضَارِعَ.",
        "project_i3rab_template": "أَدَاةُ جَزْمٍ، وَ( {VERB} ) : فِعْلٌ مَجْزُومٌ ...",
    },
    "MAIYYA": {
        "project_usage_universal_ar": "وَاوُ الْمَعِيَّةِ: تُفِيدُ الْمَعِيَّةَ وَتَنْصِبُ مَا بَعْدَهَا عَلَى أَنَّهُ مَفْعُولٌ مَعَهُ.",
        "project_i3rab_template": "وَاوُ الْمَعِيَّةِ، وَ( {NOUN} ) : مَفْعُولٌ مَعَهُ مَنْصُوبٌ وَعَلَامَةُ نَصْبِهِ الْفَتْحَةُ الظَّاهِرَةُ.",
    },
    "MUQATTAAT": {
        "project_usage_universal_ar": "حُرُوفٌ مَقْطَعَةٌ فِي أَوَائِلِ السُّوَرِ، لَا يُعْرَفُ لَهَا إِعْرَابٌ وَاحِدٌ.",
        "project_i3rab_template": "",
    },
    "AMR_TA3AJJUB": {
        "project_usage_universal_ar": "أَدَاةُ أَمْرٍ أَوْ تَعَجُّبٍ إِعْرَابِيَّةٍ حَسَبَ السِّيَاقِ.",
        "project_i3rab_template": "أَدَاةُ أَمْرٍ/تَعَجُّبٍ ...",
    },
    "MUQARABA": {
        "project_usage_universal_ar": "أَفْعَالُ الْمُقَارَبَةِ: تَدُلُّ عَلَى قُرْبِ وُقُوعِ الْفِعْلِ، وَيَأْتِي بَعْدَهَا فِعْلٌ مُضَارِعٌ.",
        "project_i3rab_template": "( {VERB} ) : فِعْلٌ مِنْ أَفْعَالِ الْمُقَارَبَةِ، وَ( {VERB2} ) : فِعْلٌ مُضَارِعٌ.",
    },
    "MADH_DHAMM": {
        "project_usage_universal_ar": "أَفْعَالُ الْمَدْحِ وَالذَّمِّ: تُسْتَعْمَلُ لِلْمَدْحِ أَوِ الذَّمِّ.",
        "project_i3rab_template": "( {VERB} ) : فِعْلُ مَدْحٍ/ذَمٍّ جَامِدٌ، وَ( {NOUN} ) : فَاعِلُهُ.",
    },
}

# Arabic Group Name -> effect signature (blank = leave project fields empty).
GROUP_TO_SIGNATURE: Dict[str, str] = {
    "الجر فقط الدلالية": "GEN",
    "الحروف المقطعة": "MUQATTAAT",
    "الزمن والنفي الإعرابية": "NEG",
    "الشرط الجازمة فقط": "COND",
    "التمييز الناصبة فقط": "NASB",
    "الأوامر والتعجب الإعرابية": "AMR_TA3AJJUB",
    "التفكير الناصبة فقط": "NASB",
    "الجزم فقط النافية والشرطية": "JAZM",
    "القرب الإعرابية": "MUQARABA",
    "التقييم الرافعة فقط": "MADH_DHAMM",
    "النصب فقط الغرضية والنافية": "NASB",
    "التوكيد": "ACC_TAWKID",
    "النفي الإعرابية": "NEG",
    "أداة نداء للبعيد": "NIDA",
    "أداة نداء للقريب": "NIDA",
    "أداة نداء الأم": "NIDA",
    "أداة الاستثناء الأم": "ISTITHNA",
    "أداة نصب ومصدر": "NASB",
    "التوكيد والتشبيه": "ACC_TAWKID",
    "التوكيد والاستدراك": "ACC_TAWKID",
    "التوكيد والتمني": "ACC_TAWKID",
    "التوكيد والترجي": "ACC_TAWKID",
    "واو المصاحبة (المعيّة)": "MAIYYA",
}

# Note substring -> signature (overrides group when present; checked in order).
NOTE_OVERRIDES: List[Tuple[str, str]] = [
    ("حَرْفُ قَسَم", "OATH_GEN"),
    ("حرف قسم", "OATH_GEN"),
    ("قَسَم", "OATH_GEN"),
    ("حَرْفُ جَرّ", "GEN"),
    ("حرف جر", "GEN"),
    ("حَرْفُ عَطْف", "CONJ"),
    ("حرف عطف", "CONJ"),
    ("حَرْفُ تَوْكِيد", "ACC_TAWKID"),
    ("حرف توكيد", "ACC_TAWKID"),
    ("توكيد ونصب", "ACC_TAWKID"),
]


def _is_header_artifact(rec: Dict[str, Any]) -> bool:
    """Detect duplicate header row artifact (Operator='Operator', Arabic Group Name='Arabic Group Name')."""
    op = (rec.get("Operator") or "").strip()
    ar_group = (rec.get("Arabic Group Name") or "").strip()
    return op == "Operator" and ar_group == "Arabic Group Name"


def _signature_from_note(note: str) -> Optional[str]:
    """Infer effect signature from Note text (explicit حرف قسم / حرف جر etc.)."""
    n = (note or "").strip()
    if not n:
        return None
    for needle, sig in NOTE_OVERRIDES:
        if needle in n:
            return sig
    return None


def apply_project_defaults(rec: Dict[str, Any]) -> Dict[str, Any]:
    """Fill missing project_effect_signature, project_usage_universal_ar, project_i3rab_template from group + note."""
    out = dict(rec)
    sig = (out.get("project_effect_signature") or "").strip()
    note_sig = _signature_from_note(out.get("Note") or "")
    if note_sig:
        sig = note_sig
    if not sig:
        group = (out.get("Arabic Group Name") or "").strip()
        sig = GROUP_TO_SIGNATURE.get(group, "").strip()
    if not sig:
        return out
    defaults = DEFAULTS_BY_SIGNATURE.get(sig)
    if not defaults:
        return out
    out["project_effect_signature"] = sig
    if not (out.get("project_usage_universal_ar") or "").strip():
        out["project_usage_universal_ar"] = defaults.get("project_usage_universal_ar", "")
    if not (out.get("project_i3rab_template") or "").strip():
        out["project_i3rab_template"] = defaults.get("project_i3rab_template", "")
    return out


def _normalize_row(row: Dict[str, Any]) -> Dict[str, Any]:
    """Ensure BASE+PROJECT keys exist (empty if missing)."""
    out: Dict[str, Any] = {}
    for k in BASE:
        out[k] = (row.get(k, "") if row.get(k, "") is not None else "")
    for k in PROJECT:
        out[k] = (row.get(k, "") if row.get(k, "") is not None else "")
    return out


def _load_rows_from_jsonl(src: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with src.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if _is_header_artifact(obj):
                continue
            rec = apply_project_defaults(obj)
            rows.append(_normalize_row(rec))
    return rows


def _load_rows_from_csv(src: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with src.open("r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if _is_header_artifact(row):
                continue
            rec = apply_project_defaults(row)
            rows.append(_normalize_row(rec))
    return rows


def main() -> None:
    jsonl_src = Path("data/operators_catalog_split_enriched.jsonl")
    csv_src = Path("data/operators_catalog_split.csv")
    out = Path("data/operators_catalog_split_project.csv")

    if jsonl_src.exists():
        rows = _load_rows_from_jsonl(jsonl_src)
    elif csv_src.exists():
        rows = _load_rows_from_csv(csv_src)
    else:
        raise FileNotFoundError(
            "No input found. Expected either "
            f"{jsonl_src.as_posix()} or {csv_src.as_posix()}."
        )

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8", newline="") as g:
        w = csv.DictWriter(g, fieldnames=BASE + PROJECT)
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in (BASE + PROJECT)})


if __name__ == "__main__":
    main()