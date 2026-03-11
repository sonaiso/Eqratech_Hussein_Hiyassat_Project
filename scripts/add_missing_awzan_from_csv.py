#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Add missing awzan (patterns) to data/awzan_merged_final.csv by deriving them from
out_with_sources.csv: for each (word, root) that has root but empty word_wazn,
derive the pattern (replace root letters with ف ع ل), then append unique new
patterns to the CSV.

قيد: نضيف الوزن بدون سوابق ولا لواحق ولا أل التعريف.
- لا سوابق: الوزن يبدأ بأحد (ف، أ، ا، ت، ي، ن) فقط — لا و، ب، ك، ل، ولا ال/ٱل.
- لا لواحق: الوزن ينتهي بآخر حرف جذر (ل) — لا ضمائر مثل ون، ان، هم، ها، إلخ.
- تطبيع: نطبّع الألف الخنجرية (ٰ U+0670) إلى ا قبل استنتاج الوزن.
- استبعاد: لا نستنتج من كلمات نداء (يا+كلمة)، ولا من فَ+أَلِف ولا فَ+س (مثل فَسَتُرْضِعُ).
- تجريد السوابق من الوزن المستنتج: فَلْيَسْتَفْعِلْ → يَسْتَفْعِلْ، إلخ.
- استبعاد الضمائر: نزع لواحق الضمير (ون، نا، هم، ها، كم، إلخ) من الكلمة قبل استنتاج الوزن — تَأْمُرُونَنَآ → تَأْمُرُ.
- نزع الحركة الإعرابية من آخر حرف في الوزن: تَفْعُلُ → تَفْعُل.
- نزع همزة الاستفهام من أول الوزن (أَتَسْتَفْعِل → تَسْتَفْعِل). نزع فَنَ (فَنَتَبَرَّأَ → تَفَعَّلَ).
"""
import csv
import sys
from pathlib import Path

DIAC = set("\u064b\u064c\u064d\u064e\u064f\u0650\u0651\u0652\u0653\u0654\u0655\u0670")
DAGGER_ALIF = "\u0670"  # ٰ
# حركات إعرابية تُنزع من آخر حرف في الوزن
FINAL_HARAKAT = frozenset("\u064e\u064f\u0650\u064b\u064c\u064d")  # َ ُ ِ ً ٌ ٍ
# لواحق الضمائر (أساس الحروف فقط، الأطول أولاً)
PRONOUN_SUFFIX_BASES = [
    ["و", "ن", "ن", "ا"],  # وننا
    ["و", "ن"], ["ا", "ن"], ["ي", "ن"], ["ا", "ت"],
    ["ه", "م"], ["ه", "ن"], ["ه", "ا"], ["ك", "م"], ["ك", "ن"], ["ن", "ا"],
]


def normalize_dagger_alif(text: str) -> str:
    """تطبيع الألف الخنجرية قبل استنتاج الوزن."""
    return (text or "").replace(DAGGER_ALIF, "\u0627")


def strip_pronoun_suffixes(word: str) -> str:
    """
    نزع لواحق الضمائر من آخر الكلمة (ون، نا، هم، ها، كم، إلخ).
    تَأْمُرُونَنَآ → تَأْمُرُ. يُرجع الجذع فقط إن بقي فيه ما يكفي من الحروف.
    """
    units = word_to_units(word or "")
    if len(units) < 4:
        return word
    bases = [u[0] for u in units]
    removed = True
    while removed and len(units) >= 3:
        removed = False
        for suf in PRONOUN_SUFFIX_BASES:
            if len(units) < len(suf):
                continue
            tail_bases = [u[0] for u in units[-len(suf):]]
            if tail_bases == suf:
                units = units[:-len(suf)]
                removed = True
                break
    return "".join(b + d for b, d in units)


def strip_final_haraka(pattern: str) -> str:
    """
    نزع الحركة الإعرابية من الحرف الأخير في الوزن (ليست من أصل الوزن).
    تَفْعُلُ → تَفْعُل، فَعَلَ → فَعَل.
    """
    if not pattern:
        return pattern
    units = word_to_units(pattern)
    if not units:
        return pattern
    base, diacs = units[-1]
    if diacs:
        new_diacs = "".join(c for c in diacs if c not in FINAL_HARAKAT)
        units[-1] = (base, new_diacs)
    return "".join(b + d for b, d in units)


def should_skip_word(word: str) -> bool:
    """
    استبعاد كلمة فلا نستنتج منها وزناً:
    - يا + كلمة (نداء): يَٰٓأُولِي، يَٰدَاوُۥدُ، ياليت، يَٰٓأَيُّهَا
    - فَ + أَلِف: فَأَكَلَ
    - فَ + س (استقبال): فَسَتُرْضِعُ
    """
    w = normalize_dagger_alif(word or "").strip()
    if not w or len(w) < 2:
        return False
    # أحرف فقط للتحقق من البداية
    bases = [c for c in w if c not in DIAC and c not in "ًٌٍ"]
    if not bases:
        return False
    first, second = bases[0], bases[1] if len(bases) > 1 else ""
    # يا للنداء: ي ثم ا/أ/آ
    if first == "ي" and second in "أإآاٱ":
        return True
    # فَأَ، فَا: ف ثم أ/ا
    if first == "ف" and second in "أإآاٱ":
        return True
    # فَسَ: ف ثم س (استقبال)
    if first == "ف" and second == "س":
        return True
    return False


def norm_char(c: str) -> str:
    if not c:
        return ""
    if c in "أإآءؤئ":
        return "ا"
    if c == "ى":
        return "ي"
    return c


def word_to_units(word: str) -> list:
    units = []
    cur_base, cur_diacs = None, []
    for ch in (word or "").replace("\u0670", "ا"):
        if ch in DIAC:
            if cur_base is not None:
                cur_diacs.append(ch)
        else:
            if cur_base is not None:
                units.append((cur_base, "".join(sorted(cur_diacs))))
            cur_base = ch
            cur_diacs = []
    if cur_base is not None:
        units.append((cur_base, "".join(sorted(cur_diacs))))
    return units


def derive_pattern(word: str, root: str) -> str:
    root_letters = [norm_char(c) for c in (root or "").replace("-", "").strip()]
    if len(root_letters) not in (3, 4):
        return ""
    placeholders = ["ف", "ع", "ل"] if len(root_letters) == 3 else ["ف", "ع", "ل", "ل"]
    units = word_to_units(word)
    out = []
    idx = 0
    for base, diacs in units:
        if idx < len(root_letters) and norm_char(base) == root_letters[idx]:
            out.append(placeholders[idx] + diacs)
            idx += 1
        else:
            out.append(base + diacs)
    if idx != len(root_letters):
        return ""
    return "".join(out)


def strip_pattern_prefix(pattern: str) -> str:
    """
    نزع سوابق الوزن المستنتج لاستخراج الجوهر فقط.
    فَلْيَسْتَفْعِلْ → يَسْتَفْعِلْ، فَلَنَفْعَلَّ → نَفْعَلَّ، فَٱسْتَفْعَلَ → اسْتَفْعَلَ، إلخ.
    """
    units = word_to_units(pattern)
    if len(units) < 2:
        return pattern
    bases = [u[0] for u in units]
    diacs_list = [u[1] for u in units]
    n_remove = 0
    # همزة الاستفهام: أَ + ت → نزع أَ (أَتَسْتَفْعِل → تَسْتَفْعِل)
    if len(bases) >= 2 and bases[0] in "أإآا" and bases[1] == "ت":
        n_remove = 1
    # فَنَ (ف + ن) — فَنَتَبَرَّأَ → تَفَعَّلَ
    elif len(bases) >= 2 and bases[0] == "ف" and bases[1] == "ن":
        n_remove = 2
    # فَبَا (ف + ب + ا) — ثلاثة وحدات
    elif len(bases) >= 3 and bases[0] == "ف" and bases[1] == "ب" and bases[2] in "أإآاٱ":
        n_remove = 3
    # فَلْ (ف + ل مع سكون) — وحدتان → يَسْتَفْعِلْ
    elif len(bases) >= 2 and bases[0] == "ف" and bases[1] == "ل" and "\u0652" in (diacs_list[1] or ""):
        n_remove = 2
    # فَٱ (ف + ٱ)
    elif len(bases) >= 2 and bases[0] == "ف" and bases[1] in "ٱ":
        n_remove = 2
    # فَلَ أو فَلَنَ (ف + ل) — وحدتان → نَفْعَلَّ
    elif len(bases) >= 2 and bases[0] == "ف" and bases[1] == "ل":
        n_remove = 2
    if n_remove == 0:
        return pattern
    remaining = units[n_remove:]
    return "".join(b + d for b, d in remaining)


def fix_istakfal_pattern(pattern: str) -> str:
    """
    إذا كان الوزن أَسْتَكْفَعْل (است + ك + فَعْل) فالكاف هي ف في استكبر — جذر (ف) وليست زائدة.
    نصلح إلى أَسْتَفْعَلَ (است + فْعَلَ) ثم strip_final_haraka يعطينا أَسْتَفْعَل.
    """
    units = word_to_units(pattern)
    bases = [u[0] for u in units]
    if len(bases) < 7:
        return pattern
    if (
        bases[0] in "أإآا"
        and bases[1] == "س"
        and bases[2] == "ت"
        and bases[3] == "ك"
        and bases[4] == "ف"
        and bases[5] == "ع"
        and bases[6] == "ل"
    ):
        # است + فْعَلَ (بدل كْفَعْل)
        return "".join(b + d for b, d in units[:3]) + "فْعَلَ"
    return pattern


def has_fal_order(pattern: str) -> bool:
    bases = [c for c in pattern if c not in DIAC and c not in "ًٌٍ"]
    try:
        i = bases.index("ف")
        j = bases.index("ع", i + 1)
        k = bases.index("ل", j + 1)
        return True
    except ValueError:
        return False


def is_core_pattern(pattern: str) -> bool:
    """
    True only if pattern has no prefix (و، ب، ك، ل، ال)، no suffix (ون، ان، هم، إلخ)،
    and no al-ta'reef anywhere. Allowed: يَفْعُلُ، نَفْعُلُ، فَعَلَ، أَفْعَلَ، تَفْعَلُ، etc.
    """
    letters = [c for c in pattern if c not in DIAC and c not in "ًٌٍ"]
    if not letters:
        return False
    letter_str = "".join(letters)
    # لا أل التعريف في أي موضع
    if "ال" in letter_str or "ٱل" in letter_str or "اَل" in letter_str:
        return False
    if len(letters) >= 2 and letters[0] in "اٱ" and letters[1] == "ل":
        return False
    # لا سوابق: يبدأ بـ ف أو أ أو ا أو ت أو ي أو ن فقط (لا و، ب، ك، ل)
    if letters[0] not in "فأاتين":
        return False
    # لا لواحق: ينتهي بآخر حرف جذر (ل)
    if letters[-1] != "ل":
        return False
    return True


def pattern_to_cv(pattern: str) -> str:
    v = "\u064e\u064f\u0650\u064b\u064c\u064d\u0651"
    cv = []
    i = 0
    while i < len(pattern):
        ch = pattern[i]
        if ch in v or ch in "\u0652\u0653\u0654\u0655\u0670":
            i += 1
            continue
        cv.append("C")
        if i + 1 < len(pattern) and pattern[i + 1] in "\u064e\u064f\u0650\u064b\u064c\u064d":
            cv.append("V")
        i += 1
    return "".join(cv)


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    csv_path = repo / "out_with_sources.csv"
    awzan_path = repo / "data" / "awzan_merged_final.csv"

    if not csv_path.exists():
        print(f"Missing: {csv_path}", file=sys.stderr)
        return 1
    if not awzan_path.exists():
        print(f"Missing: {awzan_path}", file=sys.stderr)
        return 1

    # Load existing patterns
    existing = set()
    with open(awzan_path, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            w = (row.get("الوزن") or "").strip()
            if w:
                existing.add(w)

    # Collect (word, root) with missing word_wazn
    seen_pair = set()
    pattern_to_example = {}
    with open(csv_path, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            root = (row.get("root") or "").strip()
            ww = (row.get("word_wazn") or "").strip()
            word = (row.get("word") or "").strip()
            if not root or root.count("-") < 2 or ww:
                continue
            # تطبيع الألف الخنجرية قبل أي تحويل
            word_norm = normalize_dagger_alif(word)
            if should_skip_word(word_norm):
                continue
            # نزع الضمائر قبل استنتاج الوزن (تَأْمُرُونَنَآ → تَأْمُرُ)
            word_stem = strip_pronoun_suffixes(word_norm)
            root_letters = (root or "").replace("-", "").strip()
            if len(root_letters) not in (3, 4):
                continue
            stem_bases = [c for c in word_stem if c not in DIAC and c not in "ًٌٍ"]
            if len(stem_bases) < len(root_letters):
                word_stem = word_norm
            k = (word_stem, root)
            if k in seen_pair:
                continue
            seen_pair.add(k)
            pat = derive_pattern(word_stem, root)
            if not pat or not has_fal_order(pat):
                continue
            # تجريد السوابق (فَلْي → ي، أَتَ → ت، فَنَ → …) لاستخراج الوزن الجوهري فقط
            pat = strip_pattern_prefix(pat)
            if not pat or not has_fal_order(pat):
                continue
            # إصلاح أَسْتَكْفَعْل → أَسْتَفْعَل (الكاف هي ف في استكبر)
            pat = fix_istakfal_pattern(pat)
            if not pat or not has_fal_order(pat):
                continue
            # نزع الحركة الإعرابية من آخر حرف (تَفْعُلُ → تَفْعُل)
            pat = strip_final_haraka(pat)
            if not pat or not has_fal_order(pat):
                continue
            if not is_core_pattern(pat):
                continue
            if pat not in existing and pat not in pattern_to_example:
                pattern_to_example[pat] = word_norm

    new_list = sorted(pattern_to_example.items(), key=lambda x: (len(x[0]), x[0]))
    if not new_list:
        print("No new patterns to add.", file=sys.stderr)
        return 0

    # Find next serial: max in file
    max_ser = 0
    with open(awzan_path, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            s = row.get("ser", "").strip()
            if s.isdigit():
                max_ser = max(max_ser, int(s))
    next_ser = max_ser + 1

    # Append new rows
    with open(awzan_path, "a", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        for pat, example in new_list:
            cv = pattern_to_cv(pat)
            writer.writerow([next_ser, pat, cv, example])
            next_ser += 1

    print(f"Appended {len(new_list)} new patterns to {awzan_path}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
