# scripts/generate_quran_text_from_gold.py

import csv
from collections import defaultdict
from pathlib import Path

def generate(
    gold_path="data/quran_i3rab.csv",
    output_path="data/quran-from-gold.txt"
):
    ayahs = defaultdict(list)
    order = []

    # utf-8-sig يزيل BOM تلقائياً
    with open(gold_path, encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        # تحقق من أسماء الأعمدة
        print("Columns:", reader.fieldnames)
        for row in reader:
            key = (int(row["surah"]), int(row["ayah"]))
            if key not in ayahs:
                order.append(key)
            ayahs[key].append(row["word"].strip())

    Path(output_path).parent.mkdir(
        parents=True, exist_ok=True
    )
    with open(output_path, "w", encoding="utf-8") as f:
        for (surah, ayah) in order:
            text = " ".join(ayahs[(surah, ayah)])
            f.write(f"{surah}|{ayah}|{text}\n")

    print(f"Written: {output_path}")
    print(f"Total ayahs: {len(order)}")
    print(f"Total surahs: "
          f"{len(set(s for s,a in order))}")

    print("\nSample (first 5 ayahs):")
    for key in order[:5]:
        surah, ayah = key
        text = " ".join(ayahs[key])
        print(f"  {surah}|{ayah}|{text}")

if __name__ == "__main__":
    generate()