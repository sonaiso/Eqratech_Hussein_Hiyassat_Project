#!/usr/bin/env python3
"""
Probe API URLs from data_bank.csv that have no saved file (or empty file)
and write failed ones to data/download_failed.csv (url, folder, file, reason).
Use this to get the failed list without re-running the full download (with 30s delays).
"""
import csv
import re
import sys
import time
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
CSV_PATH = DATA / "data_bank.csv"
OUT_CSV = DATA / "download_failed.csv"

BAB_TO_FOLDER = {
    "الهدف الأول : الفونولوجي": "01_phonology",
    "الهدف الثاني :   باب المبنيات": "02_mabniyat",
    "الهدف الثالث :   باب الجذر والمشتقات الصّرفية ( السماعية والقياسية )": "03_juthur_mushtaqat",
    "الهدف الثالث :   باب الجذر والمشتقات الصّرفية ( السماعية والقياسية ) ": "03_juthur_mushtaqat",
    "الهدف الرابع : باب النحو": "04_nahw",
}


def bab_to_folder(bab: str, fallback: str = "00_other") -> str:
    bab = (bab or "").strip()
    if not bab:
        return fallback
    if bab in BAB_TO_FOLDER:
        return BAB_TO_FOLDER[bab]
    m = re.search(r"الهدف\s*(\w+)\s*[::]", bab)
    if m:
        num = m.group(1)
        if "الأول" in num or "١" in num:
            return "01_phonology"
        if "الثاني" in num or "٢" in num:
            return "02_mabniyat"
        if "الثالث" in num or "٣" in num:
            return "03_juthur_mushtaqat"
        if "الرابع" in num or "٤" in num:
            return "04_nahw"
    safe = re.sub(r"[^\w\s\-]", "", bab)[:20].strip().replace(" ", "_") or "other"
    return safe


def slug(s: str, max_len: int = 60) -> str:
    if not s:
        return "unknown"
    s = (s.split("//")[0] or s).strip()
    s = re.sub(r"[^\w\-]", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    return (s or "unknown")[:max_len]


def main():
    if not CSV_PATH.exists():
        print(f"Not found: {CSV_PATH}", file=sys.stderr)
        sys.exit(1)

    with open(CSV_PATH, "r", encoding="utf-8") as f:
        reader = csv.reader(f)
        header = next(reader)
        try:
            api_idx = header.index("رابط (API)")
            bab_idx = header.index("الباب")
            table_idx = header.index("اسم الجدول")
        except ValueError as e:
            print(f"Missing column: {e}", file=sys.stderr)
            sys.exit(1)

    current_bab = ""
    tasks = []
    seen_urls = set()

    with open(CSV_PATH, "r", encoding="utf-8") as f:
        reader = csv.reader(f)
        next(reader)
        for row in reader:
            if len(row) <= api_idx:
                continue
            bab_cell = (row[bab_idx] or "").strip() if len(row) > bab_idx else ""
            if bab_cell and not bab_cell.startswith(","):
                current_bab = bab_cell
            url = (row[api_idx] or "").strip().replace("\n", "").replace("\r", "").strip('"')
            if not url or url == "مكرر" or "127.0.0.1" in url:
                continue
            if not url.startswith("http://") and not url.startswith("https://"):
                continue
            if url in seen_urls:
                continue
            seen_urls.add(url)
            folder = bab_to_folder(current_bab)
            table_cell = (row[table_idx] or "").strip() if len(row) > table_idx else ""
            table_slug = slug(table_cell)
            if "connectives/active" in url and "category_id=" in url:
                folder = "connectives_api"
                m = re.search(r"category_id=(\d+)", url)
                table_slug = f"connectives_category_{m.group(1)}" if m else table_slug
            if not table_slug or table_slug == "unknown":
                table_slug = slug(url.split("/")[-1].split("?")[0]) or "data"
            tasks.append((url, folder, table_slug))

    # Only probe URLs that have no file or empty file
    to_probe = []
    for url, folder, name in tasks:
        out_file = DATA / folder / f"{name}.json"
        if not out_file.exists() or out_file.stat().st_size == 0:
            to_probe.append((url, folder, name))

    print(f"Probing {len(to_probe)} URLs with no (or empty) file (timeout 15s, 2s delay)...")

    failed_list = []
    for i, (url, folder, name) in enumerate(to_probe):
        if i > 0:
            time.sleep(2)
        try:
            req = Request(url, headers={"Accept": "application/json", "User-Agent": "DataBankProbe/1.0"})
            with urlopen(req, timeout=15) as resp:
                _ = resp.read()
            print(f"  OK {folder}/{name}.json")
        except HTTPError as e:
            reason = str(e.code)
            failed_list.append((url, folder, f"{name}.json", reason))
            print(f"  FAIL {reason} {folder}/{name}.json")
        except (URLError, OSError) as e:
            reason = type(e).__name__ + ": " + (str(e)[:80] or "unknown")
            failed_list.append((url, folder, f"{name}.json", reason))
            print(f"  FAIL {folder}/{name}.json -> {reason[:50]}")

    with open(OUT_CSV, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["url", "folder", "file", "reason"])
        for row in failed_list:
            w.writerow(row)

    print(f"\nFailed list written to: {OUT_CSV} ({len(failed_list)} rows)")


if __name__ == "__main__":
    main()
