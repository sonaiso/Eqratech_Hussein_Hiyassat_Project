#!/usr/bin/env python3
"""
Download all JSON from API links in data/data_bank.csv (column "رابط (API)")
and save each to data/<relative_folder>/<table_slug>.json

Folder is derived from الباب (goal): phonology, mabniyat, juthur_mushtaqat, nahw.
"""
import csv
import json
import os
import re
import sys
from pathlib import Path
import time
from urllib.request import urlopen, Request
from urllib.error import URLError, HTTPError

DELAY_SEC = 30  # seconds between requests (reduce 429 rate limiting)

# Project root and paths
ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
CSV_PATH = DATA / "data_bank.csv"

# Map الباب (first column) to folder name under data/
BAB_TO_FOLDER = {
    "الهدف الأول : الفونولوجي": "01_phonology",
    "الهدف الثاني :   باب المبنيات": "02_mabniyat",
    "الهدف الثالث :   باب الجذر والمشتقات الصّرفية ( السماعية والقياسية )": "03_juthur_mushtaqat",
    "الهدف الثالث :   باب الجذر والمشتقات الصّرفية ( السماعية والقياسية ) ": "03_juthur_mushtaqat",
    "الهدف الرابع : باب النحو": "04_nahw",
}
# Fallback: extract short slug from Arabic باب when not in map
def bab_to_folder(bab: str, fallback: str = "00_other") -> str:
    bab = (bab or "").strip()
    if not bab:
        return fallback
    if bab in BAB_TO_FOLDER:
        return BAB_TO_FOLDER[bab]
    # Heuristic: الهدف الأول -> 01_phonology etc by number
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
    # Safe folder name from first 20 chars
    safe = re.sub(r"[^\w\s\-]", "", bab)[:20].strip().replace(" ", "_") or "other"
    return safe


def slug(s: str, max_len: int = 60) -> str:
    """Safe filename slug from table/name."""
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

    # Collect (url, folder, filename) for each row with valid API
    current_bab = ""
    tasks = []
    seen_urls = set()

    with open(CSV_PATH, "r", encoding="utf-8") as f:
        reader = csv.reader(f)
        next(reader)  # skip header
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
            # Connectives with category_id -> one folder, file per category
            if "connectives/active" in url and "category_id=" in url:
                folder = "connectives_api"
                m = re.search(r"category_id=(\d+)", url)
                table_slug = f"connectives_category_{m.group(1)}" if m else table_slug
            if not table_slug or table_slug == "unknown":
                table_slug = slug(url.split("/")[-1].split("?")[0]) or "data"
            tasks.append((url, folder, table_slug))

    print(f"Found {len(tasks)} unique API URLs to download.")

    ok = 0
    skip = 0
    fail = 0
    failed_list = []  # (url, folder, file, reason)

    for url, folder, name in tasks:
        out_dir = DATA / folder
        out_dir.mkdir(parents=True, exist_ok=True)
        out_file = out_dir / f"{name}.json"
        if out_file.exists() and out_file.stat().st_size > 0:
            print(f"  SKIP (exists) {folder}/{name}.json")
            skip += 1
            continue
        try:
            time.sleep(DELAY_SEC)
            req = Request(url, headers={"Accept": "application/json", "User-Agent": "DataBankDownload/1.0"})
            with urlopen(req, timeout=30) as resp:
                raw = resp.read().decode("utf-8", errors="replace")
            # Try to parse as JSON (some APIs may return HTML on error)
            try:
                data = json.loads(raw)
                with open(out_file, "w", encoding="utf-8") as w:
                    json.dump(data, w, ensure_ascii=False, indent=0)
            except json.JSONDecodeError:
                with open(out_file, "w", encoding="utf-8") as w:
                    w.write(raw)
            print(f"  OK {folder}/{name}.json")
            ok += 1
        except HTTPError as e:
            reason = f"{e.code}"  # 404, 429, etc.
            failed_list.append((url, folder, f"{name}.json", reason))
            print(f"  FAIL {url[:60]}... -> {e}", file=sys.stderr)
            fail += 1
        except (URLError, OSError) as e:
            reason = type(e).__name__ + ": " + str(e)[:80]
            failed_list.append((url, folder, f"{name}.json", reason))
            print(f"  FAIL {url[:60]}... -> {e}", file=sys.stderr)
            fail += 1

    # Write failed list to file
    failed_path = DATA / "download_failed.csv"
    if failed_list:
        with open(failed_path, "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["url", "folder", "file", "reason"])
            for url, folder, file_name, reason in failed_list:
                w.writerow([url, folder, file_name, reason])
        print(f"\nFailed downloads written to: {failed_path}")

    print(f"\nDone: {ok} saved, {skip} skipped (existing), {fail} failed (404 = endpoint missing, 429 = rate limit).")


if __name__ == "__main__":
    main()
