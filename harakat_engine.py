"""Simple harakat provider used by `reconstruction_utils.load_maps()`.

Exports an object named `حركات` with a `make_df()` method that returns a
DataFrame of harakat information. This is intentionally lightweight: it
loads `الحركات.csv` or `Harakat.csv` (fallback) from the repo root and
returns a pandas DataFrame. The loader attempts to be tolerant of
different column names used by downstream code.
"""
from typing import Optional
import os
import pandas as pd


class حركات:
    @staticmethod
    def make_df(csv_path: Optional[str] = None) -> pd.DataFrame:
        # Prefer provided path, then common filenames in repo root
        candidates = [] if csv_path else [
            os.path.join(os.path.dirname(__file__), 'الحركات.csv'),
            os.path.join(os.path.dirname(__file__), 'الحركات_كامل.csv'),
            os.path.join(os.path.dirname(__file__), 'Harakat.csv'),
        ]
        if csv_path:
            candidates.insert(0, csv_path)

        found = None
        for p in candidates:
            if p and os.path.exists(p):
                found = p
                break

        if not found:
            # Fallback: return a minimal dataframe with common haraka names
            return pd.DataFrame([
                {'شكل الحركة': 'فتحة', 'UTF-8': 'b"\xd8\xb9"'},
                {'شكل الحركة': 'ضمة', 'UTF-8': 'b"\xd8\xba"'},
                {'شكل الحركة': 'كسرة', 'UTF-8': 'b"\xd8\xbe"'},
            ])

        try:
            df = pd.read_csv(found, dtype=str).fillna('')
        except Exception:
            df = pd.read_csv(found, dtype=str, encoding='utf-8-sig').fillna('')

        return df
