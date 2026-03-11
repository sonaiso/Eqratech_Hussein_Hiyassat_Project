# -*- coding: utf-8 -*-
from __future__ import annotations

import csv as csvlib
from dataclasses import dataclass
from pathlib import Path
from typing import Set


_ARABIC_LETTER_MIN = "\u0621"
_ARABIC_LETTER_MAX = "\u064A"
_HAMZA_MAP = str.maketrans(
    "\u0623\u0625\u0622\u0671",  # أ إ آ ٱ
    "\u0627\u0627\u0627\u0627",  # ا ا ا ا
)

# Denylist entries must be normalized (Arabic letters only, no dashes, no tashkeel)
_NON_ROOT_DENY = frozenset({
    "كنت", "قلت", "مني", "لذي",
    "علي", "عليه", "عليهم", "عليكما", "عليكم", "عليكن",
})


def _only_arabic_letters(s: str) -> str:
    return "".join(ch for ch in (s or "") if _ARABIC_LETTER_MIN <= ch <= _ARABIC_LETTER_MAX)


@dataclass(frozen=True)
class RootsDB:
    """
    Simple in-memory root database.

    Expected file format: CSV/TSV with the root in the FIRST column.
    """
    _roots: Set[str]

    @classmethod
    def load(cls, csv_path: str | Path) -> "RootsDB":
        path = Path(csv_path)

        # Determine delimiter (tab => TSV, otherwise CSV)
        first_line = ""
        with path.open("r", encoding="utf-8-sig") as f:
            first_line = f.readline()
        delim = "\t" if "\t" in first_line else ","

        roots: Set[str] = set()
        with path.open("r", encoding="utf-8-sig", newline="") as f:
            reader = csvlib.DictReader(f, delimiter=delim)
            fieldnames = [fn.strip() for fn in (reader.fieldnames or []) if fn and fn.strip()]
            if not fieldnames:
                return cls(_roots=roots)

            # Auto-detect root column by common names, fallback to first column.
            root_col = None
            for candidate in ("root", "الجذر", "جذر"):
                for fn in fieldnames:
                    if fn == candidate:
                        root_col = fn
                        break
                if root_col:
                    break
            if root_col is None:
                root_col = fieldnames[0]

            for row in reader:
                raw = (row.get(root_col) or "").strip()
                if not raw:
                    continue
                r = cls.normalize(raw)
                if r:
                    roots.add(r)

        return cls(_roots=roots)

    @staticmethod
    def normalize(root: str) -> str:
        """
        Normalize a root representation:
        - remove dashes
        - unify hamza/alef carriers
        - keep Arabic letters only
        """
        r = (root or "").replace("-", "").strip()
        r = r.translate(_HAMZA_MAP)
        r = _only_arabic_letters(r)
        return r

    def is_valid(self, root: str) -> bool:
        r = self.normalize(root)
        return bool(r) and r in self._roots

    def is_rootlike(self, root: str) -> bool:
        """
        Stricter validity for *prediction*:
        - must exist in DB
        - must be 3 or 4 letters
        - must NOT be in denylist (even if present in DB)
        """
        r = self.normalize(root)
        if not r:
            return False
        if r in _NON_ROOT_DENY:
            return False
        if len(r) not in (3, 4):
            return False
        return self.is_valid(r)

    def canonicalize(self, root: str) -> str:
        """
        Canonicalize root encoding using DB-backed fixes.
        - If root already in DB -> return as-is.
        - If NOT in DB but و<->ي middle variant IS in DB -> return variant.
        - Otherwise -> return as-is.
        """
        r = self.normalize(root).replace("-", "").strip()
        if not r:
            return r

        # Already valid -> keep as-is (highest priority)
        if self.is_rootlike(r):
            return r

        # Not in DB -> try و<->ي middle variant as fallback only
        if len(r) == 3:
            a, b, c = r[0], r[1], r[2]
            if b == "و":
                cand = a + "ي" + c
                if self.is_rootlike(cand):
                    return cand
            elif b == "ي":
                cand = a + "و" + c
                if self.is_rootlike(cand):
                    return cand

        return r

    def __len__(self) -> int:
        return len(self._roots)

    def __contains__(self, root: str) -> bool:
        return self.is_valid(root)
