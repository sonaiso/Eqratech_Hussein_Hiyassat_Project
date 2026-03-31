from __future__ import annotations

import csv
import os
import unicodedata
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def _strip_diacritics(text: str) -> str:
    # Remove Arabic harakat/tanwin/sukun/shadda etc. Keep letters (including hamza letters).
    return "".join(
        ch for ch in unicodedata.normalize("NFC", text)
        if unicodedata.combining(ch) == 0
    ).replace("ـ", "").strip()


# دَمَّة \u064F — للتمييز بين رُبَّ (حرف جر) و رَبِّ (ربّ = اسم)
_DAMMA = "\u064F"


def _first_base_letter_vowel(nfd: str, base_index: int) -> Optional[str]:
    """Return the combining vowel (e.g. damma) after the base letter at base_index in NFD string."""
    if base_index < 0 or base_index >= len(nfd):
        return None
    j = base_index + 1
    while j < len(nfd) and unicodedata.category(nfd[j]) == "Mn":
        return nfd[j]
    return None


def _is_rabb_particle(token: str) -> bool:
    """
    رُبَّ (حرف جر للتقليل) يبدأ بضمة على الراء؛ رَبِّ (ربّ = الاسم) بفتحة أو كسرة.
    لا تُصنّف ربّ (الاسم) كأداة.
    """
    if not token or _strip_diacritics(token) != "رب":
        return True
    nfd = unicodedata.normalize("NFD", token.strip())
    first_letter_idx = -1
    for i, c in enumerate(nfd):
        if unicodedata.category(c) != "Mn" and c not in " \t":
            first_letter_idx = i
            break
    if first_letter_idx < 0:
        return True
    v = _first_base_letter_vowel(nfd, first_letter_idx)
    return v == _DAMMA


@dataclass(frozen=True)
class OperatorEntry:
    group_number: str
    arabic_group_name: str
    english_group_name: str
    operator: str
    purpose: str
    example: str
    note: str
    # أثر الأداة من operators_catalog_split_project_enriched / with_evidence
    effect_signature: str = ""
    usage_ar: str = ""
    i3rab_template: str = ""

    @property
    def operator_bare(self) -> str:
        return _strip_diacritics(self.operator)


class OperatorsCatalog:
    """
    Catalog of Arabic operators/particles (حروف/أدوات) loaded from a CSV.
    Used to short-circuit morphology (root/pattern) for tokens that are operators.
    """

    # Prefer enriched canonical, then legacy. Env FVAFK_OPERATORS_CSV overrides.
    DEFAULT_CANDIDATE_PATHS = [
        Path.cwd() / "data" / "operators_catalog_split_project_enriched.csv",
        Path.cwd() / "data" / "operators_catalog_split_enriched.csv",
        Path.cwd() / "data" / "operators_catalog_split.csv",
        Path.cwd() / "operators_catalog_split.csv",
    ]

    PREFIX_CHARS = ("و", "ف", "ب", "ك", "ل", "س")

    def __init__(self, csv_path: Optional[Path] = None) -> None:
        self.csv_path = csv_path or self._resolve_path()
        self._by_bare: Dict[str, List[OperatorEntry]] = {}
        if self.csv_path and self.csv_path.exists():
            self._load(self.csv_path)

    def _resolve_path(self) -> Optional[Path]:
        env = os.environ.get("FVAFK_OPERATORS_CSV")
        if env:
            p = Path(env).expanduser()
            if p.exists():
                return p
        for p in self.DEFAULT_CANDIDATE_PATHS:
            if p.exists():
                return p
        return None

    def _load(self, path: Path) -> None:
        with open(path, encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                op = (row.get("Operator") or "").strip()
                if not op:
                    continue
                entry = OperatorEntry(
                    group_number=(row.get("Group Number") or "").strip(),
                    arabic_group_name=(row.get("Arabic Group Name") or "").strip(),
                    english_group_name=(row.get("English Group Name") or "").strip(),
                    operator=op,
                    purpose=(row.get("Purpose/Usage") or "").strip(),
                    example=(row.get("Example") or "").strip(),
                    note=(row.get("Note") or "").strip(),
                    effect_signature=(row.get("project_effect_signature") or "").strip(),
                    usage_ar=(row.get("project_usage_universal_ar") or "").strip(),
                    i3rab_template=(row.get("project_i3rab_template") or "").strip(),
                )
                bare = entry.operator_bare
                self._by_bare.setdefault(bare, []).append(entry)

    def classify(self, token: str) -> Optional[Dict[str, object]]:
        """
        Return operator metadata if token is an operator (possibly prefixed by conjunctions),
        else None.
        """
        bare = _strip_diacritics(token)
        if not bare:
            return None

        # First: direct match
        direct = self._best_entry(bare)
        if direct:
            # رَبِّ (ربّ = الاسم) لا تُصنّف كأداة رُبَّ (حرف جر)
            if bare == "رب" and not _is_rabb_particle(token):
                direct = None
            if direct:
                return self._format_result(token_bare=bare, prefixes="", parts=[direct])

        # Second: peel single-letter prefixes (و/ف/ب/ك/ل/س) and retry
        prefixes, remainder = self._peel_prefixes(bare)
        if remainder != bare:
            # direct remainder
            rem_entry = self._best_entry(remainder)
            if rem_entry:
                return self._format_result(token_bare=bare, prefixes=prefixes, parts=[rem_entry])

            # compound: e.g., "إنما" = "إن" + "ما" if both exist
            compound = self._compound_match(remainder)
            if compound:
                return self._format_result(token_bare=bare, prefixes=prefixes, parts=compound)

        return None

    def _best_entry(self, bare: str) -> Optional[OperatorEntry]:
        entries = self._by_bare.get(bare)
        if not entries:
            return None
        # prefer the first; CSV ordering is curated
        return entries[0]

    def _peel_prefixes(self, bare: str) -> Tuple[str, str]:
        prefixes = ""
        remainder = bare
        for _ in range(3):  # avoid stripping too much
            if remainder and remainder[0] in self.PREFIX_CHARS and len(remainder) > 1:
                prefixes += remainder[0]
                remainder = remainder[1:]
            else:
                break
        return prefixes, remainder

    def _compound_match(self, bare: str) -> Optional[List[OperatorEntry]]:
        # find a decomposition bare = op1 + op2 where both ops exist; prefer longest op1
        candidates = sorted(self._by_bare.keys(), key=len, reverse=True)
        for op1 in candidates:
            if bare.startswith(op1) and len(op1) < len(bare):
                rest = bare[len(op1):]
                if rest in self._by_bare:
                    return [self._best_entry(op1), self._best_entry(rest)]  # type: ignore[list-item]
        return None

    def get_entries_by_bare(self, bare: str) -> List[OperatorEntry]:
        """Return all catalog entries whose bare (diacritic-stripped) form equals *bare*."""
        return list(self._by_bare.get(bare, []))

    def iter_all_entries(self):
        """Yield every :class:`OperatorEntry` in the catalog (all bare forms, all duplicates)."""
        for entries in self._by_bare.values():
            yield from entries

    def _format_result(self, token_bare: str, prefixes: str, parts: List[OperatorEntry]) -> Dict[str, object]:
        primary = parts[0]
        out = {
            "token_bare": token_bare,
            "prefixes": prefixes or None,
            "operator": primary.operator_bare,
            "group": {
                "number": primary.group_number or None,
                "arabic": primary.arabic_group_name or None,
                "english": primary.english_group_name or None,
            },
            "purpose": primary.purpose or None,
            "example": primary.example or None,
            "note": primary.note or None,
            "compound": [p.operator_bare for p in parts] if len(parts) > 1 else None,
            "source_path": str(self.csv_path) if self.csv_path else None,
        }
        if primary.usage_ar:
            out["operator_effect"] = primary.usage_ar
        if primary.effect_signature:
            out["effect_signature"] = primary.effect_signature
        if primary.i3rab_template:
            out["i3rab_template"] = primary.i3rab_template
        return out


@lru_cache(maxsize=1)
def get_operators_catalog() -> OperatorsCatalog:
    return OperatorsCatalog()

