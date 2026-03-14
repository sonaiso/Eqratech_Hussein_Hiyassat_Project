"""
Enrichment pipeline for the operator catalog.

Merges the CSV-based :class:`OperatorsCatalog` with the JSON-based
:class:`SpecialWordsDatabase` to produce enriched operator entries that
carry both structural classification (group, purpose, example) and
grammatical metadata (grammatical_status, is_mabni, syntactic_analysis,
semantic_analysis).
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Dict, Iterator, List, Optional

from .operators_catalog import OperatorEntry, OperatorsCatalog, get_operators_catalog
from .operators_particles_db import SpecialWord, SpecialWordsDatabase, get_special_words_db


def _strip_diacritics(text: str) -> str:
    """Remove Arabic diacritics (harakat, sukun, shadda) from *text*."""
    return "".join(
        ch for ch in unicodedata.normalize("NFC", text)
        if unicodedata.combining(ch) == 0
    ).replace("ـ", "").strip()


@dataclass(frozen=True)
class EnrichedOperatorEntry:
    """
    Operator entry enriched with grammatical metadata from both data sources.

    Fields inherited from :class:`~.operators_catalog.OperatorEntry`
    (CSV source):
        group_number, arabic_group_name, english_group_name,
        operator, purpose, example, note

    Fields added by enrichment from :class:`~.operators_particles_db.SpecialWord`
    (JSON source):
        grammatical_status  — e.g. "مبني على السكون"
        is_mabni            — True if the word is indeclinable (مبني)
        db_category         — category name from the JSON database
        db_number           — grammatical number from the JSON database
        db_gender           — grammatical gender from the JSON database
        db_function         — functional / semantic role (عملها/وظيفتها)
        syntactic_analysis  — إعراب summary from the JSON database
        semantic_analysis   — دلالة / ملاحظات from the JSON database
    """

    # ── CSV-source fields ──────────────────────────────────────────────────
    group_number: str
    arabic_group_name: str
    english_group_name: str
    operator: str
    purpose: str
    example: str
    note: str

    # ── JSON-enrichment fields (None when no match found) ──────────────────
    grammatical_status: Optional[str] = field(default=None)
    is_mabni: bool = field(default=False)
    db_category: Optional[str] = field(default=None)
    db_number: Optional[str] = field(default=None)
    db_gender: Optional[str] = field(default=None)
    db_function: Optional[str] = field(default=None)
    syntactic_analysis: Optional[str] = field(default=None)
    semantic_analysis: Optional[str] = field(default=None)

    @property
    def operator_bare(self) -> str:
        """Operator string without diacritics."""
        return _strip_diacritics(self.operator)

    def to_dict(self) -> Dict[str, object]:
        """Return a plain dict representation suitable for JSON serialisation."""
        return {
            "operator": self.operator,
            "operator_bare": self.operator_bare,
            "group_number": self.group_number or None,
            "arabic_group_name": self.arabic_group_name or None,
            "english_group_name": self.english_group_name or None,
            "purpose": self.purpose or None,
            "example": self.example or None,
            "note": self.note or None,
            "grammatical_status": self.grammatical_status,
            "is_mabni": self.is_mabni,
            "db_category": self.db_category,
            "db_number": self.db_number,
            "db_gender": self.db_gender,
            "db_function": self.db_function,
            "syntactic_analysis": self.syntactic_analysis,
            "semantic_analysis": self.semantic_analysis,
        }


def _enrich_entry(
    entry: OperatorEntry,
    db: SpecialWordsDatabase,
) -> EnrichedOperatorEntry:
    """
    Combine a single *entry* from the CSV catalog with matching data from *db*.

    Lookup strategy (most-specific to least-specific):
    1. Direct lookup by *entry.operator* (with diacritics).
    2. Direct lookup by *entry.operator_bare* (without diacritics).
    3. Prefix-stripped lookup via
       :meth:`~SpecialWordsDatabase.lookup_with_prefix_stripping`.
    """
    sw: Optional[SpecialWord] = (
        db.lookup(entry.operator)
        or db.lookup(entry.operator_bare)
    )
    if sw is None:
        result = db.lookup_with_prefix_stripping(entry.operator)
        if result is not None:
            sw = result[0]

    gs: Optional[str] = None
    is_mabni: bool = False
    db_category: Optional[str] = None
    db_number: Optional[str] = None
    db_gender: Optional[str] = None
    db_function: Optional[str] = None
    syn: Optional[str] = None
    sem: Optional[str] = None

    if sw is not None:
        gs = sw.grammatical_status or None
        is_mabni = sw.is_mabni
        db_category = sw.category or None
        db_number = sw.number or None
        db_gender = sw.gender or None
        db_function = sw.function or None
        syn = sw.syntactic_analysis or None
        sem = sw.semantic_analysis or None

    return EnrichedOperatorEntry(
        group_number=entry.group_number,
        arabic_group_name=entry.arabic_group_name,
        english_group_name=entry.english_group_name,
        operator=entry.operator,
        purpose=entry.purpose,
        example=entry.example,
        note=entry.note,
        grammatical_status=gs,
        is_mabni=is_mabni,
        db_category=db_category,
        db_number=db_number,
        db_gender=db_gender,
        db_function=db_function,
        syntactic_analysis=syn,
        semantic_analysis=sem,
    )


class OperatorEnrichmentPipeline:
    """
    Enrichment pipeline that combines the CSV-based
    :class:`~.operators_catalog.OperatorsCatalog` with the JSON-based
    :class:`~.operators_particles_db.SpecialWordsDatabase`.

    Usage::

        pipeline = OperatorEnrichmentPipeline()

        # Enrich a single operator token from running text
        enriched = pipeline.enrich("إِنَّ")

        # Iterate over all catalog entries in enriched form
        for entry in pipeline.enrich_all():
            print(entry.operator, entry.is_mabni, entry.grammatical_status)
    """

    def __init__(
        self,
        catalog: Optional[OperatorsCatalog] = None,
        db: Optional[SpecialWordsDatabase] = None,
    ) -> None:
        self._catalog: OperatorsCatalog = catalog or get_operators_catalog()
        self._db: SpecialWordsDatabase = db or get_special_words_db()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def enrich(self, token: str) -> Optional[EnrichedOperatorEntry]:
        """
        Return an :class:`EnrichedOperatorEntry` for *token* if it is
        recognised as an operator, else ``None``.

        The method first classifies *token* using
        :meth:`~OperatorsCatalog.classify`; if found it enriches the
        matched :class:`~OperatorEntry` with data from the JSON database.
        """
        classification = self._catalog.classify(token)
        if classification is None:
            return None

        # Retrieve the raw OperatorEntry via the new public accessor
        bare = str(classification["operator"])
        entries = self._catalog.get_entries_by_bare(bare)
        if not entries:
            return None
        entry = entries[0]
        return _enrich_entry(entry, self._db)

    def enrich_all(self) -> List[EnrichedOperatorEntry]:
        """
        Return enriched entries for **every** operator in the catalog.

        Operators that appear more than once in the CSV (different rows for
        the same bare form) are each included individually.
        """
        result: List[EnrichedOperatorEntry] = []
        for entry in self._catalog.iter_all_entries():
            result.append(_enrich_entry(entry, self._db))
        return result

    def iter_enriched(self) -> Iterator[EnrichedOperatorEntry]:
        """Lazy iterator version of :meth:`enrich_all`."""
        for entry in self._catalog.iter_all_entries():
            yield _enrich_entry(entry, self._db)

    def enriched_by_group(self) -> Dict[str, List[EnrichedOperatorEntry]]:
        """
        Return a mapping from *group_number* to enriched entries.

        Useful for inspecting a single grammatical group, e.g.::

            groups = pipeline.enriched_by_group()
            for entry in groups.get("2", []):   # Group 2: توكيد
                print(entry.operator, entry.purpose)
        """
        result: Dict[str, List[EnrichedOperatorEntry]] = {}
        for enriched in self.iter_enriched():
            key = enriched.group_number or "unknown"
            result.setdefault(key, []).append(enriched)
        return result

    def stats(self) -> Dict[str, int]:
        """
        Return basic statistics about the enrichment quality of the catalog.

        Returns a dict with:
            total           — total number of catalog entries processed
            enriched        — entries matched in the JSON database (≥1 field)
            mabni_count     — entries identified as indeclinable (مبني)
            unenriched      — entries with no JSON match
        """
        total = enriched_count = mabni_count = 0
        for entry in self.iter_enriched():
            total += 1
            if entry.grammatical_status is not None or entry.db_category is not None:
                enriched_count += 1
            if entry.is_mabni:
                mabni_count += 1
        return {
            "total": total,
            "enriched": enriched_count,
            "mabni_count": mabni_count,
            "unenriched": total - enriched_count,
        }


@lru_cache(maxsize=1)
def get_enrichment_pipeline() -> OperatorEnrichmentPipeline:
    """Return a cached singleton :class:`OperatorEnrichmentPipeline`."""
    return OperatorEnrichmentPipeline()
