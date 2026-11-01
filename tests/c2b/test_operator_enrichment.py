"""
Tests for the operator enrichment pipeline.

Covers:
- EnrichedOperatorEntry construction and serialisation
- OperatorEnrichmentPipeline with injected stubs (no filesystem dependency)
- OperatorEnrichmentPipeline.enrich() for a known operator
- OperatorEnrichmentPipeline.enrich() returning None for an unknown token
- OperatorEnrichmentPipeline.enrich_all() returns a list
- OperatorEnrichmentPipeline.enriched_by_group() groups correctly
- OperatorEnrichmentPipeline.stats() reports correct counts
- get_enrichment_pipeline() is a singleton
"""

from __future__ import annotations

from typing import Optional

import pytest

from fvafk.c2b.operator_enrichment import (
    EnrichedOperatorEntry,
    OperatorEnrichmentPipeline,
    _enrich_entry,
    _strip_diacritics,
    get_enrichment_pipeline,
)
from fvafk.c2b.operators_catalog import OperatorEntry, OperatorsCatalog
from fvafk.c2b.operators_particles_db import SpecialWord, SpecialWordsDatabase


# ─────────────────────────────────────────────────────────────────────────────
# Helpers / stubs
# ─────────────────────────────────────────────────────────────────────────────

def _make_csv_entry(
    operator: str = "في",
    group_number: str = "1",
    arabic_group_name: str = "الجر",
    english_group_name: str = "Prepositions",
    purpose: str = "للظرفية",
    example: str = "الماء في الكوز",
    note: str = "",
) -> OperatorEntry:
    return OperatorEntry(
        group_number=group_number,
        arabic_group_name=arabic_group_name,
        english_group_name=english_group_name,
        operator=operator,
        purpose=purpose,
        example=example,
        note=note,
    )


def _make_special_word(
    word: str = "في",
    grammatical_status: str = "مبني على السكون",
    category: str = "أداة نحوية",
    function: str = "حرف جر",
    syntactic_analysis: str = "حرف جر يدخل على الأسماء",
    semantic_analysis: str = "الظرفية",
    number: str = "",
    gender: str = "",
    word_type: str = "حرف",
    examples: str = "الماء في الكوز",
) -> SpecialWord:
    return SpecialWord(
        word=word,
        grammatical_status=grammatical_status,
        number=number,
        gender=gender,
        word_type=word_type,
        category=category,
        examples=examples,
        function=function,
        syntactic_analysis=syntactic_analysis,
        semantic_analysis=semantic_analysis,
    )


class _StubCatalog:
    """Minimal catalog stub with a single operator entry."""

    def __init__(self, entry: OperatorEntry) -> None:
        bare = _strip_diacritics(entry.operator)
        self._by_bare = {bare: [entry]}

    def classify(self, token: str):
        bare = _strip_diacritics(token)
        if bare in self._by_bare:
            return {"operator": bare, "token_bare": bare}
        return None

    def get_entries_by_bare(self, bare: str):
        return list(self._by_bare.get(bare, []))

    def iter_all_entries(self):
        for entries in self._by_bare.values():
            yield from entries


class _StubDB:
    """Minimal SpecialWordsDatabase stub backed by a dict."""

    def __init__(self, words: dict) -> None:
        self._words = words  # bare_token → SpecialWord

    def lookup(self, word: str) -> Optional[SpecialWord]:
        return self._words.get(_strip_diacritics(word)) or self._words.get(word)

    def lookup_with_prefix_stripping(self, word: str):
        return None


# ─────────────────────────────────────────────────────────────────────────────
# EnrichedOperatorEntry tests
# ─────────────────────────────────────────────────────────────────────────────

class TestEnrichedOperatorEntry:
    def test_operator_bare_strips_diacritics(self):
        entry = EnrichedOperatorEntry(
            group_number="1",
            arabic_group_name="الجر",
            english_group_name="Prepositions",
            operator="فِي",
            purpose="للظرفية",
            example="",
            note="",
        )
        assert entry.operator_bare == "في"

    def test_to_dict_contains_all_keys(self):
        entry = EnrichedOperatorEntry(
            group_number="1",
            arabic_group_name="الجر",
            english_group_name="Prepositions",
            operator="في",
            purpose="للظرفية",
            example="الماء في الكوز",
            note="",
            grammatical_status="مبني على السكون",
            is_mabni=True,
            db_category="أداة نحوية",
            db_function="حرف جر",
        )
        d = entry.to_dict()
        expected_keys = {
            "operator", "operator_bare", "group_number", "arabic_group_name",
            "english_group_name", "purpose", "example", "note",
            "grammatical_status", "is_mabni", "db_category",
            "db_number", "db_gender", "db_function",
            "syntactic_analysis", "semantic_analysis",
        }
        assert expected_keys == set(d.keys())

    def test_to_dict_is_mabni_true(self):
        entry = EnrichedOperatorEntry(
            group_number="2",
            arabic_group_name="التوكيد",
            english_group_name="Emphasis",
            operator="إِنَّ",
            purpose="للتوكيد",
            example="إن زيدا قائم",
            note="",
            is_mabni=True,
            grammatical_status="مبني",
        )
        d = entry.to_dict()
        assert d["is_mabni"] is True
        assert d["grammatical_status"] == "مبني"

    def test_to_dict_none_fields_for_unenriched(self):
        entry = EnrichedOperatorEntry(
            group_number="5",
            arabic_group_name="النصب",
            english_group_name="Accusative",
            operator="أَنْ",
            purpose="للمصدرية",
            example="",
            note="",
        )
        d = entry.to_dict()
        assert d["grammatical_status"] is None
        assert d["is_mabni"] is False
        assert d["db_category"] is None


# ─────────────────────────────────────────────────────────────────────────────
# _enrich_entry helper
# ─────────────────────────────────────────────────────────────────────────────

class TestEnrichEntryHelper:
    def test_enriches_when_db_has_match(self):
        entry = _make_csv_entry(operator="في")
        sw = _make_special_word(word="في")
        db = _StubDB({"في": sw})
        result = _enrich_entry(entry, db)  # type: ignore[arg-type]
        assert isinstance(result, EnrichedOperatorEntry)
        assert result.grammatical_status == "مبني على السكون"
        assert result.is_mabni is True
        assert result.db_category == "أداة نحوية"

    def test_unenriched_when_no_db_match(self):
        entry = _make_csv_entry(operator="إلى")
        db = _StubDB({})
        result = _enrich_entry(entry, db)  # type: ignore[arg-type]
        assert result.grammatical_status is None
        assert result.is_mabni is False
        assert result.db_category is None

    def test_csv_fields_preserved_after_enrichment(self):
        entry = _make_csv_entry(
            operator="في",
            group_number="1",
            purpose="للظرفية",
            example="الماء في الكوز",
        )
        db = _StubDB({})
        result = _enrich_entry(entry, db)  # type: ignore[arg-type]
        assert result.group_number == "1"
        assert result.purpose == "للظرفية"
        assert result.example == "الماء في الكوز"


# ─────────────────────────────────────────────────────────────────────────────
# OperatorEnrichmentPipeline
# ─────────────────────────────────────────────────────────────────────────────

class TestOperatorEnrichmentPipeline:
    def _make_pipeline(self, operator: str = "في") -> OperatorEnrichmentPipeline:
        entry = _make_csv_entry(operator=operator)
        sw = _make_special_word(word=_strip_diacritics(operator))
        catalog = _StubCatalog(entry)
        db = _StubDB({_strip_diacritics(operator): sw})
        pipeline = OperatorEnrichmentPipeline.__new__(OperatorEnrichmentPipeline)
        pipeline._catalog = catalog  # type: ignore[assignment]
        pipeline._db = db  # type: ignore[assignment]
        return pipeline

    def test_enrich_known_operator(self):
        pipeline = self._make_pipeline("في")
        result = pipeline.enrich("في")
        assert result is not None
        assert isinstance(result, EnrichedOperatorEntry)
        assert result.operator == "في"

    def test_enrich_returns_none_for_unknown_token(self):
        pipeline = self._make_pipeline("في")
        result = pipeline.enrich("كاتب")
        assert result is None

    def test_enrich_all_returns_list(self):
        pipeline = self._make_pipeline("في")
        all_entries = pipeline.enrich_all()
        assert isinstance(all_entries, list)
        assert len(all_entries) >= 1

    def test_enrich_all_entries_are_enriched_type(self):
        pipeline = self._make_pipeline("في")
        for e in pipeline.enrich_all():
            assert isinstance(e, EnrichedOperatorEntry)

    def test_iter_enriched_yields_same_as_enrich_all(self):
        pipeline = self._make_pipeline("في")
        from_all = pipeline.enrich_all()
        from_iter = list(pipeline.iter_enriched())
        assert len(from_all) == len(from_iter)
        assert from_all[0].operator == from_iter[0].operator

    def test_enriched_by_group_keys_are_group_numbers(self):
        pipeline = self._make_pipeline("في")
        groups = pipeline.enriched_by_group()
        assert isinstance(groups, dict)
        assert "1" in groups  # _make_csv_entry uses group_number="1"

    def test_enriched_by_group_values_are_lists_of_entries(self):
        pipeline = self._make_pipeline("في")
        groups = pipeline.enriched_by_group()
        for entries in groups.values():
            assert isinstance(entries, list)
            for e in entries:
                assert isinstance(e, EnrichedOperatorEntry)

    def test_stats_returns_required_keys(self):
        pipeline = self._make_pipeline("في")
        s = pipeline.stats()
        assert "total" in s
        assert "enriched" in s
        assert "mabni_count" in s
        assert "unenriched" in s

    def test_stats_total_equals_enriched_plus_unenriched(self):
        pipeline = self._make_pipeline("في")
        s = pipeline.stats()
        assert s["total"] == s["enriched"] + s["unenriched"]

    def test_stats_enriched_count_increases_when_db_has_match(self):
        pipeline = self._make_pipeline("في")
        s = pipeline.stats()
        # The stub DB does have "في" — so enriched should be 1, unenriched 0
        assert s["enriched"] == 1
        assert s["unenriched"] == 0

    def test_stats_unenriched_count_when_no_db_match(self):
        entry = _make_csv_entry(operator="إلى")
        catalog = _StubCatalog(entry)
        db = _StubDB({})  # empty — no match
        pipeline = OperatorEnrichmentPipeline.__new__(OperatorEnrichmentPipeline)
        pipeline._catalog = catalog  # type: ignore[assignment]
        pipeline._db = db  # type: ignore[assignment]
        s = pipeline.stats()
        assert s["total"] == 1
        assert s["enriched"] == 0
        assert s["unenriched"] == 1


# ─────────────────────────────────────────────────────────────────────────────
# Singleton factory
# ─────────────────────────────────────────────────────────────────────────────

class TestGetEnrichmentPipeline:
    def test_returns_pipeline_instance(self):
        pipeline = get_enrichment_pipeline()
        assert isinstance(pipeline, OperatorEnrichmentPipeline)

    def test_is_singleton(self):
        p1 = get_enrichment_pipeline()
        p2 = get_enrichment_pipeline()
        assert p1 is p2
