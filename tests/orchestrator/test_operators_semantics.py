# -*- coding: utf-8 -*-
"""Tests for operators_semantics loader and lookup (PP semantic hint API)."""

from __future__ import annotations

import pytest


def test_get_operator_semantic_hints_ila():
    from orchestrator.operators_semantics import get_operator_semantic_hints
    h = get_operator_semantic_hints("إلى")
    assert h is not None
    assert h.get("preferred_semantic_role") == "GOAL"
    assert "GOAL" in (h.get("semantic_functions") or [])


def test_get_operator_semantic_hints_ala():
    from orchestrator.operators_semantics import get_operator_semantic_hints
    h = get_operator_semantic_hints("على")
    assert h is not None
    assert h.get("preferred_semantic_role") == "GOAL"
    assert "الله" in (h.get("withhold_location_for") or [])


def test_get_operator_semantic_hints_min():
    from orchestrator.operators_semantics import get_operator_semantic_hints
    h = get_operator_semantic_hints("مِنْ")
    assert h is not None
    assert h.get("preferred_semantic_role") == "SOURCE"


def test_get_operator_semantic_hints_fi():
    from orchestrator.operators_semantics import get_operator_semantic_hints
    h = get_operator_semantic_hints("فِي")
    assert h is not None
    assert h.get("preferred_semantic_role") == "LOCATION"


def test_load_uses_enriched_or_fallback():
    from orchestrator.operators_semantics.loader import load_operator_semantics, get_source_file_used
    load_operator_semantics(force_reload=True)
    source = get_source_file_used()
    assert source in (
        "operators_catalog_split_project_enriched.csv",
        "operators_catalog_split_project_with_evidence.csv",
        "builtin",
    )
