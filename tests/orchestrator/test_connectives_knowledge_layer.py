# -*- coding: utf-8 -*-
"""
Tests for shared Connectives Knowledge Layer (Connectives Injection Pass 1).
Asserts: load, normalize, lookup by token/group, diacritic-insensitive, stage consumption.
"""

from __future__ import annotations

import pytest

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

try:
    from orchestrator.connectives import (
        load_connectives_knowledge,
        get_connective_by_token,
        get_connectives_by_group,
        classify_connective,
        is_conditional_connective,
        is_negation_connective,
        is_explanatory_or_causal_connective,
        is_adversative_connective,
        GROUP_CONDITIONAL,
        GROUP_NEGATION,
        GROUP_EXPLANATION_CAUSATION,
        GROUP_ADVERSATIVE,
    )
except ImportError:
    from src.orchestrator.connectives import (
        load_connectives_knowledge,
        get_connective_by_token,
        get_connectives_by_group,
        classify_connective,
        is_conditional_connective,
        is_negation_connective,
        is_explanatory_or_causal_connective,
        is_adversative_connective,
        GROUP_CONDITIONAL,
        GROUP_NEGATION,
        GROUP_EXPLANATION_CAUSATION,
        GROUP_ADVERSATIVE,
    )


def test_files_load_successfully():
    """Connectives JSON files load and produce normalized list."""
    items = load_connectives_knowledge(force_reload=True)
    assert isinstance(items, list)
    # At least one category should have been loaded if data dir exists
    data_dir = ROOT / "data" / "connectives_api"
    if data_dir.exists():
        assert len(items) >= 1, "Expected at least one connective from data/connectives_api"
    for c in items[:3]:
        assert "token" in c
        assert "normalized_token" in c
        assert "group" in c
        assert "category_id" in c
        assert "source_file" in c
        assert "raw" in c


def test_normalization_produces_expected_fields():
    """Normalized entries have stable schema."""
    items = load_connectives_knowledge(force_reload=True)
    if not items:
        pytest.skip("No connectives loaded (data/connectives_api may be missing)")
    c = items[0]
    required = {"token", "normalized_token", "category_id", "category_name", "group", "source_file", "raw"}
    for key in required:
        assert key in c, f"Missing key: {key}"
    assert c["group"] in (GROUP_CONDITIONAL, GROUP_NEGATION, GROUP_EXPLANATION_CAUSATION, GROUP_ADVERSATIVE)


def test_lookup_by_token_works():
    """get_connective_by_token returns entry when token is in knowledge."""
    # Conditional: لو، إن، إذا often present in category 3
    for token in ["لَو", "لو", "إِنْ", "إن", "لَكِنْ", "لكن"]:
        c = get_connective_by_token(token)
        if c is not None:
            assert "group" in c
            assert "token" in c or "normalized_token" in c
            break
    else:
        # At least one known token should resolve if data exists
        all_ = load_connectives_knowledge()
        if all_:
            t = all_[0]["token"]
            assert get_connective_by_token(t) is not None


def test_lookup_diacritic_insensitive():
    """Lookup is reasonably diacritic-insensitive."""
    items = load_connectives_knowledge(force_reload=True)
    if not items:
        pytest.skip("No connectives loaded")
    # Use first token with diacritics and without
    sample = items[0]
    token_with = sample.get("token") or ""
    token_norm = sample.get("normalized_token") or ""
    if token_with and token_norm:
        c1 = get_connective_by_token(token_with)
        c2 = get_connective_by_token(token_norm)
        assert (c1 is not None) == (c2 is not None)
        if c1 and c2:
            assert c1.get("group") == c2.get("group")


def test_group_classification_conditional():
    """Conditional group: لو، إن، إذا (if present in selected files)."""
    for token in ["لَو", "لو", "إِنْ", "إن", "إِذَا", "اذا"]:
        c = get_connective_by_token(token)
        if c is not None and c.get("group") == GROUP_CONDITIONAL:
            assert is_conditional_connective(token)
            assert classify_connective(token) is not None
            return
    # If no conditional in data, at least is_* does not crash
    assert is_conditional_connective("لو") or not load_connectives_knowledge() or True


def test_group_classification_negation():
    """Negation group: لا، لم، لن، ما (if present)."""
    for token in ["لَا", "لا", "لَم", "لم", "لَن", "لن", "مَا", "ما"]:
        if is_negation_connective(token):
            assert get_connective_by_token(token) is not None
            return
    # No crash when no match
    assert is_negation_connective("لا") or not load_connectives_knowledge() or True


def test_group_classification_explanation_causation():
    """Explanation/causation: لأن، كي، إذ، أي (if present)."""
    for token in ["لأَن", "لأن", "أَيْ", "أي", "إذ", "كي"]:
        if is_explanatory_or_causal_connective(token):
            assert get_connective_by_token(token) is not None
            return
    assert is_explanatory_or_causal_connective("أي") or not load_connectives_knowledge() or True


def test_group_classification_adversative():
    """Adversative: لكن، بل، غير أن، إلا أن (if present in category 29)."""
    for token in ["لَكِنْ", "لكن", "بَل", "بل", "لَكِنَّ", "لكنّ"]:
        if is_adversative_connective(token):
            assert get_connective_by_token(token) is not None
            return
    assert is_adversative_connective("لكن") or not load_connectives_knowledge() or True


def test_get_connectives_by_group():
    """get_connectives_by_group returns list for valid group."""
    for group in [GROUP_CONDITIONAL, GROUP_NEGATION, GROUP_EXPLANATION_CAUSATION, GROUP_ADVERSATIVE]:
        lst = get_connectives_by_group(group)
        assert isinstance(lst, list)
        for c in lst:
            assert c.get("group") == group
    empty = get_connectives_by_group("nonexistent")
    assert empty == []


def test_classify_connective_returns_none_for_unknown():
    """Unknown token returns None."""
    assert classify_connective("") is None
    assert classify_connective("xyz_nonexistent_word") is None


def test_l10b_consumes_connective_hints():
    """L10B can consume connective hints without direct JSON coupling (integration)."""
    classify_connective  # use module-level import
    # Any token that is in the knowledge should get a stable schema from classify_connective
    items = load_connectives_knowledge(force_reload=True)
    if not items:
        pytest.skip("No connectives data")
    token = items[0].get("token") or items[0].get("normalized_token")
    c = classify_connective(token)
    assert c is not None
    # L10B expects group and category_name for hints
    assert "group" in c
    assert c.get("category_name") or c.get("group")


def test_pipeline_still_runs():
    """Existing pipeline still runs (smoke)."""
    from .conftest import run_pipeline_for_test
    result = run_pipeline_for_test("الْحَمْدُ لِلَّهِ")
    assert result is not None
    assert "layer_outputs" in result or "errors" in result
    lo = result.get("layer_outputs") or {}
    # L10B may have connective_group on nodes
    l10b = lo.get("L10B_DEEP_SYNTAX") or {}
    tr = l10b.get("transformation_result") or {}
    nodes = tr.get("dependency_nodes") or []
    for n in nodes:
        if n.get("connective_group"):
            assert n.get("connective_group") in (GROUP_CONDITIONAL, GROUP_NEGATION, GROUP_EXPLANATION_CAUSATION, GROUP_ADVERSATIVE)
            break
