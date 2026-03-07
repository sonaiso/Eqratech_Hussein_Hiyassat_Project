"""Enforce that detect_operator() does NOT strip diacritics: exact match and prefix variants only."""
from __future__ import annotations

from scripts.run_complete_snapshot import detect_operator


def test_operator_exact_match_requires_diacritics():
    """Catalog key 'بِ' must match only 'بِ', not bare 'ب' (no stripping)."""
    catalog = {
        "بِ": {"group_number": "1", "arabic_group": "حرف جر", "english_group": "preposition", "purpose": "genitive", "example": "", "note": ""},
    }
    # With diacritics: must match
    out_with = detect_operator("بِ", catalog)
    assert out_with["is_operator"] is True
    assert out_with["operator"] == "بِ"

    # Without diacritics (bare ب): must NOT match as operator (no stripping)
    out_bare = detect_operator("ب", catalog)
    assert out_bare["is_operator"] is False


def test_operator_prefix_stem_keeps_diacritics():
    """Prefix stripping consumes one unit (letter + diacritics); stem is matched exactly."""
    catalog = {
        "فِي": {"group_number": "1", "arabic_group": "حرف جر", "english_group": "preposition", "purpose": "genitive", "example": "", "note": ""},
    }
    # "وَفِي" -> prefix وَ + stem فِي
    out = detect_operator("وَفِي", catalog)
    assert out.get("has_operator_prefix") is True
    assert out.get("stem") == "فِي"
    assert out.get("stem_operator") == catalog["فِي"]
