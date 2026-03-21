# -*- coding: utf-8 -*-
"""
Regression: hollow passive participle (اسم المفعول الأجوف) — root and ISM_MAFUUL.
Forbidden wrong analyses: ق-ي-ل (for مقول), ب-و-ع (for مبيع), خ-ي-ف (for مخوف).
"""

from __future__ import annotations

import pytest

from orchestrator.arabic_word_state import ensure_arabic_word_state, ref_word_state_for_token
from orchestrator.l14_jamid_mushtaq import build_jamid_mushtaq

FORBIDDEN_WRONG = frozenset({"ق-ي-ل", "ب-و-ع", "خ-ي-ف"})


def _lo(surface: str, *, l8_root: str, l9_tpl: str = "مَفْعُول", l9_ww: str = "مَفْعُول") -> dict:
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": l8_root}]}},
        "L9_WAZN_MATCHING": {
            "transformation_result": {"words": [{"word": surface, "template": l9_tpl, "word_wazn": l9_ww}]}
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


def _assert_mafuul(tc: dict, expected_root: str) -> None:
    assert tc.get("derivational_class") == "ISM_MAFUUL", tc
    assert tc.get("jamid_or_mushtaq") == "MUSHTAQ", tc
    assert tc.get("root") == expected_root, tc
    assert tc.get("root") not in FORBIDDEN_WRONG


@pytest.mark.parametrize(
    ("surface", "wrong_l8", "expected_root"),
    [
        ("مَقُول", "ق-ي-ل", "ق-و-ل"),
        ("المَقُول", "ق-ي-ل", "ق-و-ل"),
        ("مَبِيع", "ب-و-ع", "ب-ي-ع"),
        ("المَبِيعَات", "ب-و-ع", "ب-ي-ع"),
        ("مَخُوف", "خ-ي-ف", "خ-و-ف"),
    ],
)
def test_hollow_ism_mafuul_root_and_class(surface: str, wrong_l8: str, expected_root: str) -> None:
    lo = _lo(surface, l8_root=wrong_l8)
    ensure_arabic_word_state(lo)
    st = ref_word_state_for_token(lo, "0")
    assert st.get("root") == expected_root
    assert st.get("root") not in FORBIDDEN_WRONG
    assert st.get("hollow_ism_mafuul") is True

    out = build_jamid_mushtaq(lo)
    tc = (out or {}).get("token_classifications") or []
    assert len(tc) == 1
    _assert_mafuul(tc[0], expected_root)


def test_hollow_ism_mafuul_no_l9_wazn() -> None:
    surface = "مَقُول"
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": "ق-ي-ل"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": surface, "template": "", "word_wazn": ""}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    _assert_mafuul(tc, "ق-و-ل")
    assert tc.get("rule") in ("hollow_ism_mafuul_lexicon", "hollow_ism_mafuul_shape")


def test_wal_makhufiin_stem_align() -> None:
    """وَالْمَخُوفِينَ → stem مخوف → خ-و-ف."""
    surface = "وَالْمَخُوفِينَ"
    lo = _lo(surface, l8_root="خ-ي-ف")
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    _assert_mafuul(tc, "خ-و-ف")


def test_forbidden_wrong_roots_fail() -> None:
    for surface, wrong, ok in [
        ("مَقُول", "ق-ي-ل", "ق-و-ل"),
        ("مَبِيع", "ب-و-ع", "ب-ي-ع"),
        ("مَخُوف", "خ-ي-ف", "خ-و-ف"),
    ]:
        lo = _lo(surface, l8_root=wrong)
        r = build_jamid_mushtaq(lo)["token_classifications"][0].get("root")
        assert r == ok
        assert r not in FORBIDDEN_WRONG
