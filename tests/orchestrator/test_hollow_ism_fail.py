# -*- coding: utf-8 -*-
"""
Regression: hollow-verb active participle (اسم الفاعل الأجوف) — root and ISM_FAIL.
Forbidden surface roots: ص-ي-م, ق-ي-ل, خ-ي-ف for the reference lemmas.
"""

from __future__ import annotations

import pytest

from orchestrator.arabic_word_state import ensure_arabic_word_state, ref_word_state_for_token
from orchestrator.l14_jamid_mushtaq import build_jamid_mushtaq


FORBIDDEN_WRONG_HOLLOW_ROOTS = frozenset({"ص-ي-م", "ق-ي-ل", "خ-ي-ف"})


def _base_lo(surface: str, *, l8_root: str, l9_tpl: str = "فَاعِل", l9_ww: str = "فَاعِل") -> dict:
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": l8_root}]}},
        "L9_WAZN_MATCHING": {
            "transformation_result": {"words": [{"word": surface, "template": l9_tpl, "word_wazn": l9_ww}]}
        },
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }


def _assert_ism_fail_and_root(tc: dict, expected_root: str) -> None:
    assert tc.get("derivational_class") == "ISM_FAIL", tc
    assert tc.get("jamid_or_mushtaq") == "MUSHTAQ", tc
    assert tc.get("root") == expected_root, tc
    assert tc.get("root") not in FORBIDDEN_WRONG_HOLLOW_ROOTS


@pytest.mark.parametrize(
    ("surface", "wrong_l8", "expected_root"),
    [
        ("صَائِم", "ص-ي-م", "ص-و-م"),
        ("وَالصَّائِمَاتِ", "ص-ي-م", "ص-و-م"),
        ("قَائِل", "ق-ي-ل", "ق-و-ل"),
        ("البَائِعِينَ", "ب-و-ع", "ب-ي-ع"),  # L8 may guess wrong middle; lexicon fixes to باع
        ("الخَائِفُونَ", "خ-ي-ف", "خ-و-ف"),
    ],
)
def test_hollow_ism_fail_root_and_class(surface: str, wrong_l8: str, expected_root: str) -> None:
    lo = _base_lo(surface, l8_root=wrong_l8)
    ensure_arabic_word_state(lo)
    st = ref_word_state_for_token(lo, "0")
    assert st.get("root") == expected_root
    assert st.get("root") not in FORBIDDEN_WRONG_HOLLOW_ROOTS
    assert st.get("hollow_ism_fail") is True

    out = build_jamid_mushtaq(lo)
    tc = (out or {}).get("token_classifications") or []
    assert len(tc) == 1
    _assert_ism_fail_and_root(tc[0], expected_root)


def test_hollow_ism_fail_without_l9_wazn_still_ism_fail() -> None:
    """Empty L9 but hollow stem + wrong L8 root → lexicon fixes root; RULE 1H classifies ISM_FAIL."""
    surface = "صَائِم"
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": "noun"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": "ص-ي-م"}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": [{"word": surface, "template": "", "word_wazn": ""}]}},
        "L8B_VERB_BAB_GOVERNANCE": {"transformation_result": {"verb_governance_profiles": []}},
    }
    out = build_jamid_mushtaq(lo)
    tc = out["token_classifications"][0]
    _assert_ism_fail_and_root(tc, "ص-و-م")
    assert tc.get("rule") in (
        "hollow_ism_fail_lexicon",
        "hollow_ism_fail_shape",
        "wazn_ism_fail_pattern",  # canonical wazn recovery may supply فَاعِل before pattern gate
    )


def test_forbidden_wrong_roots_rejected() -> None:
    """Explicit regression: outputs must not contain the surface-hamza wrong analyses."""
    for surface, wrong, ok in [
        ("صَائِم", "ص-ي-م", "ص-و-م"),
        ("قَائِل", "ق-ي-ل", "ق-و-ل"),
        ("الخَائِفُونَ", "خ-ي-ف", "خ-و-ف"),
    ]:
        lo = _base_lo(surface, l8_root=wrong)
        out = build_jamid_mushtaq(lo)
        r = out["token_classifications"][0].get("root")
        assert r == ok
        assert r not in FORBIDDEN_WRONG_HOLLOW_ROOTS
