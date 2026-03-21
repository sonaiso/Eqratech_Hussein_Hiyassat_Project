# -*- coding: utf-8 -*-
"""Canonical hollow root + stem wazn propagation (ARABIC_WORD_STATE, display rows)."""

from __future__ import annotations

import re

from src.orchestrator.arabic_word_state import (
    build_root_wazn_display_rows,
    rebuild_arabic_word_state_from_layers,
    ref_word_state_for_token,
)

_DIAC = re.compile(r"[\u064b-\u0652\u0670]")


def _strip_d(s: str) -> str:
    return _DIAC.sub("", s or "")


def _lo(surface: str, l8_root: str, kind: str = "noun") -> dict:
    return {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": surface}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": surface, "kind": kind}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": surface, "root": l8_root}]}},
        "L9_WAZN_MATCHING": {"transformation_result": {"words": []}},
    }


def test_canonical_root_hollow_participle_lexicon_and_display_rows() -> None:
    cases = [
        ("صَائِم", "ص-ي-م", "ص-و-م"),
        ("وَالصَّائِمَاتِ", "ص-ي-م", "ص-و-م"),
        ("قَائِل", "ق-ي-ل", "ق-و-ل"),
        ("البَائِعِينَ", "ب-ي-ع", "ب-ي-ع"),
        ("الخَائِفُونَ", "خ-ي-ف", "خ-و-ف"),
    ]
    for surface, wrong_l8, expected in cases:
        lo = _lo(surface, wrong_l8)
        rebuild_arabic_word_state_from_layers(lo)
        st = ref_word_state_for_token(lo, "0")
        assert (st.get("root") or "") == expected, f"{surface}: root got {st.get('root')}"
        assert (st.get("canonical_root") or "") == expected, f"{surface}: canonical_root"
        rows = build_root_wazn_display_rows(lo)
        assert rows[0].get("root") == expected


def test_muftal_stem_wazn_muslim_mu_min() -> None:
    for surface, wrong in (
        ("وَالْمُسْلِمَاتِ", "س-ل-م"),
        ("وَالْمُؤْمِنِينَ", "ا-م-ن"),
    ):
        lo = _lo(surface, wrong, kind="noun")
        rebuild_arabic_word_state_from_layers(lo)
        st = ref_word_state_for_token(lo, "0")
        wz = (st.get("canonical_wazn") or st.get("wazn_template") or "").strip()
        assert wz and wz != "—", f"{surface}: expected wazn, got {wz!r}"
        assert "مُفْعِل" in wz


def test_hollow_stem_wazn_sa_imiin_not_dash() -> None:
    """Long surface + hollow participle: stem صَائِم → wazn from فاعل family, not —."""
    surface = "وَالصَّائِمِينَ"
    lo = _lo(surface, "ص-ي-م", kind="noun")
    rebuild_arabic_word_state_from_layers(lo)
    st = ref_word_state_for_token(lo, "0")
    wz = (st.get("canonical_wazn") or st.get("wazn_template") or "").strip()
    assert wz and wz != "—", f"{surface}: expected wazn, got {wz!r}"
    assert (st.get("root") or "") == "ص-و-م"


def test_geminate_verb_template_not_malformed_faal() -> None:
    lo = {
        "L2_TOKENIZATION": {"transformation_result": {"tokens": [{"word": "أَعَدَّ"}]}},
        "L5_WORD_TYPING": {"transformation_result": {"words": [{"word": "أَعَدَّ", "kind": "verb"}]}},
        "L8_ROOT_EXTRACTION": {"transformation_result": {"words": [{"word": "أَعَدَّ", "root": "ع-د-د"}]}},
        "L9_WAZN_MATCHING": {
            "transformation_result": {"words": [{"word": "أَعَدَّ", "template": "فَعَلَّ", "word_wazn": ""}]}
        },
    }
    rebuild_arabic_word_state_from_layers(lo)
    st = ref_word_state_for_token(lo, "0")
    tpl = (st.get("wazn_template") or "").strip()
    nd = _strip_d(tpl).replace("\u0651", "")
    assert "فعلل" not in nd
    assert "فَعَّ" in tpl or "فعل" not in nd
