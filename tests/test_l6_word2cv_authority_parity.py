# -*- coding: utf-8 -*-
"""Parity: ``word2cv_authority`` ≡ ``analyze_text_for_cv_after_phonology`` ≡ direct ``word-2-cv``."""

from __future__ import annotations

from fvafk.c1.cv_pattern import analyze_text_for_cv_after_phonology
from fvafk.c1.word2cv_loader import analyze_token_for_pipeline
from word2cv_authority import compute_authoritative_cv_analysis


def test_single_word_parity_ar_rahmān():
    text = "الرَّحْمَنُ"
    auth = compute_authoritative_cv_analysis(text)
    pipe = analyze_text_for_cv_after_phonology(text)
    assert auth == pipe
    assert len(auth["words"]) == 1
    w = auth["words"][0]
    assert w["cv"] == "CVCCVCCVCV"
    assert w["cv_advanced"] == "CVaCCVaCCVaCVo"
    assert w["word_normalized"] == "ٱلرَّحْمَنُ"
    direct = analyze_token_for_pipeline(text)
    assert w["cv"] == direct["cv"] and w["cv_advanced"] == direct["cv_advanced"]


def test_multi_token_parity():
    text = "الرَّحْمَنُ عَلَى الْعَرْشِ"
    auth = compute_authoritative_cv_analysis(text)
    pipe = analyze_text_for_cv_after_phonology(text)
    assert auth == pipe
    assert len(auth["words"]) == 3
    # Token 1 and 3: explicit expected from authority; token 2 = عَلَى (not EXCLUDE_EXACT)
    assert auth["words"][0]["cv"] == "CVCCVCCVCV"
    assert auth["words"][1]["word"] == "عَلَى"
    assert auth["words"][1]["cv"] == "CVCVC"
    assert auth["words"][2]["word"] == "الْعَرْشِ"
    assert auth["words"][2]["cv_advanced"].startswith("CV")


def test_raw_mode_authoritative_matches_direct():
    """Raw display is debug-only; per-token values still come from word-2-cv."""
    tok = "الرَّحْمَنُ"
    a = analyze_token_for_pipeline(tok)
    r = compute_authoritative_cv_analysis(tok)["words"][0]
    assert r["cv"] == a["cv"] and r["cv_advanced"] == a["cv_advanced"]


def test_g_wasl_does_not_change_cv_fields():
    from fvafk.cli.main import MinimalCLI

    text = "الرَّحْمَنُ"
    cli = MinimalCLI()
    out = cli.run(text=text, morphology=False, multi_word=False)
    w = out["c1"]["cv_analysis"]["words"][0]
    direct = analyze_token_for_pipeline(text)
    assert w["cv"] == direct["cv"]
    assert w["cv_advanced"] == direct["cv_advanced"]
    gates = out["c2a"]["gates"]
    wasl = next((g for g in gates if g.get("gate_id") == "G_WASL"), None)
    assert wasl is not None
    assert wasl["status"] in ("WARN", "ACCEPT")
