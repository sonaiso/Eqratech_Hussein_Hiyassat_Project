from fvafk.c1.cv_pattern import analyze_text_for_cv_after_phonology


def _cv_one(token: str):
    r = analyze_text_for_cv_after_phonology(token)
    assert r["engine"] == "word2cv"
    assert r["total_words_computed"] == 1
    assert len(r["words"]) == 1
    return r["words"][0]


def test_word2cv_pipeline_matches_src_word_2_cv():
    """CV / cv_advanced must match src/word-2-cv.py (single source of truth)."""
    cases = {
        "كِتَاب": {"cv": "CVCVVC", "cv_advanced": "CViCVAC"},
        "يَوْم": {"cv": "CVCC", "cv_advanced": "CVaCC"},
        "مُدَرِّس": {"cv": "CVCVCCVC", "cv_advanced": "CVoCVaCCViC"},
    }
    for token, expected in cases.items():
        got = _cv_one(token)
        assert got["cv"] == expected["cv"] and got["cv_advanced"] == expected["cv_advanced"], (
            token,
            got,
            expected,
        )
