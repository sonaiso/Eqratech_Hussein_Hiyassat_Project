import pytest


def test_initial_shadda_wasl_does_not_create_initial_cc_cluster():
    """
    Wasl context (prev token exists):
    "كُنتُم مُّؤْمِنِينَ" should not produce an initial CC cluster in CV for the second token.
    """
    from fvafk.c1.cv_pattern import analyze_text_for_cv_after_phonology

    out = analyze_text_for_cv_after_phonology("كُنتُم مُّؤْمِنِينَ")
    assert out["total_words_computed"] == 2

    cv2 = out["words"][1]["cv"]
    assert isinstance(cv2, str)
    assert not cv2.startswith("CC")

