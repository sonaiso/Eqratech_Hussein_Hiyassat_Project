# -*- coding: utf-8 -*-
from orchestrator.quran_gold.alignment import (
    AlignmentStatus,
    align_gold_words_to_tokens,
    normalize_arabic_surface,
)


def test_normalize_wasla():
    a = "\u0671" + "\u0644\u0644\u0647"  # ٱلله style
    b = "\u0627" + "\u0644\u0644\u0647"
    assert normalize_arabic_surface(a) == normalize_arabic_surface(b)


def test_align_simple():
    gold = ["أ", "ب"]
    tok = ["أ", "ب"]
    res, aln, amb = align_gold_words_to_tokens(gold, tok)
    assert aln == 2 and amb == 0
    assert res[0].status == AlignmentStatus.ALIGNED
    assert res[1].token_index == 1


def test_align_duplicate_surface_ambiguous():
    gold = ["ما", "ما"]
    tok = ["ما", "ما"]
    res, aln, amb = align_gold_words_to_tokens(gold, tok)
    assert res[0].status == AlignmentStatus.AMBIGUOUS
    assert res[0].token_index is None
    assert res[1].status == AlignmentStatus.ALIGNED
    assert res[1].token_index == 1
