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


def test_align_duplicate_surface_order_preserving():
    gold = ["ما", "ما"]
    tok = ["ما", "ما"]
    res, aln, amb = align_gold_words_to_tokens(gold, tok)
    assert aln == 2 and amb == 0
    assert res[0].token_index == 0
    assert res[1].token_index == 1


def test_prefix_wa_on_token():
    from orchestrator.quran_gold.alignment import align_gold_words_to_pipeline_tokens

    gold = ["إِيَّاكَ"]
    tok = ["وَإِيَّاكَ"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].outcome.value.startswith("aligned")
    assert r[0].token_index == 0


def test_order_conflict():
    from orchestrator.quran_gold.alignment import AlignmentOutcome, align_gold_words_to_pipeline_tokens

    gold = ["ب", "أ"]
    tok = ["أ", "ب"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].outcome == AlignmentOutcome.ALIGNMENT_ORDER_CONFLICT or r[1].outcome == AlignmentOutcome.ALIGNMENT_ORDER_CONFLICT


def test_superscript_alif_csv_vs_uthmani():
    from orchestrator.quran_gold.alignment import align_gold_words_to_pipeline_tokens

    gold = ["الرَّحْمَنِ"]
    tok = ["ٱلرَّحْمَٰنِ"]
    r = align_gold_words_to_pipeline_tokens(gold, tok)
    assert r[0].token_index == 0
    assert r[0].outcome.value.startswith("aligned")
