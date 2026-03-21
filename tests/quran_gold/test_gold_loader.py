# -*- coding: utf-8 -*-
from orchestrator.quran_gold.ayah_loader import get_ayah_text, load_ayah_text_index


def test_get_ayah_text_fatiha():
    t = get_ayah_text(1, 1)
    assert t is not None
    assert "بِسْمِ" in t or "ٱللَّهِ" in t


def test_index_nonempty():
    idx = load_ayah_text_index()
    assert len(idx) > 6000
