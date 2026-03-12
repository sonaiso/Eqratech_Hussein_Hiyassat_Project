# -*- coding: utf-8 -*-
"""Tests for Rhetoric Signals V1 extractor."""

from __future__ import annotations

import pytest

from engines.rhetoric.extractor import RhetoricSignalsExtractor
from engines.rhetoric.types import RhetoricSignal


@pytest.fixture
def extractor() -> RhetoricSignalsExtractor:
    return RhetoricSignalsExtractor()


def test_interrogative_hal(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["هل", "جئت"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    istifham = next((s for s in signals if s.type == "interrogative"), None)
    assert istifham is not None
    assert istifham.label_ar == "استفهام"
    assert istifham.trigger == "هل"
    assert istifham.span == {"start": 0, "end": 1}
    assert istifham.confidence >= 0.8
    assert "استفهام" in istifham.evidence[0] or "هل" in istifham.evidence[0]


def test_vocative_ya(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["يا", "أيها", "الناس"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    nida = next((s for s in signals if s.type == "vocative"), None)
    assert nida is not None
    assert nida.label_ar == "نداء"
    assert nida.trigger == "يا"
    assert nida.span["start"] == 0


def test_oath_wallah(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["والله", "لأفعلن"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    qasam = next((s for s in signals if s.type == "oath"), None)
    assert qasam is not None
    assert qasam.label_ar == "قسم"
    assert "والله" in qasam.trigger or qasam.trigger == "والله"


def test_tarajji_laalla(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["لعل", "الله", "يرحمنا"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    tarajji = next((s for s in signals if s.type == "tarajji"), None)
    assert tarajji is not None
    assert tarajji.label_ar == "ترجّي"
    assert "لعل" in tarajji.trigger or tarajji.trigger == "لعل"


def test_tamanni_layta(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["ليت", "شبابا", "يعود"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    tamanni = next((s for s in signals if s.type == "tamanni"), None)
    assert tamanni is not None
    assert tamanni.label_ar == "تمنّي"
    assert tamanni.trigger == "ليت"


def test_imperative_from_sentence_type(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["اكتب", "الدرس"]
    signals = extractor.extract(tokens, sentence_type="أمر")
    assert len(signals) >= 1
    amr = next((s for s in signals if s.type == "imperative"), None)
    assert amr is not None
    assert amr.label_ar == "أمر"


def test_prohibition_from_sentence_type(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["لا", "تذهب"]
    signals = extractor.extract(tokens, sentence_type="نهي")
    assert len(signals) >= 1
    nahy = next((s for s in signals if s.type == "prohibition"), None)
    assert nahy is not None
    assert nahy.label_ar == "نهي"


def test_emphasis_inna(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["إن", "الله", "غفور"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    tawkid = next((s for s in signals if s.type == "emphasis"), None)
    assert tawkid is not None
    assert tawkid.label_ar == "توكيد"


def test_exclusivity_innama(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["إنما", "الله", "واحد"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    qasr = next((s for s in signals if s.type == "exclusivity"), None)
    assert qasr is not None
    assert qasr.label_ar == "قصر"


def test_exclusivity_ma_illa(extractor: RhetoricSignalsExtractor) -> None:
    tokens = ["ما", "نجح", "إلا", "المجتهد"]
    signals = extractor.extract(tokens)
    assert len(signals) >= 1
    qasr = next((s for s in signals if s.type == "exclusivity"), None)
    assert qasr is not None
    assert qasr.span["start"] <= qasr.span["end"]


def test_multi_label_oath_and_emphasis(extractor: RhetoricSignalsExtractor) -> None:
    # والله لأفعلنّ — oath (والله) + emphasis (ل or نّ)
    tokens = ["والله", "لأفعلن"]
    signals = extractor.extract(tokens)
    types = [s.type for s in signals]
    assert "oath" in types
    assert "emphasis" in types
    assert len(signals) >= 2


def test_negative_no_signals(extractor: RhetoricSignalsExtractor) -> None:
    """Sentence with no surface rhetoric triggers should yield no signals."""
    tokens = ["الرجل", "جلس", "في", "البيت"]
    signals = extractor.extract(tokens, sentence_type="خبرية")
    assert isinstance(signals, list)
    assert len(signals) == 0
