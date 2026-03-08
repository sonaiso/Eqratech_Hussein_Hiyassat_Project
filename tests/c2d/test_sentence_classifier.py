"""Tests for C2d SentenceClassifier"""
import pytest
from fvafk.c2d import SentenceClassifier, SentenceType

sc = SentenceClassifier()

def test_khabariyya():
    r = sc.classify(["الجو", "جميل"])
    assert r.sentence_type == SentenceType.KHABARIYYA
    assert r.confidence >= 0.5

def test_istifham_hal():
    r = sc.classify(["هل", "فهمت"])
    assert r.sentence_type == SentenceType.ISTIFHAM
    assert r.trigger_word == "هل"

def test_istifham_man():
    r = sc.classify(["من", "أنت"])
    assert r.sentence_type == SentenceType.ISTIFHAM

def test_nida():
    r = sc.classify(["يا", "أحمد", "انتبه"])
    assert r.sentence_type == SentenceType.NIDA

def test_tamanni():
    r = sc.classify(["ليت", "الشباب", "يعود"])
    assert r.sentence_type == SentenceType.TAMANNI

def test_qasam():
    r = sc.classify(["والله", "لأجتهدن"])
    assert r.sentence_type == SentenceType.QASAM

def test_shart_in():
    r = sc.classify(["إن", "تجتهد", "تنجح"])
    assert r.sentence_type == SentenceType.SHART

def test_shart_law():
    r = sc.classify(["لو", "اجتهدت", "لنجحت"])
    assert r.sentence_type == SentenceType.SHART

def test_sababiyya():
    r = sc.classify(["نجح", "لأن", "اجتهد"])
    assert r.sentence_type == SentenceType.SABABIYYA

def test_nahy():
    r = sc.classify(["لا", "تهمل", "درسك"])
    assert r.sentence_type == SentenceType.NAHY

def test_madh():
    r = sc.classify(["نعم", "الرجل", "محمد"])
    assert r.sentence_type == SentenceType.MADH

def test_dhamm():
    r = sc.classify(["بئس", "الطالب", "الكسول"])
    assert r.sentence_type == SentenceType.DHAMM

def test_empty_tokens():
    r = sc.classify([])
    assert r.sentence_type == SentenceType.UNKNOWN
    assert r.confidence == 0.0

def test_to_dict_keys():
    r = sc.classify(["هل", "جئت"])
    d = r.to_dict()
    assert "sentence_type" in d
    assert "confidence" in d
    assert "trigger_word" in d

def test_confidence_high_for_markers():
    r = sc.classify(["يا", "زيد"])
    assert r.confidence >= 0.90