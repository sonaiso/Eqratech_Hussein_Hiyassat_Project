# -*- coding: utf-8 -*-
"""Tests for c2e Morphological Enrichment Layer."""
from __future__ import annotations

import pytest
from fvafk.c2e import MorphEnricher, EnrichmentResult


def _enrich(word: str, stripped: str, kind: str, root: str, **kwargs) -> EnrichmentResult:
    enricher = MorphEnricher()
    return enricher.enrich(word, stripped, kind, root, **kwargs)


# ---------- Verb: tense ----------
def test_verb_tense_madi():
    r = _enrich("كَتَبَ", "كتب", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.tense == "ماضي"


def test_verb_tense_mudari():
    r = _enrich("يَكْتُبُ", "يكتب", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.tense == "مضارع"


def test_verb_tense_amr():
    r = _enrich("اكْتُبْ", "اكتب", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.tense == "أمر"


# ---------- Verb: voice ----------
def test_verb_voice_majhul():
    r = _enrich("كُتِبَ", "كتب", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.voice == "مجهول"


# ---------- Verb: gender ----------
def test_verb_gender_muannath():
    r = _enrich("كَتَبَتْ", "كتبت", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.gender == "مؤنث"


# ---------- Verb: number ----------
def test_verb_number_jam():
    r = _enrich("كَتَبُوا", "كتبوا", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.number == "جمع"


def test_verb_number_muthanna():
    r = _enrich("كَتَبَا", "كتبا", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.number == "مثنى"


def test_verb_number_jam_mudari():
    r = _enrich("يَكْتُبُونَ", "يكتبون", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.number == "جمع"


# ---------- Verb: person ----------
def test_verb_person_first():
    r = _enrich("أَكْتُبُ", "اكتب", "verb", "كتب")
    assert r.verb_features is not None
    assert r.verb_features.person == 1


# ---------- Noun: derivation ----------
def test_noun_derivation_mushtaq():
    r = _enrich("الطَّالِبُ", "طالب", "noun", "طلب")
    assert r.derivation == "مشتق"


def test_noun_derivation_mushtaq_kitab():
    r = _enrich("كِتَابٌ", "كتاب", "noun", "كتب")
    assert r.derivation == "مشتق"


# ---------- Derivation: jamid ----------
def test_derivation_jamid_allah():
    r = _enrich("اللَّهُ", "", "mabni", "")
    assert r.derivation == "جامد"


def test_derivation_jamid_operator():
    r = _enrich("مِنْ", "", "operator", "")
    assert r.derivation == "جامد"


def test_derivation_jamid_particle():
    r = _enrich("عَلَى", "", "particle", "")
    assert r.derivation == "جامد"


# ---------- Result structure ----------
def test_result_has_to_dict():
    r = _enrich("كَتَبَ", "كتب", "verb", "كتب")
    d = r.to_dict()
    assert d["derivation"] == "مشتق"
    assert d["verb"] is not None
    assert d["verb"]["tense"] == "ماضي"
    assert d["noun"] is None


def test_noun_has_features():
    r = _enrich("الطَّالِبُ", "طالب", "noun", "طلب", c2b_features={"number": "singular", "gender": "masculine"})
    assert r.noun_features is not None
    assert r.derivation == "مشتق"
