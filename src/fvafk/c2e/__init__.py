# -*- coding: utf-8 -*-
"""C2e — Morphological Enrichment Layer.

Takes c2b output (word, kind, root, affixes, features) and adds deep
morphological features: tense, voice, person, number, gender for verbs;
derivation and pattern_type for nouns.
"""
from fvafk.c2e.enricher import MorphEnricher, EnrichmentResult, VerbFeatures, NounFeatures

__all__ = ["MorphEnricher", "EnrichmentResult", "VerbFeatures", "NounFeatures"]
