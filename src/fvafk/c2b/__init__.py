"""
Morphology (C2b) package.
"""

from .morpheme import (
    Affix,
    AffixType,
    Morpheme,
    MorphologicalAnalysis,
    Pattern,
    PatternType,
    Root,
    RootType,
)
from .root_extractor import RootExtractor

__all__ = [
    "Affix",
    "AffixType",
    "Morpheme",
    "MorphologicalAnalysis",
    "Pattern",
    "PatternType",
    "Root",
    "RootType",
    "RootExtractor",
]
