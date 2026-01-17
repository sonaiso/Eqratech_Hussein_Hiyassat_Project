"""
FractalHub Data Module

Provides:
- Dictionary loading (v01 and v02)
- Dictionary validation
- Unit/gate/invariant lookup
"""

from fractalhub.data.loader import load_dictionary, DictionaryLoader

__all__ = [
    "load_dictionary",
    "DictionaryLoader",
]
