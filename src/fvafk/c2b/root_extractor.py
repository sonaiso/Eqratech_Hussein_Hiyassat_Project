"""
Root extraction for Arabic words.
"""

from __future__ import annotations

import re
import unicodedata
from typing import List, Optional, Set

from .morpheme import Root, RootType


def normalize_hamza_for_roots(text: str) -> str:
    """
    Universal hamza normalization for root extraction.

    Applies Arabic orthographic rules:
    - Hamza carriers → base letters
    - Preserves linguistic structure
    - Works for ALL Arabic words

    Args:
        text: Arabic text with possible hamza carriers

    Returns:
        Normalized text with hamza carriers replaced by base letters

    Examples:
        >>> normalize_hamza_for_roots("مُؤْمِنُونَ")
        "مامنون"  # ؤ → ا
        >>> normalize_hamza_for_roots("أَكَلَ")
        "اكل"  # أ → ا
    """
    text = unicodedata.normalize('NFC', text)
    text = text.replace('أ', 'ا')
    text = text.replace('إ', 'ا')
    text = text.replace('آ', 'ا')
    text = text.replace('ؤ', 'ا')
    text = text.replace('ئ', 'ي')
    text = ''.join(
        c
        for c in unicodedata.normalize('NFD', text)
        if unicodedata.category(c) != 'Mn'
    )
    return unicodedata.normalize('NFC', text)


class RootExtractor:
    DIACRITICS = "َُِْٰٓٔٱًٌٍّ"
    WEAK_LETTERS = {'و', 'ي', 'ا', 'ء'}
    PATTERN_LETTERS = {'ا', 'و', 'ي'}

    PREFIXES = ['است', 'ال', 'وال', 'فال', 'بال', 'كال', 'لل', 'م', 'ت', 'ي', 'ن', 'أ', 'تـ', 'يـ', 'نـ']
    SUFFIXES = ['ون', 'ين', 'ات', 'ان', 'ات', 'ة', 'ه', 'ها', 'هم', 'كم', 'هما', 'نا', 'ن']

    def __init__(self, known_roots: Optional[Set[str]] = None):
        self.known_roots = known_roots or set()

    def extract(self, word: str) -> Optional[Root]:
        if not word:
            return None

        normalized = self._normalize(word)
        normalized = normalize_hamza_for_roots(normalized)
        stripped = self._strip_affixes(normalized)
        consonants = self._extract_consonants(stripped)

        if self._is_valid_root(consonants):
            root_type = RootType.TRILATERAL if len(consonants) == 3 else RootType.QUADRILATERAL
            letters = tuple(consonants[:len(consonants)])
            return Root(letters=letters, root_type=root_type)
        return None

    def _normalize(self, word: str) -> str:
        buffer: List[str] = []
        i = 0
        while i < len(word):
            ch = word[i]
            if ch == 'ّ':
                if buffer:
                    buffer.append(buffer[-1])
                i += 1
                continue
            if ch in self.DIACRITICS or ch == 'ـ':
                i += 1
                continue
            buffer.append(ch)
            i += 1
        text = ''.join(buffer)
        text = text.replace('أ', 'ا').replace('إ', 'ا').replace('آ', 'ا')
        text = text.replace('ى', 'ي')
        text = re.sub(r'[\u064B-\u065F\u0670]', '', text)
        text = text.replace('أ', 'ا').replace('إ', 'ا').replace('آ', 'ا')
        text = text.replace('ى', 'ي').replace('ـ', '')
        text = re.sub(r'[\u064B-\u065F\u0670]', '', text)
        return text.strip()

    def _strip_affixes(self, word: str) -> str:
        text = word
        for prefix in sorted(self.PREFIXES, key=len, reverse=True):
            if text.startswith(prefix) and len(text) - len(prefix) >= 3:
                text = text[len(prefix):]
                break
        for suffix in sorted(self.SUFFIXES, key=len, reverse=True):
            if text.endswith(suffix) and len(text) - len(suffix) >= 3:
                text = text[:-len(suffix)]
                break
        return text.strip()

    def _extract_consonants(self, word: str) -> List[str]:
        letters = [ch for ch in word if self._is_arabic_letter(ch)]
        consonants: List[str] = []
        for idx, letter in enumerate(letters):
            if letter in self.PATTERN_LETTERS and 0 < idx < len(letters) - 1:
                prev_is_consonant = letters[idx - 1] not in self.PATTERN_LETTERS
                next_is_consonant = letters[idx + 1] not in self.PATTERN_LETTERS
                if prev_is_consonant and next_is_consonant:
                    continue
            consonants.append(letter)
        if len(consonants) == 4 and consonants[0] == consonants[1] and consonants[2] != consonants[0]:
            consonants = consonants[1:]
        if len(consonants) in (3, 4):
            return consonants
        if len(consonants) > 4:
            return consonants[:4]
        if len(consonants) < 3:
            return letters[:3] if len(letters) >= 3 else letters
        return consonants

    def _is_valid_root(self, letters: List[str]) -> bool:
        if len(letters) not in (3, 4):
            return False
        if self.known_roots:
            root_str = '-'.join(letters)
            if root_str not in self.known_roots:
                return False
        return all(self._is_arabic_letter(ch) for ch in letters)

    def _is_arabic_letter(self, ch: str) -> bool:
        return bool(ch) and ((0x0621 <= ord(ch) <= 0x064A) or ch in {'ة', 'ى'})
