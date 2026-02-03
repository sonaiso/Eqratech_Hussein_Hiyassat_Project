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
    """
    Extracts consonantal roots from Arabic words.
    
    Handles trilateral (3-letter) and quadrilateral (4-letter) roots. Strips
    known affixes, normalizes hamza carriers, and filters pattern vowels to
    identify the underlying root consonants.
    
    Example:
        >>> extractor = RootExtractor()
        >>> root = extractor.extract("كَاتِب")
        >>> print('-'.join(root.letters))
        ك-ت-ب
    """
    DIACRITICS = "َُِْٰٓٔٱًٌٍّ"
    WEAK_LETTERS = {'و', 'ي', 'ا', 'ء'}
    PATTERN_LETTERS = {'ا', 'و', 'ي'}

    PREFIXES = [
        'است',  # استفعل
        'ال', 'وال', 'فال', 'بال', 'كال', 'لل',  # أل التعريف
        'س', 'سي', 'سو',  # حرف استقبال
        'ف', 'و', 'ب', 'ك', 'ل',  # حروف عطف/جر
        'م', 'ت', 'ي', 'ن', 'أ',  # حروف مضارعة
        'تـ', 'يـ', 'نـ'
    ]
    SUFFIXES = [
        'ون', 'ين', 'ات', 'ان', 'تم', 'تن', 'وا',  # ضمائر جمع
        'ها', 'هم', 'هما', 'هن', 'كم', 'كن',  # ضمائر غائب/مخاطب
        'ني', 'نا', 'ك', 'ه', 'ة', 'ن'  # ضمائر مفرد + تاء مربوطة
    ]

    def __init__(self, known_roots: Optional[Set[str]] = None):
        """
        Initialize root extractor.
        
        Args:
            known_roots: Optional set of valid roots for validation
        """
        self.known_roots = known_roots or set()

    def extract(self, word: str) -> Optional[Root]:
        """
        Extract root from Arabic word.
        
        Args:
            word: Arabic word (with or without diacritics)
        
        Returns:
            Root object or None if extraction fails
        """
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
        # حذف البادئات المعقدة أولاً (است، ال، وال، إلخ)
        complex_prefixes = [p for p in self.PREFIXES if len(p) >= 2]
        for prefix in sorted(complex_prefixes, key=len, reverse=True):
            if text.startswith(prefix) and len(text) - len(prefix) >= 3:
                text = text[len(prefix):]
                break
        
        # حذف البادئات البسيطة (ف، س، ي، إلخ) - يمكن أن يكون عدة حروف
        simple_prefixes = ['ف', 'و', 'ב', 'س', 'ي', 'ת', 'ן', 'أ', 'م']
        max_iterations = 3  # أقصى عدد من البادئات البسيطة
        for _ in range(max_iterations):
            removed = False
            for prefix in simple_prefixes:
                if text.startswith(prefix) and len(text) - len(prefix) >= 3:
                    text = text[1:]
                    removed = True
                    break
            if not removed:
                break
        
        # حذف اللواحق - يمكن أن يكون عدة لواحق
        for _ in range(2):  # حد أقصى لاحقتان
            removed = False
            for suffix in sorted(self.SUFFIXES, key=len, reverse=True):
                if text.endswith(suffix) and len(text) - len(suffix) >= 3:
                    text = text[:-len(suffix)]
                    removed = True
                    break
            if not removed:
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
        
        # إزالة التكرار الناتج عن الشدة في الأوزان الصرفية
        # مثال: "زرراع" (من زُرَّاع) → إزالة إحدى الراءات → "زراع"
        consonants = self._deduplicate_gemination(consonants)
        
        if len(consonants) == 4 and consonants[0] == consonants[1] and consonants[2] != consonants[0]:
            consonants = consonants[1:]
        if len(consonants) in (3, 4):
            return consonants
        if len(consonants) > 4:
            return consonants[:4]
        if len(consonants) < 3:
            return letters[:3] if len(letters) >= 3 else letters
        return consonants
    
    def _deduplicate_gemination(self, consonants: List[str]) -> List[str]:
        """
        إزالة الحروف المضعفة الناتجة عن الشدة في الأوزان الصرفية.
        
        مثال:
        - "زرراع" → ["ز", "ر", "ر", "ا", "ع"] → ["ز", "ر", "ا", "ع"]
        - "كتب" → ["ك", "ت", "ب"] → ["ك", "ت", "ب"] (بدون تغيير)
        
        القاعدة: إذا كان هناك حرفان متتاليان متطابقان، نزيل أحدهما
        إلا إذا كان الجذر رباعياً حقيقياً (مثل: زلزل، وسوس).
        """
        if len(consonants) <= 3:
            return consonants
        
        result: List[str] = []
        i = 0
        while i < len(consonants):
            current = consonants[i]
            # تحقق من وجود حرف متطابق تالٍ
            if i + 1 < len(consonants) and consonants[i + 1] == current:
                # أضف الحرف مرة واحدة فقط
                result.append(current)
                # تجاوز الحرف المكرر
                i += 2
            else:
                result.append(current)
                i += 1
        
        return result

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
