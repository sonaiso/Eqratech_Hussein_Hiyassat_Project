"""
PatternMatcher: Recognize Arabic morphological patterns.
"""

from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple

from .awzan_loader import AwzanPatternLoader
from .morpheme import Pattern, PatternType, Root


@dataclass(frozen=True)
class PatternTemplate:
    template: str
    pattern_type: PatternType
    category: str
    form: Optional[str] = None
    meaning: Optional[str] = None
    cv_simple: Optional[str] = None
    cv_detailed: Optional[str] = None
    cv_advanced: Optional[str] = None
    notes: Optional[str] = None

    def feature_map(self) -> Dict[str, str]:
        features: Dict[str, str] = {
            "pattern_type": self.pattern_type.name,
            "category": self.category,
        }
        if self.form:
            features["form"] = self.form
        if self.meaning:
            features["meaning"] = self.meaning
        if self.cv_simple:
            features["cv_simple"] = self.cv_simple
        if self.cv_detailed:
            features["cv_detailed"] = self.cv_detailed
        if self.cv_advanced:
            features["cv_advanced"] = self.cv_advanced
        if self.notes:
            features["notes"] = self.notes
        return features
    def matches_root_type(self, root: Root) -> bool:
        count = sum(1 for c in self.template if c in {'ف', 'ع', 'ل'})
        if len(root.letters) >= count:
            return True
        return False


class PatternDatabase:
    def __init__(self) -> None:
        self.patterns: List[PatternTemplate] = []
        self._initialize_patterns()

    def _initialize_patterns(self) -> None:
        base = [
            PatternTemplate(template="فَعَلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعَلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعِلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعُلَ", pattern_type=PatternType.FORM_I, category="verb", form="I"),
            PatternTemplate(template="فَعَّلَ", pattern_type=PatternType.FORM_II, category="verb", form="II"),
            PatternTemplate(template="فَاعَلَ", pattern_type=PatternType.FORM_III, category="verb", form="III"),
            PatternTemplate(template="أَفْعَلَ", pattern_type=PatternType.FORM_IV, category="verb", form="IV"),
            PatternTemplate(template="تَفَعَّلَ", pattern_type=PatternType.FORM_V, category="verb", form="V"),
            PatternTemplate(template="تَفَاعَلَ", pattern_type=PatternType.FORM_VI, category="verb", form="VI"),
            PatternTemplate(template="انْفَعَلَ", pattern_type=PatternType.FORM_VII, category="verb", form="VII"),
            PatternTemplate(template="افْتَعَلَ", pattern_type=PatternType.FORM_VIII, category="verb", form="VIII"),
            PatternTemplate(template="اسْتَفْعَلَ", pattern_type=PatternType.FORM_X, category="verb", form="X"),
            PatternTemplate(template="فَاعِل", pattern_type=PatternType.ACTIVE_PARTICIPLE, category="noun"),
            PatternTemplate(template="مَفْعُول", pattern_type=PatternType.PASSIVE_PARTICIPLE, category="noun"),
            PatternTemplate(template="مَفْعَل", pattern_type=PatternType.PLACE_TIME_NOUN, category="noun"),
            PatternTemplate(template="فِعَال", pattern_type=PatternType.VERBAL_NOUN, category="noun"),
            PatternTemplate(template="فَعِيل", pattern_type=PatternType.INTENSIVE, category="noun"),
            PatternTemplate(template="أَفْعَل", pattern_type=PatternType.ELATIVE, category="noun"),
            PatternTemplate(template="فَاعِلُون", pattern_type=PatternType.SOUND_MASCULINE_PLURAL, category="plural"),
            PatternTemplate(template="فَاعِلِين", pattern_type=PatternType.SOUND_MASCULINE_PLURAL, category="plural"),
            PatternTemplate(template="فَاعِلَات", pattern_type=PatternType.SOUND_FEMININE_PLURAL, category="plural"),
            PatternTemplate(template="فُعُول", pattern_type=PatternType.BROKEN_PLURAL_FUUL, category="plural"),
            PatternTemplate(template="فِعَال", pattern_type=PatternType.BROKEN_PLURAL_FIAAL, category="plural"),
            PatternTemplate(template="أَفْعَال", pattern_type=PatternType.BROKEN_PLURAL_AFAAL, category="plural"),
            PatternTemplate(template="فِعَل", pattern_type=PatternType.BROKEN_PLURAL_FIUL, category="plural"),
            # High-impact broken plurals (Qur'anic frequent)
            PatternTemplate(template="فُعَّل", pattern_type=PatternType.BROKEN_PLURAL_FU33AL, category="plural"),
            PatternTemplate(template="فُعَلَاء", pattern_type=PatternType.BROKEN_PLURAL_FU3ALAA, category="plural"),
            PatternTemplate(template="فُعَلَاءُ", pattern_type=PatternType.BROKEN_PLURAL_FU3ALAA, category="plural"),
        ]
        extra_patterns = AwzanPatternLoader.load()
        seen_templates = {unicodedata.normalize('NFC', p.template) for p in base}
        for data in extra_patterns:
            tpl = unicodedata.normalize('NFC', data["template"])
            if tpl in seen_templates:
                continue
            seen_templates.add(unicodedata.normalize('NFC', tpl))
            base.append(
                PatternTemplate(
                    template=tpl,
                    pattern_type=data["pattern_type"],
                    category=data["category"],
                    form=data["form"],
                    meaning=data["meaning"],
                    cv_simple=data["cv_simple"],
                    cv_detailed=data["cv_detailed"],
                    cv_advanced=data["cv_advanced"],
                    notes=data["notes"],
                )
            )
        self.patterns.extend(base)
        self._by_category = {}
        for p in base:
            self._by_category.setdefault(p.category, []).append(p)

    def get_all(self) -> List[PatternTemplate]:
        return self.patterns

    def get_by_category(self, category: str) -> List[PatternTemplate]:
        return self._by_category.get(category, [])


from fvafk.c1.cv_pattern import advanced_cv_pattern
from fvafk.c1.cv_pattern import cv_pattern


class PatternMatcher:
    def __init__(self, database: Optional[PatternDatabase] = None) -> None:
        self.database = database or PatternDatabase()

    def match(self, word: str, root: Root) -> Optional[Pattern]:
        if not word or not root:
            return None
        # NFC-normalize so combining diacritics are in canonical order.
        word = unicodedata.normalize("NFC", word)
        # IMPORTANT (per awzan_test_report): compute CV from the ORIGINAL word (with tashkeel)
        # not from stripped/normalized stems.
        advanced_cv_word = self._sanitize_cv(advanced_cv_pattern(word))
        simple_cv_word = cv_pattern(word)
        normalized = self._normalize(word)

        best_pattern: Optional[Pattern] = None
        best_confidence: float = -1.0

        def _update_best(tmpl: PatternTemplate, conf: float) -> None:
            nonlocal best_pattern, best_confidence
            if conf > best_confidence:
                best_confidence = conf
                best_pattern = Pattern(
                    name=tmpl.pattern_type.value,
                    template=tmpl.template,
                    pattern_type=tmpl.pattern_type,
                    stem=word,
                    features={**tmpl.feature_map(), "confidence": f"{conf:.2f}"},
                )

        categories = ["verb", "noun", "plural"]
        checked = set()
        best: Optional[Pattern] = None
        best_confidence = -1.0

        def _consider(template: PatternTemplate, confidence: float) -> None:
            nonlocal best, best_confidence
            if confidence > best_confidence:
                best_confidence = confidence
                best = Pattern(
                    name=template.pattern_type.value,
                    template=template.template,
                    pattern_type=template.pattern_type,
                    stem=word,
                    features={**template.feature_map(), "confidence": f"{confidence:.2f}"},
                )

        for category in categories:
            for template in self.database.get_by_category(category):
                if id(template) in checked:
                    continue
                checked.add(id(template))
                if not template.matches_root_type(root):
                    continue
                candidate = self._instantiate_template(template.template, root)
                matched, confidence = self._matches(
                    normalized,
                    candidate,
                    template.pattern_type,
                    advanced_cv_word,
                    template,
                )
                if matched:
                    _consider(template, confidence)
                    if best_confidence >= 1.0:
                        return best
        for template in self.database.get_all():
            if id(template) in checked:
                continue
            if not template.matches_root_type(root):
                continue
            candidate = self._instantiate_template(template.template, root)
            matched, confidence = self._matches(
                normalized,
                candidate,
                template.pattern_type,
                advanced_cv_word,
                template,
            )
            if matched:
                _consider(template, confidence)
                if best_confidence >= 1.0:
                    return best

        if best is not None:
            return best

        # ------------------------------------------------------------------
        # CV-based fallback (golden rule from docs/awzan_test_report.md)
        # ------------------------------------------------------------------
        # If exact template instantiation didn't match (often due to missing diacritics
        # or orthographic variants), fall back to matching by CV / Advanced_CV fields
        # in the awzan database, computed from the original word.
        #
        # This increases coverage; confidence is lower than exact instantiation.
        for template in self.database.get_all():
            # Prefer Advanced_CV when available.
            if template.cv_advanced:
                template_cv_adv = self._sanitize_cv(template.cv_advanced)
                if template_cv_adv and template_cv_adv == advanced_cv_word:
                    _update_best(template, 0.75)
            elif template.cv_simple and template.cv_simple == simple_cv_word:
                _update_best(template, 0.70)

        return best_pattern

    def _normalize(self, word: str) -> str:
        # Canonical Unicode form first so that diacritic ordering is consistent
        # (e.g. shadda+fatha vs fatha+shadda are canonically equivalent).
        text = unicodedata.normalize('NFC', word)
        # Convert Tanwin to standard short vowels
        # This is critical for matching catalog patterns (e.g., matching "كاتبٌ" with "فاعل")
        text = text.replace('ً', 'َ').replace('ٌ', 'ُ').replace('ٍ', 'ِ')
        
        # Remove definiteness (Al-)
        # Strip simple "ال" prefix
        if text.startswith("ال") and len(text) > 3:
             # Find end of "ال" (skip non-letters)
             idx = 2
             while idx < len(text) and text[idx] in "ْ":
                 idx += 1
             
             # Handle Sun letters (Shadda after Al)
             # e.g., "الشَّمْس" -> "شَّمْس" -> we want to match pattern "فَعْل"
             # If next char has shadda, keep it but remove the Al
             # Actually, templates usually don't have the shadda from sun letters
             # So we should probably strip that shadda too if it's a sun letter effect
             
             stem_start = idx
             stem = text[stem_start:]
             
             # If the first letter of the stem has a shadda, it might be a sun letter assimilation
             # We should remove the shadda to recover the underlying form for pattern matching
             # e.g. "الشَّمْس" -> "شَمْس" (to match fa3l)
             if len(stem) > 1 and stem[1] == 'ّ':
                 # Remove shadda
                 stem = stem[0] + stem[2:]
                 
             text = stem

        Unlike :meth:`match`, which returns the *first* match found, this
        method evaluates every template and returns the one with the highest
        confidence score.  This avoids situations where an earlier-checked
        category (e.g. verb) wins over a later one (e.g. noun/participle) even
        though the noun template is a better fit for the surface form.
        """
        if not word or not root:
            return None
        advanced_cv_word = self._sanitize_cv(advanced_cv_pattern(word))
        normalized = self._normalize(word)

        best_pattern: Optional[Pattern] = None
        best_confidence: float = -1.0

        for template in self.database.get_all():
            if not template.matches_root_type(root):
                continue
            candidate = self._instantiate_template(template.template, root)
            matched, confidence = self._matches(
                normalized, candidate, template.pattern_type,
                advanced_cv_word, template,
            )
            if matched and confidence > best_confidence:
                best_confidence = confidence
                best_pattern = Pattern(
                    name=template.pattern_type.value,
                    template=template.template,
                    pattern_type=template.pattern_type,
                    stem=word,
                    features={**template.feature_map(), "confidence": f"{confidence:.2f}"},
                )

        return best_pattern

    def _normalize(self, word: str) -> str:
        text = unicodedata.normalize('NFC', word)
        text = text.replace('ً', '').replace('ٌ', '').replace('ٍ', '')
        # If the surface had fathatan, Arabic orthography often adds a final alif (…ًا).
        # After stripping marks, drop this support-alif to match templates (e.g., عظيمًا -> عظيم).
        if "\u064b" in word and text.endswith("ا") and len(text) > 3:
            text = text[:-1]
        text = text.replace('أ', 'ا').replace('إ', 'ا').replace('آ', 'ا')
        text = text.replace('ى', 'ي')
        return text.strip()

    def _instantiate_template(self, template_str: str, root: Root) -> str:
        # Apply NFC normalization to template for consistent diacritic ordering
        template_str = unicodedata.normalize('NFC', template_str)
        chars = []
        l_count = 0
        for ch in unicodedata.normalize('NFC', template_str):
            if ch == 'ف':
                chars.append(root.letters[0])
            elif ch == 'ع':
                chars.append(root.letters[1])
            elif ch == 'ل':
                if l_count == 0:
                    idx = 2
                else:
                    idx = min(3, len(root.letters) - 1)
                chars.append(root.letters[idx])
                l_count += 1
            else:
                chars.append(ch)
        return unicodedata.normalize('NFC', ''.join(chars))

    def _matches(
        self,
        word: str,
        candidate: str,
        pattern_type: PatternType,
        advanced_cv_word: str,
        template: PatternTemplate,
    ) -> Tuple[bool, float]:
        word = unicodedata.normalize('NFC', word)
        candidate = unicodedata.normalize('NFC', candidate)
        if word == candidate:
            return True, 1.0
        
        stripped_word = self._strip_diacritics(word)
        stripped_candidate = self._strip_diacritics(candidate)
        
        # Check broken plural fu'ul BEFORE the consonant guard, because the
        # و in فُعُول is a pattern vowel (not a root letter) and makes
        # stripped_candidate longer than stripped_word.
        if pattern_type == PatternType.BROKEN_PLURAL_FUUL:
            candidate_no_waw = candidate.replace("و", "")
            stripped_candidate_no_waw = self._strip_diacritics(candidate_no_waw)
            if stripped_word == stripped_candidate_no_waw:
                return True, 0.85

        # If consonants don't match, fail immediately
        if stripped_word != stripped_candidate:
            return False, 0.0
        
        # If consonants don't match, fail immediately
        if stripped_word != stripped_candidate:
            return False, 0.0
        
        # If consonants don't match, fail immediately
        if stripped_word != stripped_candidate:
            return False, 0.0
        
        # Check CV pattern if available
        if template.cv_advanced:
            template_cv = self._sanitize_cv(template.cv_advanced)
            if template_cv and (not advanced_cv_word or advanced_cv_word != template_cv):
                return False, 0.0
        
        # Check shadda match (Crucial from gate matcher)
        # If candidate has shadda, word MUST have shadda
        if 'ّ' in candidate and 'ّ' not in word:
             return False, 0.0
             
        # If candidate has no shadda (and is not placeholder-heavy), word should not have shadda?
        # In gate matcher: if p_sh and not w_sh -> Fail. if not p_sh and w_sh -> Fail (unless placeholder).
        # Here candidate is instantiated, so placeholders are filled.
        # But root letters might have shadda natively? No, usually pattern dictates shadda.
        if 'ّ' not in candidate and 'ّ' in word:
             return False, 0.0

        # Lenient match: ignore final short vowel differences
        # e.g. "كَاتِبُ" vs "كَاتِب"
        def strip_final_vowel(s):
            if s and s[-1] in "َُِ":
                return s[:-1]
            return s
            
        if strip_final_vowel(word) == strip_final_vowel(candidate):
            return True, 0.95
            
        # If lengths match (and stripped text matches), good enough
        if len(word) == len(candidate):
            return True, 0.90
            
        if pattern_type == PatternType.FORM_X:
            return True, 0.9
            
        # If we got here, stripped text matches but full text doesn't
        # Likely a vowel mismatch. Return a lower confidence match
        return True, 0.60

    @staticmethod
    def _sanitize_cv(value: str) -> str:
        return "".join(ch for ch in value if ch.isalpha())

    def _strip_diacritics(self, text: str) -> str:
        diacritics = "َُِْٰٓٔٱ" + "ًٌٍ"
        had_fathatan = "\u064b" in text
        for d in diacritics:
            text = text.replace(d, '')
        # Normalize hamza carriers to bare alif for robust matching (e.g., أخرج vs افعل).
        text = (
            text.replace("أ", "ا")
            .replace("إ", "ا")
            .replace("آ", "ا")
        )
        text = re.sub(r'[\u064B-\u0650\u0652-\u065F\u0670]', '', text)
        if had_fathatan and text.endswith("ا") and len(text) > 3:
            text = text[:-1]
        return text
