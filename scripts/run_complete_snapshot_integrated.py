#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Complete Pipeline Snapshot - Integrated Version
Combines operators, CV patterns, roots, mabniyat, and wazn matching.
"""

import argparse
import json
import sys
import csv
import unicodedata
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass
from collections import Counter

# Arabic diacritics constants
FATHATAN = "\u064B"
DAMMATAN = "\u064C"
KASRATAN = "\u064D"
FATHA = "\u064E"
DAMMA = "\u064F"
KASRA = "\u0650"
SHADDA = "\u0651"
SUKUN = "\u0652"
DAGGER_ALIF = "\u0670"
ALIF_WASLA = "\u0671"

TANWIN = {FATHATAN, DAMMATAN, KASRATAN}
VOWELS = {FATHA, DAMMA, KASRA, SUKUN}
DIACRITICS = set().union(TANWIN, VOWELS, {SHADDA, DAGGER_ALIF})
PLACEHOLDERS = {"ف", "ع", "ل"}

# Configuration
REQUIRE_FAL_ORDER_IN_PATTERN = True
MIN_PATTERN_UNITS = 3
SUBSTRING_MATCHING = True
ALLOW_MISSING_WORD_VOWELS = True
IGNORE_LAST_VOWEL = False
IGNORE_TANWIN = False

# Test text (Ayat al-Dayn)
AYAT_AL_DAYN = (
    "يَا أَيُّهَا الَّذِينَ آمَنُوا إِذَا تَدَايَنتُم بِدَيْنٍ إِلَى أَجَلٍ مُّسَمًّى فَاكْتُبُوهُ وَلْيَكْتُب بَّيْنَكُمْ كَاتِبٌ بِالْعَدْلِ وَلَا يَأْبَ كَاتِبٌ أَن يَكْتُبَ كَمَا عَلَّمَهُ اللَّهُ فَلْيَكْتُبْ وَلْيُمْلِلِ الَّذِي عَلَيْهِ الْحَقُّ وَلْيَتَّقِ اللَّهَ رَبَّهُ وَلَا يَبْخَسْ مِنْهُ شَيْئاً فَإِن كَانَ الَّذِي عَلَيْهِ الْحَقُّ سَفِيهاً أَوْ ضَعِيفاً أَوْ لَا يَسْتَطِيعُ أَن يُمِلَّ هُوَ فَلْيُمْلِلْ وَلِيُّهُ بِالْعَدْلِ وَاسْتَشْهِدُوا شَهِيدَيْنِ مِن رِّجَالِكُمْ فَإِن لَّمْ يَكُونَا رَجُلَيْنِ فَرَجُلٌ وَامْرَأَتَانِ مِمَّن تَرْضَوْنَ مِنَ الشُّهَدَاءِ أَن تَضِلَّ إِحْدَاهُمَا فَتُذَكِّرَ إِحْدَاهُمَا الْأُخْرَى وَلَا يَأْبَ الشُّهَدَاءُ إِذَا مَا دُعُوا وَلَا تَسْأَمُوا أَن تَكْتُبُوهُ صَغِيراً أَوْ كَبِيراً إِلَى أَجَلِهِ ذَلِكُمْ أَقْسَطُ عِندَ اللَّهِ وَأَقْوَمُ لِلشَّهَادَةِ وَأَدْنَى أَلَّا تَرْتَابُوا إِلَّا أَن تَكُونَ تِجَارَةً حَاضِرَةً تُدِيرُونَهَا بَيْنَكُمْ فَلَيْسَ عَلَيْكُمْ جُنَاحٌ أَلَّا تَكْتُبُوهَا وَأَشْهِدُوا إِذَا تَبَايَعْتُمْ وَلَا يُضَارَّ كَاتِبٌ وَلَا شَهِيدٌ وَإِن تَفْعَلُوا فَإِنَّهُ فُسُوقٌ بِكُمْ وَاتَّقُوا اللَّهَ وَيُعَلِّمُكُمُ اللَّهُ وَاللَّهُ بِكُلِّ شَيْءٍ عَلِيمٌ"
)


@dataclass(frozen=True)
class Unit:
    """Represents a base letter + diacritics unit."""
    base: str
    diacs: Tuple[str, ...]


@dataclass
class MatchHit:
    """Represents a wazn pattern match."""
    pattern: str
    reason: str  # FULLMATCH or WINDOW
    window_start: int
    score_key: Tuple[int, int, int, int]


def _sorted_tuple(s):
    """Convert set to sorted tuple for deterministic comparison."""
    return tuple(sorted(s))

def remove_al_and_shadda(word: str) -> str:
    """Remove 'ال' definiteness and following shadda from word."""
    if word.startswith('ال'):
        remaining = word[2:]
        chars = list(remaining)
        if len(chars) >= 2:
            for i in range(1, min(3, len(chars))):
                if chars[i] == SHADDA:
                    new_chars = chars[:i] + chars[i+1:]
                    remaining = ''.join(new_chars)
                    break
        return remaining
    return word


def split_units(text: str) -> List[Unit]:
    """Split Arabic text into (base_letter + diacritics) units."""
    units: List[Unit] = []
    cur_base: Optional[str] = None
    cur_diacs = []

    for ch in text:
        if ch in DIACRITICS:
            if cur_base is None:
                continue
            cur_diacs.append(ch)
        else:
            if cur_base is not None:
                units.append(Unit(cur_base, _sorted_tuple(cur_diacs)))
            cur_base = ch
            cur_diacs = []

    if cur_base is not None:
        units.append(Unit(cur_base, _sorted_tuple(cur_diacs)))

    return units

def expand_shadda(units: List[Unit]) -> List[Unit]:
    """Expand shadda into two consonants."""
    expanded = []
    for unit in units:
        if SHADDA in unit.diacs:
            second_marks = [m for m in unit.diacs if m != SHADDA]
            expanded.append(Unit(unit.base, (SUKUN,)))
            expanded.append(Unit(unit.base, _sorted_tuple(second_marks)))
        else:
            expanded.append(unit)
    return expanded

def has_fal_order_in_pattern(pattern: str) -> bool:
    """Check if pattern contains ف then ع then ل in order."""
    bases = [u.base for u in split_units(pattern)]
    try:
        i_f = bases.index("ف")
        i_a = bases.index("ع", i_f + 1)
        i_l = bases.index("ل", i_a + 1)
        return True
    except ValueError:
        return False

def pattern_effective_len(units: List[Unit]) -> int:
    """Calculate effective length including shadda complexity."""
    shadda_count = sum(1 for u in units if SHADDA in u.diacs)
    return len(units) + shadda_count

def count_fixed_letters(units: List[Unit]) -> int:
    """Count non-placeholder letters."""
    return sum(1 for u in units if u.base not in PLACEHOLDERS)

def count_specified_diacritics(units: List[Unit]) -> int:
    """Count specified vowels, tanwin, and shadda."""
    c = 0
    for u in units:
        for d in u.diacs:
            if d in VOWELS or d in TANWIN or d == SHADDA:
                c += 1
    return c

def unit_vowel(diacs: Tuple[str, ...]) -> Optional[str]:
    """Extract vowel from diacritics."""
    for d in diacs:
        if d in VOWELS:
            return d
    return None

def unit_tanwin(diacs: Tuple[str, ...]) -> Optional[str]:
    """Extract tanwin from diacritics."""
    for d in diacs:
        if d in TANWIN:
            return d
    return None

def unit_has_shadda(diacs: Tuple[str, ...]) -> bool:
    """Check if unit has shadda."""
    return SHADDA in diacs

def normalize_units_for_options(units: List[Unit], ignore_last_vowel: bool, ignore_tanwin: bool) -> List[Unit]:
    """Normalize units according to options."""
    if not units:
        return units
    out = []
    for idx, u in enumerate(units):
        diacs = set(u.diacs)
        if ignore_tanwin:
            diacs -= TANWIN
        if ignore_last_vowel and idx == len(units) - 1:
            diacs -= VOWELS
            diacs -= TANWIN
        out.append(Unit(u.base, _sorted_tuple(diacs)))
    return out

def units_match(p: Unit, w: Unit, allow_missing_word_vowels: bool) -> bool:
    """Check if pattern unit matches word unit."""
    # Base letter matching
    if p.base in PLACEHOLDERS:
        base_ok = True
    else:
        base_ok = (p.base == w.base)
    if not base_ok:
        return False

    # Shadda matching
    p_sh = unit_has_shadda(p.diacs)
    w_sh = unit_has_shadda(w.diacs)

    if p_sh and not w_sh:
        return False
    elif not p_sh and w_sh and p.base not in PLACEHOLDERS:
        return False

    # Vowel matching
    pv = unit_vowel(p.diacs)
    wv = unit_vowel(w.diacs)
    if pv is not None:
        if wv is None and allow_missing_word_vowels:
            pass
        else:
            if pv != wv:
                return False

    # Tanwin matching
    pt = unit_tanwin(p.diacs)
    wt = unit_tanwin(w.diacs)
    if pt is not None:
        if wt is None and allow_missing_word_vowels:
            pass
        else:
            if pt != wt:
                return False

    return True

def try_match_pattern_to_word(pattern: str, word: str) -> List[MatchHit]:
    """Try to match a wazn pattern to a word."""
    word_processed = remove_al_and_shadda(word)

    p_units = split_units(pattern)
    w_units = split_units(word_processed)

    p_units = normalize_units_for_options(p_units, IGNORE_LAST_VOWEL, IGNORE_TANWIN)
    w_units = normalize_units_for_options(w_units, IGNORE_LAST_VOWEL, IGNORE_TANWIN)

    if len(p_units) < MIN_PATTERN_UNITS:
        return []
    if REQUIRE_FAL_ORDER_IN_PATTERN and not has_fal_order_in_pattern(pattern):
        return []

    lp = len(p_units)
    lw = len(w_units)

    fixed = count_fixed_letters(p_units)
    diac_spec = count_specified_diacritics(p_units)
    eff_len = pattern_effective_len(p_units)

    def make_score(reason: str) -> Tuple[int, int, int, int]:
        reason_rank = 10 if reason == "FULLMATCH" else 1
        return (reason_rank, eff_len, fixed, diac_spec)

    if lp > lw:
        return []

    # Full match
    if lp == lw:
        ok = True
        for i in range(lp):
            if not units_match(p_units[i], w_units[i], ALLOW_MISSING_WORD_VOWELS):
                ok = False
                break
        if ok:
            return [MatchHit(pattern, "FULLMATCH", 0, make_score("FULLMATCH"))]
        return []

    # Window matching
    if not SUBSTRING_MATCHING:
        return []

    best_start = None
    for start in range(0, lw - lp + 1):
        ok = True
        for i in range(lp):
            if not units_match(p_units[i], w_units[start + i], ALLOW_MISSING_WORD_VOWELS):
                ok = False
                break
        if ok:
            best_start = start
            break

    if best_start is None:
        return []

    return [MatchHit(pattern, "WINDOW", best_start, make_score("WINDOW"))]

def best_hit(hits: List[MatchHit]) -> Optional[MatchHit]:
    """Select best match from hits."""
    if not hits:
        return None
    hits_sorted = sorted(
        hits,
        key=lambda h: (h.score_key, len(h.pattern), h.pattern),
        reverse=True
    )
    return hits_sorted[0]

def detect_cv_pattern_integrated(word: str) -> Dict[str, Any]:
    """Detect CV pattern using integrated unit-based approach."""
    units = split_units(word)
    units = expand_shadda(units)

    pattern = []
    i = 0

    # Handle initial hamza
    if units and units[0].base in {ALIF_WASLA, "أ", "إ", "آ"}:
        pattern.extend(["C", "V"])
        units = units[1:]

    # Process remaining units
    prev_marks = []
    for unit in units:
        if not unit.base.isalpha():
            prev_marks = unit.diacs
            continue

        # Check for madd
        is_madd = False
        if unit.base == "ا":
            is_madd = any(m in {FATHA, FATHATAN} for m in prev_marks)
        elif unit.base == "و":
            is_madd = any(m in {DAMMA, DAMMATAN} for m in prev_marks)
        elif unit.base in {"ي", "ى"}:
            is_madd = any(m in {KASRA, KASRATAN} for m in prev_marks)
        elif unit.base == "آ":
            pattern.append("C")
            is_madd = False

        if is_madd:
            pattern.append("V")
        else:
            pattern.append("C")
            if any(m in VOWELS or m in TANWIN for m in unit.diacs):
                pattern.append("V")

        prev_marks = unit.diacs

    pattern_str = ''.join(pattern)

    # Classify pattern type
    pattern_type = None
    if pattern_str == 'CVCVC':
        pattern_type = 'faʕal (فَعَل)'
    elif pattern_str == 'CVCCVC':
        pattern_type = 'faʕʕal (فَعَّل)'
    elif pattern_str == 'CVCVVC':
        pattern_type = 'faʕaal (فَعَال)'
    elif pattern_str == 'CVCVVCVC':
        pattern_type = 'faʕaalah (فَعَالَة)'
    elif pattern_str == 'CVCCVVC':
        pattern_type = 'mafʕuul (مَفْعُول)'
    elif pattern_str == 'CVCVCCVC':
        pattern_type = 'mufaʕʕil (مُفَعِّل)'

    # Check CV law
    follows_cv_law = True
    if len(pattern_str) < 2 or pattern_str[0] != "C" or pattern_str[1] != "V":
        follows_cv_law = False

    return {
        "pattern": pattern_str,
        "pattern_type": pattern_type,
        "length": len(pattern),
        "consonant_count": pattern.count('C'),
        "vowel_count": pattern.count('V'),
        "follows_cv_law": follows_cv_law,
    }

def load_operators_catalog(verbose: bool = False) -> Dict[str, Dict[str, Any]]:
    """Load operators catalog from CSV file."""
    catalog_path = Path("data/operators_catalog_split.csv")

    if not catalog_path.exists():
        if verbose:
            print(f"Warning: Operators catalog not found at {catalog_path}", file=sys.stderr)
        return {}

    operators = {}

    try:
        with open(catalog_path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                operator = row['Operator'].strip()
                operators[operator] = {
                    "group_number": row['Group Number'],
                    "arabic_group": row['Arabic Group Name'],
                    "english_group": row['English Group Name'],
                    "purpose": row['Purpose/Usage'],
                    "example": row['Example'],
                    "note": row['Note'],
                }

        if verbose:
            print(f"Loaded {len(operators)} operators from catalog", file=sys.stderr)

    except Exception as e:
        if verbose:
            print(f"Error loading operators catalog: {e}", file=sys.stderr)
        return {}

    return operators

def load_mabniyat_catalog(verbose: bool = False) -> Dict[str, Dict[str, Any]]:
    """Load Mabniyat (indeclinable nouns/particles) from data/arabic_json/2."""
    catalog_path = Path("data/arabic_json/2")
    mabniyat = {}

    if not catalog_path.exists():
        if verbose:
            print(f"Warning: Mabniyat catalog path not found at {catalog_path}", file=sys.stderr)
        return {}

    count = 0
    try:
        for json_file in catalog_path.rglob("*.json"):
            try:
                with open(json_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)

                if isinstance(data, list):
                    items = data
                else:
                    items = [data]

                for item in items:
                    if not isinstance(item, dict):
                        continue

                    word = item.get("الأداة")
                    if not word:
                        continue

                    clean_word = ''.join(c for c in word if c not in 'ًٌٍَُِّْٰ')
                    forms = [f.strip() for f in clean_word.split('/')]

                    for form in forms:
                        if form:
                            mabniyat[form] = item
                            count += 1

            except Exception as e:
                if verbose:
                    print(f"Error loading {json_file}: {e}", file=sys.stderr)

        if verbose:
            print(f"Loaded {count} Mabniyat entries", file=sys.stderr)

    except Exception as e:
        if verbose:
            print(f"Error walking mabniyat catalog: {e}", file=sys.stderr)

    return mabniyat

def sniff_delimiter(path: str) -> str:
    """Detect CSV delimiter."""
    with open(path, "r", encoding="utf-8", newline="") as f:
        sample = f.read(4096)
    try:
        dialect = csv.Sniffer().sniff(sample, delimiters=[",", "\t", ";", "|"])
        return dialect.delimiter
    except Exception:
        if "\t" in sample.splitlines()[0] if sample.splitlines() else "":
            return "\t"
        return ","

def load_wazn_patterns(verbose: bool = False) -> List[str]:
    """Load wazn patterns from CSV."""
    patterns_path = Path("data/awzan-claude-atwah.csv")

    if not patterns_path.exists():
        if verbose:
            print(f"Warning: Wazn patterns not found at {patterns_path}", file=sys.stderr)
        return []

    patterns = []
    try:
        delim = sniff_delimiter(str(patterns_path))
        with open(patterns_path, 'r', encoding='utf-8', newline='') as f:
            reader = csv.DictReader(f, delimiter=delim)
            for row in reader:
                # Try different possible column names
                pattern = row.get('الوزن') or row.get('wazn') or row.get('pattern') or row.get('Pattern')
                if pattern and pattern.strip():
                    patterns.append(pattern.strip())

        # Deduplicate
        seen = set()
        unique_patterns = []
        for p in patterns:
            if p not in seen:
                seen.add(p)
                unique_patterns.append(p)

        if verbose:
            print(f"Loaded {len(unique_patterns)} wazn patterns", file=sys.stderr)

        return unique_patterns

    except Exception as e:
        if verbose:
            print(f"Error loading wazn patterns: {e}", file=sys.stderr)
        return []

def extract_root(word: str, mabniyat_catalog: Optional[Dict[str, Dict[str, Any]]] = None) -> Dict[str, Any]:
    """Extract tri-literal root from Arabic word."""
    clean = ''.join(c for c in word if c not in 'ًٌٍَُِّْٰ')
    original_clean = clean

    # Check Mabniyat Catalog first
    if mabniyat_catalog and clean in mabniyat_catalog:
        mabniyat_info = mabniyat_catalog[clean]
        return {
            "original_word": word,
            "cleaned": original_clean,
            "stem": clean,
            "root_trilateral": None,
            "root_quadrilateral": None,
            "root_type": "mabni",
            "confidence": 1.0,
            "consonants_extracted": 0,
            "method": "knowledge_base_lookup",
            "mabniyat_info": {
                "type": mabniyat_info.get("النوع"),
                "grammatical_case": mabniyat_info.get("الحالة النحوية"),
                "number": mabniyat_info.get("العدد"),
                "gender": mabniyat_info.get("الجنس") or mabniyat_info.get("الجنس "),
            }
        }

    # Remove prefixes
    prefixes = ["ال", "وال", "فال", "بال", "كال", "لل", "و", "ف", "ب", "ل", "ك", "س", "ت", "ي", "ن", "أ"]
    for prefix in prefixes:
        if clean.startswith(prefix) and len(clean) > len(prefix) + 2:
            clean = clean[len(prefix):]
            break

    # Remove suffixes
    suffixes = ["ونه", "وها", "هما", "كما", "كن", "هم", "هن", "نا", "ني", "وا", "ون", "ين", "ان", "تان", "تين", "ة", "ه", "ها", "ت", "ك", "ي"]
    for suffix in suffixes:
        if clean.endswith(suffix) and len(clean) > len(suffix) + 2:
            clean = clean[:-len(suffix)]
            break

    # Extract consonantal root
    consonants = []
    weak_letters = set("اوىيءآأإؤئ")

    for char in clean:
        if char.isalpha() and char not in "ـ":
            if len(consonants) > 0 and char in weak_letters:
                continue
            consonants.append(char)

    if len(consonants) >= 3:
        root_3 = ''.join(consonants[:3])
        root_4 = ''.join(consonants[:4]) if len(consonants) >= 4 else None
        confidence = 0.7 if len(consonants) == 3 else 0.6
    elif len(consonants) == 2:
        root_3 = ''.join(consonants)
        root_4 = None
        confidence = 0.3
    else:
        root_3 = None
        root_4 = None
        confidence = 0.0

    return {
        "original_word": word,
        "cleaned": original_clean,
        "stem": clean,
        "root_trilateral": root_3,
        "root_quadrilateral": root_4,
        "root_type": "trilateral" if root_3 and len(root_3) == 3 else "quadrilateral" if root_4 else "unknown",
        "confidence": confidence,
        "consonants_extracted": len(consonants),
        "method": "morphological_stripping",
    }

def detect_operator(word: str, operators_catalog: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
    """Detect Arabic operator (particle/verb) using catalog."""
    clean_word = ''.join(c for c in word if c not in 'ًٌٍَُِّْٰ')

    # Direct match
    if clean_word in operators_catalog:
        return {
            "is_operator": True,
            "operator": clean_word,
            "original_word": word,
            **operators_catalog[clean_word],
        }

    # Check for prefixed operators
    prefixes = ["و", "ف", "ب", "ل", "ك"]
    for prefix in prefixes:
        if clean_word.startswith(prefix) and len(clean_word) > 1:
            stem = clean_word[1:]
            if stem in operators_catalog:
                return {
                    "is_operator": False,
                    "has_operator_prefix": True,
                    "prefix": prefix,
                    "prefix_operator": operators_catalog.get(prefix, {}),
                    "stem": stem,
                    "stem_operator": operators_catalog.get(stem, {}),
                    "original_word": word,
                }

    return {
        "is_operator": False,
        "has_operator_prefix": False,
        "original_word": word,
    }

def analyze_word(word: str, operators_catalog: Dict, mabniyat_catalog: Dict, wazn_patterns: List[str]) -> Dict[str, Any]:
    """Perform complete analysis on a single word."""
    # Operator analysis
    operator_analysis = detect_operator(word, operators_catalog)

    # CV pattern
    cv_pattern = detect_cv_pattern_integrated(word)

    # Root extraction
    root_extraction = extract_root(word, mabniyat_catalog)

    # Wazn matching
    wazn_matches = []
    all_hits = []
    for pattern in wazn_patterns:
        hits = try_match_pattern_to_word(pattern, word)
        if hits:
            all_hits.extend(hits)

    if all_hits:
        # Sort and take top matches
        all_hits.sort(key=lambda h: (h.score_key, len(h.pattern), h.pattern), reverse=True)
        for hit in all_hits[:3]:  # Top 3 matches
            wazn_matches.append({
                "pattern": hit.pattern,
                "match_type": hit.reason,
                "window_start": hit.window_start,
                "score": list(hit.score_key),
            })

    return {
        "word": word,
        "operator_analysis": operator_analysis,
        "cv_pattern": cv_pattern,
        "root_extraction": root_extraction,
        "wazn_matches": wazn_matches,
    }

def compute_statistics(word_analyses: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Compute statistics from word analyses."""
    total_words = len(word_analyses)

    # Operator stats (include prefixed operators)
    operators_detected = sum(
        1 for w in word_analyses
        if w["operator_analysis"]["is_operator"] or w["operator_analysis"].get("has_operator_prefix")
    )

    # Root stats
    roots_extracted = sum(1 for w in word_analyses if w["root_extraction"]["root_trilateral"])
    trilateral_roots = sum(1 for w in word_analyses if w["root_extraction"]["root_type"] == "trilateral")
    quadrilateral_roots = sum(1 for w in word_analyses if w["root_extraction"]["root_type"] == "quadrilateral")
    mabniyat = sum(1 for w in word_analyses if w["root_extraction"]["root_type"] == "mabni")

    # CV pattern stats
    patterns_classified = sum(1 for w in word_analyses if w["cv_pattern"]["pattern_type"])
    patterns_valid = sum(1 for w in word_analyses if w["cv_pattern"]["follows_cv_law"])

    # Wazn matching stats
    total_matches = sum(len(w["wazn_matches"]) for w in word_analyses)
    full_matches = sum(1 for w in word_analyses for m in w["wazn_matches"] if m["match_type"] == "FULLMATCH")
    window_matches = sum(1 for w in word_analyses for m in w["wazn_matches"] if m["match_type"] == "WINDOW")

    return {
        "total_words": total_words,
        "operators": {
            "total_detected": operators_detected,
        },
        "roots": {
            "total_extracted": roots_extracted,
            "trilateral": trilateral_roots,
            "quadrilateral": quadrilateral_roots,
            "mabniyat": mabniyat,
        },
        "cv_patterns": {
            "classified": patterns_classified,
            "valid": patterns_valid,
        },
        "wazn_matches": {
            "total": total_matches,
            "full_matches": full_matches,
            "window_matches": window_matches,
        }
    }

def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("snapshot_out.json"),
        help="Output JSON file (default: snapshot_out.json)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print verbose output to stderr",
    )
    parser.add_argument(
        "--text",
        type=str,
        default=AYAT_AL_DAYN,
        help="Custom text to process (default: Ayat al-Dayn)",
    )
    args = parser.parse_args()

    try:
        if args.verbose:
            print("=" * 80, file=sys.stderr)
            print("COMPLETE PIPELINE - Enhanced Integration", file=sys.stderr)
            print("=" * 80, file=sys.stderr)

        # Load catalogs
        operators_catalog = load_operators_catalog(args.verbose)
        mabniyat_catalog = load_mabniyat_catalog(args.verbose)
        wazn_patterns = load_wazn_patterns(args.verbose)

        # Tokenize
        words = args.text.split()

        if args.verbose:
            print(f"\nTokenized into {len(words)} words", file=sys.stderr)

        # Analyze all words
        word_analyses = []
        for word in words:
            analysis = analyze_word(word, operators_catalog, mabniyat_catalog, wazn_patterns)
            word_analyses.append(analysis)

        # Compute statistics
        statistics = compute_statistics(word_analyses)

        if args.verbose:
            print(f"\n=== ENHANCED ANALYSIS ===", file=sys.stderr)
            print(f"Operators: {statistics['operators']['total_detected']}/{statistics['total_words']} ({statistics['operators']['total_detected']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"Roots: {statistics['roots']['total_extracted']}/{statistics['total_words']} ({statistics['roots']['total_extracted']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"Mabniyat: {statistics['roots']['mabniyat']}/{statistics['total_words']} ({statistics['roots']['mabniyat']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"CV Patterns (classified): {statistics['cv_patterns']['classified']}/{statistics['total_words']} ({statistics['cv_patterns']['classified']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"CV Patterns (valid): {statistics['cv_patterns']['valid']}/{statistics['total_words']} ({statistics['cv_patterns']['valid']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"Wazn Matches: {statistics['wazn_matches']['total']}/{statistics['total_words']} ({statistics['wazn_matches']['total']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  - Full matches: {statistics['wazn_matches']['full_matches']}", file=sys.stderr)
            print(f"  - Window matches: {statistics['wazn_matches']['window_matches']}", file=sys.stderr)

        # Build output
        result = {
            "metadata": {
                "title": "Complete Pipeline - Enhanced Integration",
                "source": "آية الدين (Al-Baqarah 2:282)",
                "pipeline_version": "3.0.0",
                "features": ["operators", "cv_patterns", "roots", "mabniyat", "wazn_matching"],
                "catalogs_loaded": {
                    "operators": len(operators_catalog),
                    "mabniyat": len(set(mabniyat_catalog.keys())),
                    "wazn_patterns": len(wazn_patterns),
                }
            },
            "statistics": statistics,
            "word_analysis": word_analyses,
        }

        # Write output
        with open(args.output, "w", encoding="utf-8") as f:
            json.dump(result, f, ensure_ascii=False, indent=2)

        if args.verbose:
            print("\n" + "=" * 80, file=sys.stderr)
            print("✅ PIPELINE COMPLETE", file=sys.stderr)
            print("=" * 80, file=sys.stderr)
            print(f"\n📊 Summary:", file=sys.stderr)
            print(f"  Total words: {statistics['total_words']}", file=sys.stderr)
            print(f"  Operators: {statistics['operators']['total_detected']} ({statistics['operators']['total_detected']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  Roots: {statistics['roots']['total_extracted']} ({statistics['roots']['total_extracted']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  Mabniyat: {statistics['roots']['mabniyat']} ({statistics['roots']['mabniyat']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  CV Patterns (classified): {statistics['cv_patterns']['classified']} ({statistics['cv_patterns']['classified']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  CV Patterns (valid): {statistics['cv_patterns']['valid']} ({statistics['cv_patterns']['valid']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print(f"  Wazn Matches: {statistics['wazn_matches']['total']} ({statistics['wazn_matches']['total']/statistics['total_words']*100:.1f}%)", file=sys.stderr)
            print("\n" + "=" * 80, file=sys.stderr)

        print(f"Wrote {args.output}", file=sys.stderr)
        return 0

    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
