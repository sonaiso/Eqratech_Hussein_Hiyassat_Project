# -*- coding: utf-8 -*-
"""
MorphEnricher: takes word + c2b output and adds deep morphological features.
Fills verb features (tense, voice, person, number, gender) and noun pattern_type.
"""
from __future__ import annotations

import unicodedata
from typing import Any, Dict, Optional

from .models import EnrichmentResult, NounFeatures, VerbFeatures
from .noun_analyzer import analyze_noun
from .verb_analyzer import analyze_verb
from .i3rab_generator import generate_i3rab, WordInfo, WordType, Function, Case, Number, Gender


def _bare(s: str) -> str:
    """Remove diacritics (tashkeel) from string."""
    return "".join(
        c for c in (s or "")
        if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)
    ).replace("-", "").strip()


def _root_letters(root: str) -> str:
    """Normalize root to letters only (no dashes)."""
    if not root:
        return ""
    return "".join(c for c in root if "\u0621" <= c <= "\u064A").strip()


def _is_valid_root(root: str) -> bool:
    r = _root_letters(root)
    return len(r) in (3, 4) and all("\u0621" <= c <= "\u064A" for c in r)


# Words that have no root (جامد) — same as resolver for consistency
_NO_ROOT_WORDS_BARE = frozenset({
    "الله", "اللهم", "لله",
    "يأيها", "ياايها",
})


def _is_jalala_or_no_root_bare(bare_word: str) -> bool:
    if not bare_word:
        return False
    if bare_word in _NO_ROOT_WORDS_BARE:
        return True
    for suf in ("الله", "لله"):
        if bare_word.endswith(suf) and len(bare_word) <= len(suf) + 2:
            return True
    return False


def _noun_function_from_hint(case: Case, noun_features: Optional[NounFeatures], c2b: dict) -> Function:
    hint = (c2b.get("i3rab_function_hint") or "").strip().lower()
    if hint == "ism_majrur" or case == Case.JARR:
        return Function.ISM_MAJRUR
    if hint == "mafool":
        return Function.MAFOOL
    if hint == "mafool_mutlaq":
        return Function.MAFOOL_MUTLAQ
    if hint == "hal":
        return Function.HAL
    if hint == "tamyiz":
        return Function.TAMYIZ
    if hint == "naib_fa3il":
        return Function.NAIB_FA3IL

    # Best-effort fallback from noun pattern type
    pattern_type = ((noun_features.pattern_type if noun_features else None) or "").strip()
    if case == Case.JARR:
        return Function.ISM_MAJRUR
    if case == Case.NASB and "مصدر" in pattern_type:
        return Function.MAFOOL_MUTLAQ
    return Function.FA3IL


def _mark_after_base(text: str, base_pos: int) -> Optional[str]:
    nfd = unicodedata.normalize("NFD", text or "")
    bases = [i for i, c in enumerate(nfd) if unicodedata.category(c) != "Mn" and c not in " \t"]
    if base_pos < 0:
        base_pos = len(bases) + base_pos
    if base_pos < 0 or base_pos >= len(bases):
        return None
    j = bases[base_pos] + 1
    while j < len(nfd) and unicodedata.category(nfd[j]) == "Mn":
        return nfd[j]
    return None


def _past_bina_from_surface(surface_word: str, vf: VerbFeatures) -> tuple[str, Optional[str]]:
    bare = _bare(surface_word)
    if not bare:
        return "الْفَتْحِ", None

    if bare.endswith("ت") and _mark_after_base(surface_word, -2) == "\u0652":
        return "السُّكُونِ", "تَاءِ الْفَاعِلِ"
    if bare.endswith("نا"):
        return "السُّكُونِ", "نَا الْفَاعِلِينَ"
    if bare.endswith("وا"):
        return "الضَّمِّ", "وَاوِ الْجَمَاعَةِ"
    if bare.endswith("ا") and len(bare) >= 4:
        return "السُّكُونِ", "أَلِفِ الِاثْنَيْنِ"

    bina_map = {
        "معلوم_مفرد":   "الْفَتْحِ",
        "معلوم_جمع":    "الضَّمِّ",
        "معلوم_مثنى":   "السُّكُونِ",
        "مجهول_مفرد":   "الْفَتْحِ",
    }
    suffix_map = {
        "جمع":  "وَاوِ الْجَمَاعَةِ",
        "مثنى": "أَلِفِ الِاثْنَيْنِ",
    }
    bina_key = f"{vf.voice}_{vf.number}"
    return bina_map.get(bina_key, "الْفَتْحِ"), suffix_map.get(vf.number)


def _particle_i3rab_text(kind: str, c2b: dict) -> Optional[str]:
    hint = (c2b.get("i3rab_text_hint") or "").strip()
    if hint:
        return hint
    template = (c2b.get("i3rab_template") or "").strip()
    if template:
        if "{" in template:
            effect_sig = ((c2b.get("effect_signature") or "") + " " + (c2b.get("operator_effect") or "")).upper()
            if "JAZM" in effect_sig:
                return "حَرْفُ جَزْمٍ مَبْنِيٌّ عَلَى السُّكُونِ"
            if "NASB" in effect_sig:
                return "حَرْفُ نَصْبٍ مَبْنِيٌّ عَلَى السُّكُونِ"
            return "حَرْفٌ مَبْنِيٌّ"
        return template
    effect_sig = ((c2b.get("effect_signature") or "") + " " + (c2b.get("operator_effect") or "")).upper()
    if "JAZM" in effect_sig:
        return "حَرْفُ جَزْمٍ مَبْنِيٌّ عَلَى السُّكُونِ"
    if "NASB" in effect_sig:
        return "حَرْفُ نَصْبٍ مَبْنِيٌّ عَلَى السُّكُونِ"
    if kind in {"operator", "particle"}:
        return "حَرْفٌ مَبْنِيٌّ"
    if kind == "pronoun":
        return "ضَمِيرٌ مُنْفَصِلٌ مَبْنِيٌّ"
    # name: لفظ الجلالة أو اسم علم
    if kind == "name":
        word = (c2b.get("surface_word") or "").strip()
        bare = _bare(word).replace("\u0671", "\u0627")  # ألف وصل → ا for jalala check
        if _is_jalala_or_no_root_bare(bare):
            return "لَفْظُ الْجَلَالَةِ مَبْنِيٌّ عَلَى الْفَتْحِ"
        return "اسْمٌ عَلَمٌ مَبْنِيٌّ"
    # demonstrative: هذا، ذلك، أولئك...
    if kind == "demonstrative":
        return "اسْمُ إِشَارَةٍ مَبْنِيٌّ"
    # mabni: إياك، ولا، إلَيْكَ...
    if kind == "mabni":
        return "كَلِمَةٌ مَبْنِيَّةٌ"
    # unknown: fallback so every word has some i3rab
    if kind == "unknown":
        return "كَلِمَةٌ مَبْنِيَّةٌ"
    return None


def _build_i3rab(
    kind: str,
    verb_features: Optional[VerbFeatures],
    noun_features: Optional[NounFeatures],
    c2b_features: Optional[dict],
) -> Optional[str]:
    """Map c2e features → WordInfo → generate_i3rab()."""
    try:
        c2b = c2b_features or {}

        # --- VERB ---
        if kind == "verb" and verb_features:
            vf = verb_features
            number_map = {
                "مفرد": Number.MUFRAD,
                "مثنى": Number.MUTHANA,
                "جمع":  Number.JAMA3,
            }
            num = number_map.get(vf.number, Number.MUFRAD)
            is_khamsa = num in (Number.MUTHANA, Number.JAMA3)

            if vf.tense == "ماضي":
                bina, suffix = _past_bina_from_surface(c2b.get("surface_word") or "", vf)
                info = WordInfo(
                    word_type=WordType.VERB_PAST,
                    function=Function.FA3IL,
                    verb_bina=bina,
                    mudari3_suffix=suffix,
                )
            elif vf.tense == "أمر":
                info = WordInfo(
                    word_type=WordType.VERB_AMR,
                    function=Function.FA3IL,
                    is_af3al_khamsa=is_khamsa,
                )
            else:  # مضارع
                case_map = {
                    "nominative":          Case.RAFA,
                    "accusative":          Case.NASB,
                    "accusative_or_genitive": Case.NASB,
                    "genitive":            Case.JARR,
                    "jussive":             Case.JAZM,
                }
                raw_case = c2b.get("case", "nominative")
                case = case_map.get(raw_case, Case.RAFA)
                info = WordInfo(
                    word_type=WordType.VERB_MUD,
                    function=Function.FA3IL,
                    case=case,
                    number=num,
                    is_af3al_khamsa=is_khamsa,
                )
            return generate_i3rab(info)

        # --- NOUN ---
        if kind == "noun" and noun_features:
            nf = noun_features
            case_map = {
                "nominative":             Case.RAFA,
                "accusative":             Case.NASB,
                "genitive":               Case.JARR,
                "accusative_or_genitive": Case.NASB,
                "jussive":                Case.JAZM,
            }
            number_map = {
                "singular": Number.MUFRAD,
                "dual":     Number.MUTHANA,
                "مثنى":     Number.MUTHANA,
                "plural":   Number.JAMA3,
                "جمع":      Number.JAMA3,
            }
            case  = case_map.get(nf.case or "nominative", Case.RAFA)
            num   = number_map.get(nf.number or "singular", Number.MUFRAD)
            gend  = Gender.F if (nf.gender or "").startswith("ف") or nf.gender == "feminine" else Gender.M
            noun_function = _noun_function_from_hint(case, noun_features, c2b)

            info = WordInfo(
                word_type=WordType.NOUN,
                function=noun_function,
                case=case,
                number=num,
                gender=gend,
                is_definite=bool(nf.definite),
            )
            noun_i3rab = generate_i3rab(info)
            # إذا كان الاسم مسبوقاً بحرف جر — نذكر الحرف في العبارة
            prefix = c2b.get("prefix") or ""
            jar_map = [
                ("بال", "الْبَاءُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ"),
                ("ب",   "الْبَاءُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ"),
                ("لل",  "اللَّامُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ"),
                ("ل",   "اللَّامُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْكَسْرِ"),
                ("كال", "الْكَافُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ"),
                ("ك",   "الْكَافُ حَرْفُ جَرٍّ مَبْنِيٌّ عَلَى الْفَتْحِ"),
            ]
            if case == Case.JARR:
                for p, letter_i3rab in jar_map:
                    if prefix.startswith(p):
                        return f"{letter_i3rab}، وَ{noun_i3rab}"
            return noun_i3rab

        if kind in {"operator", "particle", "pronoun", "unknown", "mabni", "demonstrative", "name"}:
            return _particle_i3rab_text(kind, c2b)

    except Exception:
        pass
    return None


class MorphEnricher:
    """Enriches c2b output with deep morphological features."""

    def enrich(
        self,
        word: str,
        stripped: str,
        kind: str,
        root: str,
        c2b_features: Optional[Dict[str, Any]] = None,
        c2b_pattern_template: Optional[str] = None,
    ) -> EnrichmentResult:
        """
        Enrich a single word with morphological features.

        Args:
            word: surface form (with diacritics if available)
            stripped: bare stem from c2b
            kind: verb | noun | operator | mabni | etc.
            root: root string (e.g. "ك-ت-ب" or "كتب") or empty
            c2b_features: optional dict from c2b (number, gender, case, definite)
            c2b_pattern_template: optional pattern template from c2b (e.g. فَاعِل)

        Returns:
            EnrichmentResult with derivation, verb_features or noun_features, confidence
        """
        c2b_features = c2b_features or {}
        bare = _bare(word)
        use_stripped = stripped or bare
        root_letters = _root_letters(root)

        # Derivation: مشتق vs جامد
        if kind in ("mabni", "operator", "particle", "demonstrative", "conjunction"):
            derivation = "جامد"
            confidence = 0.95
        elif _is_jalala_or_no_root_bare(bare) or _is_jalala_or_no_root_bare(use_stripped):
            derivation = "جامد"
            confidence = 0.95
        elif _is_valid_root(root) and kind in ("verb", "noun"):
            derivation = "مشتق"
            confidence = 0.9
        else:
            derivation = "جامد"
            confidence = 0.85

        verb_features: Optional[VerbFeatures] = None
        noun_features: Optional[NounFeatures] = None

        if kind == "verb":
            verb_features = analyze_verb(word, word, root_letters, c2b_pattern_template or "")
            if verb_features:
                confidence = max(confidence, 0.88)
        elif kind == "noun":
            noun_features = analyze_noun(
                word,
                use_stripped,
                root_letters,
                c2b_features=c2b_features,
                c2b_pattern_template=c2b_pattern_template,
            )
            if noun_features:
                confidence = max(confidence, 0.85)

        i3rab_text = _build_i3rab(kind, verb_features, noun_features, c2b_features)

        return EnrichmentResult(
            word=word,
            derivation=derivation,
            verb_features=verb_features,
            noun_features=noun_features,
            confidence=confidence,
            i3rab_text=i3rab_text,
        )
