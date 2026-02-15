"""
WordFormBuilder.

Builds `WordForm` objects from the current C2b dict outputs emitted by the CLI.
Supports both:
- single-word C2b payloads (no "word"/"span")
- multi-word items (contains "word" and "span")
"""

from __future__ import annotations

from dataclasses import asdict
from typing import Any, Dict, Optional, Tuple

from .word_form import (
    Affixes,
    Case,
    Gender,
    Number,
    PartOfSpeech,
    PatternInfo,
    RootInfo,
    Span,
    SyntaxRole,
    WordForm,
    strip_diacritics,
)


def _pos_from_kind(kind: str) -> PartOfSpeech:
    k = (kind or "").strip().lower()
    for pos in PartOfSpeech:
        if pos.value == k:
            return pos
    return PartOfSpeech.UNKNOWN


def _case_from_features(features: Dict[str, Any]) -> Optional[Case]:
    v = (features or {}).get("case")
    if not v:
        return None
    v = str(v).strip().lower()
    for c in Case:
        if c.value == v:
            return c
    return Case.UNKNOWN


def _number_from_features(features: Dict[str, Any]) -> Optional[Number]:
    v = (features or {}).get("number")
    if not v:
        return None
    v = str(v).strip().lower()
    for n in Number:
        if n.value == v:
            return n
    return Number.UNKNOWN


def _gender_from_features(features: Dict[str, Any]) -> Optional[Gender]:
    v = (features or {}).get("gender")
    if not v:
        return None
    v = str(v).strip().lower()
    for g in Gender:
        if g.value == v:
            return g
    return Gender.UNKNOWN


class WordFormBuilder:
    """
    Construct `WordForm` from C2b analysis dicts.

    This is a bridge layer; it should not throw on missing optional fields.
    """

    def from_multi_word_item(self, item: Dict[str, Any]) -> WordForm:
        surface = item.get("word") or item.get("surface") or ""
        span_dict = item.get("span") or {}
        span = None
        if isinstance(span_dict, dict) and "start" in span_dict and "end" in span_dict:
            span = Span(start=int(span_dict["start"]), end=int(span_dict["end"]))
        return self.from_single(surface=surface, analysis=item, span=span)

    def from_single(self, *, surface: str, analysis: Dict[str, Any], span: Optional[Span] = None) -> WordForm:
        kind = (analysis.get("kind") or "unknown") if isinstance(analysis, dict) else "unknown"
        features = (analysis.get("features") or {}) if isinstance(analysis, dict) else {}

        pos = _pos_from_kind(kind)
        bare = strip_diacritics(surface)

        # Root
        root_info: Optional[RootInfo] = None
        root = analysis.get("root") if isinstance(analysis, dict) else None
        if isinstance(root, dict) and root.get("letters"):
            letters = tuple(root.get("letters") or ())
            root_info = RootInfo(
                letters=letters,
                formatted=str(root.get("formatted") or "-".join(letters)),
                root_type=str(root.get("type") or "unknown"),
                length=int(root.get("length") or len(letters)),
            )

        # Pattern
        pattern_info: Optional[PatternInfo] = None
        pat = analysis.get("pattern") if isinstance(analysis, dict) else None
        if isinstance(pat, dict):
            pattern_info = PatternInfo(
                template=pat.get("template"),
                pattern_type=str(pat.get("type") or "unknown"),
                category=str(pat.get("category") or "unknown"),
                stem=pat.get("stem"),
                features=dict(pat.get("features") or {}),
            )

        # Affixes
        affixes_info: Optional[Affixes] = None
        aff = analysis.get("affixes") if isinstance(analysis, dict) else None
        if isinstance(aff, dict):
            affixes_info = Affixes(
                prefix=aff.get("prefix"),
                suffix=aff.get("suffix"),
                normalized=aff.get("normalized"),
                stripped=aff.get("stripped"),
            )

        # Closed-class payloads (if present)
        operator = analysis.get("operator") if isinstance(analysis, dict) else None
        particle = analysis.get("particle") if isinstance(analysis, dict) else None
        demonstrative = analysis.get("demonstrative") if isinstance(analysis, dict) else None
        name = analysis.get("name") if isinstance(analysis, dict) else None
        pronoun = analysis.get("pronoun") if isinstance(analysis, dict) else None

        return WordForm(
            surface=surface,
            bare=bare,
            kind=str(kind),
            pos=pos,
            span=span,
            root=root_info,
            pattern=pattern_info,
            affixes=affixes_info,
            features=dict(features) if isinstance(features, dict) else {},
            operator=operator if isinstance(operator, dict) else None,
            particle=particle if isinstance(particle, dict) else None,
            demonstrative=demonstrative if isinstance(demonstrative, dict) else None,
            name=name if isinstance(name, dict) else None,
            pronoun=pronoun if isinstance(pronoun, dict) else None,
            case=_case_from_features(features if isinstance(features, dict) else {}),
            definiteness=(features or {}).get("definite") if isinstance(features, dict) else None,
            number=_number_from_features(features if isinstance(features, dict) else {}),
            gender=_gender_from_features(features if isinstance(features, dict) else {}),
            syntax_role=None,
            dependencies=[],
        )

