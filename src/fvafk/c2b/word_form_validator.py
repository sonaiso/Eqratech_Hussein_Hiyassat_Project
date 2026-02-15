"""
WordForm validation helpers.

These checks are intentionally best-effort and non-blocking: they return a list
of human-readable issues rather than raising exceptions.
"""

from __future__ import annotations

from typing import List

from .word_form import PartOfSpeech, WordForm


def validate_word_form(wf: WordForm) -> List[str]:
    issues: List[str] = []

    if not wf.surface:
        issues.append("surface is empty")

    if wf.pos in {PartOfSpeech.OPERATOR, PartOfSpeech.PARTICLE, PartOfSpeech.DEMONSTRATIVE, PartOfSpeech.NAME, PartOfSpeech.PRONOUN}:
        # Closed-class: root/pattern may be absent.
        return issues

    if wf.pos in {PartOfSpeech.NOUN, PartOfSpeech.VERB}:
        if wf.root is None:
            issues.append("missing root for content word")
        if wf.pattern is None:
            issues.append("missing pattern for content word")

    return issues

