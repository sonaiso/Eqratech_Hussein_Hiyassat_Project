# -*- coding: utf-8 -*-
"""Rhetoric Signals V1 — extractor (surface and syntax-assisted)."""

from __future__ import annotations

from typing import List, Optional

from .signals import (
    BARE_EMPHASIS,
    BARE_ILLA,
    BARE_ISTIFHAM,
    BARE_ISTIFHAM_HAMZA,
    BARE_MA,
    BARE_NAHY_LA,
    BARE_NIDA,
    BARE_QASAM,
    BARE_QASR_INNAMA,
    BARE_TAMANNI,
    BARE_TARAJJI,
    SIGNAL_EMPHASIS,
    SIGNAL_EXCLUSIVITY,
    SIGNAL_IMPERATIVE,
    SIGNAL_INTERROGATIVE,
    SIGNAL_OATH,
    SIGNAL_PROHIBITION,
    SIGNAL_TAMANNI,
    SIGNAL_TARAJJI,
    SIGNAL_VOCATIVE,
)
from .types import RhetoricSignal

# Nun al-tawkid: نّ (U+0646 U+0651) or ن with shadda
NUN_SHADDA = "\u0646\u0651"


def _bare(s: str) -> str:
    """Strip diacritics for matching."""
    return "".join(
        c for c in (s or "")
        if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)
    ).strip()


def _has_nun_tawkid(token: str) -> bool:
    """True if token ends with نّ (nun al-tawkid)."""
    bare_token = _bare(token)
    return bare_token.endswith("نن") or NUN_SHADDA in token


def _has_lam_tawkid(token: str) -> bool:
    """True if token starts with ل (lam al-tawkid) in a verb context."""
    b = _bare(token)
    if not b or len(b) < 2:
        return False
    # لَأَفْعَلَنَّ: starts with ل then همزة وصل
    if b[0] == "ل" and b[1] in "اأ":
        return True
    return False


class RhetoricSignalsExtractor:
    """Extracts rhetoric signals from a tokenized sentence (V1: surface/syntax only)."""

    def extract(
        self,
        tokens: List[str],
        sentence_type: Optional[str] = None,
    ) -> List[RhetoricSignal]:
        """Return one or more rhetoric signals for the sentence. Multi-label supported."""
        if not tokens:
            return []
        bare_tokens = [_bare(t) for t in tokens]
        signals: List[RhetoricSignal] = []

        # Interrogative
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_ISTIFHAM:
                signals.append(RhetoricSignal(
                    type=SIGNAL_INTERROGATIVE[0],
                    label_ar=SIGNAL_INTERROGATIVE[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.92,
                    evidence=[f"استفهام بـ {tokens[i]}"],
                ))
                break
            if bt == BARE_ISTIFHAM_HAMZA and len(bt) <= 2:
                signals.append(RhetoricSignal(
                    type=SIGNAL_INTERROGATIVE[0],
                    label_ar=SIGNAL_INTERROGATIVE[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88,
                    evidence=["همزة استفهام"],
                ))
                break

        # Vocative
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_NIDA:
                signals.append(RhetoricSignal(
                    type=SIGNAL_VOCATIVE[0],
                    label_ar=SIGNAL_VOCATIVE[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=[f"نداء بـ {tokens[i]}"],
                ))
                break

        # Oath
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_QASAM:
                signals.append(RhetoricSignal(
                    type=SIGNAL_OATH[0],
                    label_ar=SIGNAL_OATH[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=[f"قسم بـ {tokens[i]}"],
                ))
                break

        # Tarajji
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_TARAJJI:
                signals.append(RhetoricSignal(
                    type=SIGNAL_TARAJJI[0],
                    label_ar=SIGNAL_TARAJJI[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.92,
                    evidence=[f"ترجّي بـ {tokens[i]}"],
                ))
                break

        # Tamanni
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_TAMANNI:
                signals.append(RhetoricSignal(
                    type=SIGNAL_TAMANNI[0],
                    label_ar=SIGNAL_TAMANNI[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=[f"تمنّي بـ {tokens[i]}"],
                ))
                break

        # Exclusivity: إنما / أنما or ما ... إلا
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_QASR_INNAMA:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EXCLUSIVITY[0],
                    label_ar=SIGNAL_EXCLUSIVITY[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.90,
                    evidence=["إنما / أنما قصر"],
                ))
                break
        if not any(s.type == SIGNAL_EXCLUSIVITY[0] for s in signals):
            ma_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_MA), None)
            illa_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_ILLA), None)
            if ma_idx is not None and illa_idx is not None and ma_idx < illa_idx:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EXCLUSIVITY[0],
                    label_ar=SIGNAL_EXCLUSIVITY[1],
                    trigger=f"{tokens[ma_idx]} ... {tokens[illa_idx]}",
                    span={"start": ma_idx, "end": illa_idx + 1},
                    confidence=0.85,
                    evidence=["ما ... إلا قصر"],
                ))

        # Emphasis: إنّ, لقد, lam al-tawkid, nun al-tawkid
        for i, bt in enumerate(bare_tokens):
            if bt in BARE_EMPHASIS:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.90,
                    evidence=[f"توكيد بـ {tokens[i]}"],
                ))
        for i, t in enumerate(tokens):
            if _has_lam_tawkid(t):
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88,
                    evidence=["لام التوكيد"],
                ))
                break
        for i, t in enumerate(tokens):
            if _has_nun_tawkid(t):
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88,
                    evidence=["نون التوكيد"],
                ))
                break

        # Imperative / Prohibition: reuse sentence_type when provided
        if sentence_type is not None:
            if sentence_type in ("أمر",):
                signals.append(RhetoricSignal(
                    type=SIGNAL_IMPERATIVE[0],
                    label_ar=SIGNAL_IMPERATIVE[1],
                    trigger=tokens[0] if tokens else "",
                    span={"start": 0, "end": min(1, len(tokens))},
                    confidence=0.88,
                    evidence=["جملة أمر من التصنيف"],
                ))
            elif sentence_type in ("نهي",):
                # Find لا for span
                la_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_NAHY_LA), 0)
                signals.append(RhetoricSignal(
                    type=SIGNAL_PROHIBITION[0],
                    label_ar=SIGNAL_PROHIBITION[1],
                    trigger=tokens[la_idx] if la_idx < len(tokens) else "",
                    span={"start": la_idx, "end": la_idx + 1},
                    confidence=0.90,
                    evidence=["جملة نهي من التصنيف"],
                ))

        return signals
