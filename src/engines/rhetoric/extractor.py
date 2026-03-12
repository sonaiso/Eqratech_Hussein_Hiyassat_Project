# -*- coding: utf-8 -*-
"""
Rhetoric Signals V1 — extractor.

Layer 5: consumes Lexicon (Layer 3) and Syntax/Sentence classification (Layer 4).
Primary: derive signals from sentence_type and word_analyses (kind/operator).
Fallback: raw-token matching only when word_analyses not provided (documented).
See docs/RHETORIC_ARCHITECTURE_COMPLIANCE.md.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

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

NUN_SHADDA = "\u0646\u0651"

# Layer 4 sentence_type (Arabic) → (signal_type, label_ar) for primary path
_SENTENCE_TYPE_TO_SIGNAL: Dict[str, tuple] = {
    "استفهام": SIGNAL_INTERROGATIVE,
    "نداء": SIGNAL_VOCATIVE,
    "قسم": SIGNAL_OATH,
    "توكيد": SIGNAL_EMPHASIS,
    "ترجي": SIGNAL_TARAJJI,
    "تمني": SIGNAL_TAMANNI,
    "أمر": SIGNAL_IMPERATIVE,
    "نهي": SIGNAL_PROHIBITION,
}


def _bare(s: str) -> str:
    """Strip diacritics for matching."""
    return "".join(
        c for c in (s or "")
        if not (0x064B <= ord(c) <= 0x0652 or ord(c) == 0x0670)
    ).strip()


def _has_nun_tawkid(token: str) -> bool:
    """True if token ends with نّ (nun al-tawkid). Fallback when morphology does not provide it."""
    bare_token = _bare(token)
    return bare_token.endswith("نن") or NUN_SHADDA in token


def _has_lam_tawkid(token: str) -> bool:
    """True if token starts with ل then همزة (lam al-tawkid). Must NOT be used for لا (operator)."""
    b = _bare(token)
    if not b or len(b) < 2:
        return False
    if b[0] == "ل" and b[1] in "اأ":
        return True
    return False


def _is_operator_token(word_analysis: Optional[Dict[str, Any]]) -> bool:
    """True if Lexicon (Layer 3) classified this word as operator."""
    if not word_analysis:
        return False
    return (word_analysis.get("kind") or "").strip().lower() == "operator"


class RhetoricSignalsExtractor:
    """
    Extracts rhetoric signals from a sentence.
    Primary: Layer 4 (sentence_type) and Layer 3 (word_analyses: kind/operator).
    Fallback: raw token matching only when word_analyses not provided.
    """

    def extract(
        self,
        tokens: List[str],
        sentence_type: Optional[str] = None,
        word_analyses: Optional[List[Dict[str, Any]]] = None,
        trigger_word: Optional[str] = None,
    ) -> List[RhetoricSignal]:
        """
        Return rhetoric signals. Multi-label supported.
        - sentence_type: from Layer 4 (c2d).
        - word_analyses: optional list of c2b word dicts (kind, operator) aligned with tokens.
        - trigger_word: optional trigger from sentence classifier for span/trigger.
        """
        if not tokens:
            return []
        bare_tokens = [_bare(t) for t in tokens]
        signals: List[RhetoricSignal] = []
        emitted_types: set = set()

        def _trigger_span_for_sentence_type() -> tuple:
            """Resolve trigger and span from trigger_word or first token."""
            if trigger_word:
                for i, t in enumerate(tokens):
                    if _bare(t) == _bare(trigger_word):
                        return t, {"start": i, "end": i + 1}
            if tokens:
                return tokens[0], {"start": 0, "end": 1}
            return "", {"start": 0, "end": 0}

        # ---------- Primary: from Layer 4 (sentence_type) ----------
        if sentence_type:
            st_norm = (sentence_type or "").strip()
            if st_norm in _SENTENCE_TYPE_TO_SIGNAL:
                sig_tuple = _SENTENCE_TYPE_TO_SIGNAL[st_norm]
                emitted_types.add(sig_tuple[0])
                trigger, span = _trigger_span_for_sentence_type()
                if st_norm == "نهي" and word_analyses:
                    for i, w in enumerate(word_analyses):
                        if i < len(tokens) and _bare(tokens[i]) == BARE_NAHY_LA:
                            trigger, span = tokens[i], {"start": i, "end": i + 1}
                            break
                signals.append(RhetoricSignal(
                    type=sig_tuple[0],
                    label_ar=sig_tuple[1],
                    trigger=trigger,
                    span=span,
                    confidence=0.90,
                    evidence=["من تصنيف الجملة (الطبقة 4)"],
                ))

        # ---------- Primary: from Layer 3 (word_analyses: operator) ----------
        if word_analyses:
            for i, w in enumerate(word_analyses):
                if i >= len(tokens):
                    break
                kind = (w.get("kind") or "").strip().lower()
                if kind != "operator":
                    continue
                op = w.get("operator") or {}
                op_bare = (op.get("operator") or "").strip().lower() if isinstance(op, dict) else ""
                if not op_bare:
                    op_bare = _bare(tokens[i])

                # Emit only if not already emitted from sentence_type
                if "interrogative" not in emitted_types and op_bare in BARE_ISTIFHAM:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_INTERROGATIVE[0],
                        label_ar=SIGNAL_INTERROGATIVE[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.92,
                        evidence=["من المعجم (أداة استفهام)"],
                    ))
                    emitted_types.add(SIGNAL_INTERROGATIVE[0])
                if "vocative" not in emitted_types and op_bare in BARE_NIDA:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_VOCATIVE[0],
                        label_ar=SIGNAL_VOCATIVE[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.95,
                        evidence=["من المعجم (أداة نداء)"],
                    ))
                    emitted_types.add(SIGNAL_VOCATIVE[0])
                if "oath" not in emitted_types and op_bare in BARE_QASAM:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_OATH[0],
                        label_ar=SIGNAL_OATH[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.95,
                        evidence=["من المعجم (أداة قسم)"],
                    ))
                    emitted_types.add(SIGNAL_OATH[0])
                if "tarajji" not in emitted_types and op_bare in BARE_TARAJJI:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_TARAJJI[0],
                        label_ar=SIGNAL_TARAJJI[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.92,
                        evidence=["من المعجم (أداة ترجّي)"],
                    ))
                    emitted_types.add(SIGNAL_TARAJJI[0])
                if "tamanni" not in emitted_types and op_bare in BARE_TAMANNI:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_TAMANNI[0],
                        label_ar=SIGNAL_TAMANNI[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.95,
                        evidence=["من المعجم (أداة تمنّي)"],
                    ))
                    emitted_types.add(SIGNAL_TAMANNI[0])
                if "exclusivity" not in emitted_types and op_bare in BARE_QASR_INNAMA:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_EXCLUSIVITY[0],
                        label_ar=SIGNAL_EXCLUSIVITY[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.90,
                        evidence=["من المعجم (إنما/أنما قصر)"],
                    ))
                    emitted_types.add(SIGNAL_EXCLUSIVITY[0])
                if "emphasis" not in emitted_types and op_bare in BARE_EMPHASIS:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_EMPHASIS[0],
                        label_ar=SIGNAL_EMPHASIS[1],
                        trigger=tokens[i],
                        span={"start": i, "end": i + 1},
                        confidence=0.90,
                        evidence=["من المعجم (أداة توكيد)"],
                    ))
                    emitted_types.add(SIGNAL_EMPHASIS[0])

            # Emphasis: lam al-tawkid — only on non-operator tokens (لا must never be lam tawkid)
            if "emphasis" not in emitted_types:
                for i, t in enumerate(tokens):
                    if _is_operator_token(word_analyses[i] if i < len(word_analyses) else None):
                        continue
                    if _has_lam_tawkid(t):
                        signals.append(RhetoricSignal(
                            type=SIGNAL_EMPHASIS[0],
                            label_ar=SIGNAL_EMPHASIS[1],
                            trigger=tokens[i],
                            span={"start": i, "end": i + 1},
                            confidence=0.88,
                            evidence=["لام التوكيد (انتباه: لا تُطبَّق على أداة)"],
                        ))
                        emitted_types.add(SIGNAL_EMPHASIS[0])
                        break
            if "emphasis" not in emitted_types:
                for i, t in enumerate(tokens):
                    if _has_nun_tawkid(t):
                        signals.append(RhetoricSignal(
                            type=SIGNAL_EMPHASIS[0],
                            label_ar=SIGNAL_EMPHASIS[1],
                            trigger=tokens[i],
                            span={"start": i, "end": i + 1},
                            confidence=0.88,
                            evidence=["نون التوكيد (fallback)"],
                        ))
                        emitted_types.add(SIGNAL_EMPHASIS[0])
                        break

            # Exclusivity: ما ... إلا (syntax-assisted)
            if "exclusivity" not in emitted_types:
                ma_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_MA), None)
                illa_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_ILLA), None)
                if ma_idx is not None and illa_idx is not None and ma_idx < illa_idx:
                    signals.append(RhetoricSignal(
                        type=SIGNAL_EXCLUSIVITY[0],
                        label_ar=SIGNAL_EXCLUSIVITY[1],
                        trigger=f"{tokens[ma_idx]} ... {tokens[illa_idx]}",
                        span={"start": ma_idx, "end": illa_idx + 1},
                        confidence=0.85,
                        evidence=["ما ... إلا قصر (سياق)"],
                    ))
                    emitted_types.add(SIGNAL_EXCLUSIVITY[0])

            # No raw-token fallback when word_analyses provided — primary path only
            return signals

        # ---------- Fallback: no word_analyses — raw token matching (documented) ----------
        for i, bt in enumerate(bare_tokens):
            if "interrogative" not in emitted_types and (bt in BARE_ISTIFHAM or (bt == BARE_ISTIFHAM_HAMZA and len(bt) <= 2)):
                signals.append(RhetoricSignal(
                    type=SIGNAL_INTERROGATIVE[0],
                    label_ar=SIGNAL_INTERROGATIVE[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88 if bt == BARE_ISTIFHAM_HAMZA else 0.92,
                    evidence=["استفهام (fallback بدون سياق معجمي)"],
                ))
                emitted_types.add(SIGNAL_INTERROGATIVE[0])
                break
        for i, bt in enumerate(bare_tokens):
            if "vocative" not in emitted_types and bt in BARE_NIDA:
                signals.append(RhetoricSignal(
                    type=SIGNAL_VOCATIVE[0],
                    label_ar=SIGNAL_VOCATIVE[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=["نداء (fallback)"],
                ))
                emitted_types.add(SIGNAL_VOCATIVE[0])
                break
        for i, bt in enumerate(bare_tokens):
            if "oath" not in emitted_types and bt in BARE_QASAM:
                signals.append(RhetoricSignal(
                    type=SIGNAL_OATH[0],
                    label_ar=SIGNAL_OATH[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=["قسم (fallback)"],
                ))
                emitted_types.add(SIGNAL_OATH[0])
                break
        for i, bt in enumerate(bare_tokens):
            if "tarajji" not in emitted_types and bt in BARE_TARAJJI:
                signals.append(RhetoricSignal(
                    type=SIGNAL_TARAJJI[0],
                    label_ar=SIGNAL_TARAJJI[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.92,
                    evidence=["ترجّي (fallback)"],
                ))
                emitted_types.add(SIGNAL_TARAJJI[0])
                break
        for i, bt in enumerate(bare_tokens):
            if "tamanni" not in emitted_types and bt in BARE_TAMANNI:
                signals.append(RhetoricSignal(
                    type=SIGNAL_TAMANNI[0],
                    label_ar=SIGNAL_TAMANNI[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.95,
                    evidence=["تمنّي (fallback)"],
                ))
                emitted_types.add(SIGNAL_TAMANNI[0])
                break
        for i, bt in enumerate(bare_tokens):
            if "exclusivity" not in emitted_types and bt in BARE_QASR_INNAMA:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EXCLUSIVITY[0],
                    label_ar=SIGNAL_EXCLUSIVITY[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.90,
                    evidence=["قصر إنما (fallback)"],
                ))
                emitted_types.add(SIGNAL_EXCLUSIVITY[0])
                break
        if "exclusivity" not in emitted_types:
            ma_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_MA), None)
            illa_idx = next((i for i, bt in enumerate(bare_tokens) if bt == BARE_ILLA), None)
            if ma_idx is not None and illa_idx is not None and ma_idx < illa_idx:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EXCLUSIVITY[0],
                    label_ar=SIGNAL_EXCLUSIVITY[1],
                    trigger=f"{tokens[ma_idx]} ... {tokens[illa_idx]}",
                    span={"start": ma_idx, "end": illa_idx + 1},
                    confidence=0.85,
                    evidence=["ما ... إلا (fallback)"],
                ))
                emitted_types.add(SIGNAL_EXCLUSIVITY[0])
        for i, bt in enumerate(bare_tokens):
            if "emphasis" not in emitted_types and bt in BARE_EMPHASIS:
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.90,
                    evidence=["توكيد (fallback)"],
                ))
                emitted_types.add(SIGNAL_EMPHASIS[0])
        for i, t in enumerate(tokens):
            if "emphasis" not in emitted_types and _has_lam_tawkid(t):
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88,
                    evidence=["لام التوكيد (fallback)"],
                ))
                emitted_types.add(SIGNAL_EMPHASIS[0])
                break
        for i, t in enumerate(tokens):
            if "emphasis" not in emitted_types and _has_nun_tawkid(t):
                signals.append(RhetoricSignal(
                    type=SIGNAL_EMPHASIS[0],
                    label_ar=SIGNAL_EMPHASIS[1],
                    trigger=tokens[i],
                    span={"start": i, "end": i + 1},
                    confidence=0.88,
                    evidence=["نون التوكيد (fallback)"],
                ))
                emitted_types.add(SIGNAL_EMPHASIS[0])
                break

        # Imperative / Prohibition from sentence_type only (already done above if sentence_type was set)
        if sentence_type in ("أمر",) and "imperative" not in emitted_types:
            trigger, span = _trigger_span_for_sentence_type()
            signals.append(RhetoricSignal(
                type=SIGNAL_IMPERATIVE[0],
                label_ar=SIGNAL_IMPERATIVE[1],
                trigger=trigger,
                span=span,
                confidence=0.88,
                evidence=["جملة أمر من التصنيف"],
            ))
        elif sentence_type in ("نهي",) and "prohibition" not in emitted_types:
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
