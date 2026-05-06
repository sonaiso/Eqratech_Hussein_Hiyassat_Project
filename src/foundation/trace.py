"""
استخراج الأثر — Trace Extractor
==================================
يُوفِّر هذا الملف TraceExtractor الذي يُطبِّق دالة الأثر
τ : R → T بمستويات متعددة:

    SURFACE  → تجزئة الكلمات ووحدات يونيكود
    PHONEMIC → تحليل الفونيمات (ربط محركات Eqratech)
    MORPHEMIC → تحليل الجذر والوزن (ربط محركات Eqratech)
    SYNTACTIC → تحليل العلاقات النحوية
    SEMANTIC  → تحليل الدلالة
    FULL      → كل المستويات متسلسلة

في v0.1، المستويات SURFACE و PHONEMIC مُطبَّقة بشكل كامل،
والمستويات الأعلى تُعيد بيانات جزئية مع placeholder
لربط محركات Eqratech الكاملة لاحقاً.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from .ontology import Reality, Trace, TraceLevel, trace_fn
from .unicode_units import ArabicText, TokenUnit, UnitKind


# ---------------------------------------------------------------------------
# كائن الأثر المُعزَّز
# ---------------------------------------------------------------------------

@dataclass
class RichTrace:
    """
    أثر غني — يُضيف إلى Trace الأساسي:
    - وحدات يونيكود كاملة لكل كلمة
    - إحصاءات نصية تفصيلية
    - تحليل مستويات عُليا عند توفرها
    """
    base: Trace
    arabic_text: ArabicText
    token_analyses: List[Dict[str, Any]] = field(default_factory=list)
    level_data: Dict[str, Any] = field(default_factory=dict)

    @property
    def uid(self) -> str:
        return self.base.uid

    @property
    def tokens(self) -> List[str]:
        return self.base.tokens

    def to_dict(self) -> Dict[str, Any]:
        return {
            "uid": self.uid,
            "source_uid": self.base.source_uid,
            "level": self.base.level.value,
            "tokens": self.tokens,
            "features": self.base.features,
            "token_analyses": self.token_analyses,
            "level_data": self.level_data,
            "stats": self.arabic_text.stats(),
        }

    def __repr__(self) -> str:
        return (
            f"RichTrace(uid={self.uid!r}, level={self.base.level.value!r}, "
            f"tokens={len(self.tokens)}, units={len(self.arabic_text)})"
        )


# ---------------------------------------------------------------------------
# المُستخلِص
# ---------------------------------------------------------------------------

class TraceExtractor:
    """
    مُستخلِص الأثر — يُطبِّق τ : R → T بعمق اختياري.

    الاستخدام:
        extractor = TraceExtractor()
        reality = Reality(raw_text="الكِتَابُ مُفِيدٌ")
        rich_trace = extractor.extract(reality)
        print(rich_trace)

    مستويات التحليل:
        SURFACE   → كلمات + يونيكود كامل (مُطبَّق في v0.1)
        PHONEMIC  → تحليل الحركات والأصوات (جزئي في v0.1)
        MORPHEMIC → جذر ووزن (placeholder في v0.1)
        SYNTACTIC → علاقات نحوية (placeholder في v0.1)
        SEMANTIC  → دلالة (placeholder في v0.1)
        FULL      → كل المستويات
    """

    def __init__(self) -> None:
        self._cache: Dict[str, RichTrace] = {}

    # ------------------------------------------------------------------
    # الواجهة العامة
    # ------------------------------------------------------------------

    def extract(
        self,
        reality: Reality,
        level: TraceLevel = TraceLevel.SURFACE,
        use_cache: bool = True,
    ) -> RichTrace:
        """
        يستخلص أثراً غنياً من واقع.

        المعاملات:
            reality   — الواقع المُحلَّل
            level     — مستوى التحليل المطلوب
            use_cache — هل يُستخدَم cache؟

        يُعيد: RichTrace
        """
        cache_key = f"{reality.uid}:{level.value}"
        if use_cache and cache_key in self._cache:
            return self._cache[cache_key]

        # الأثر الأساسي
        base_trace = trace_fn(reality, level)

        # التحليل بالأثر اليونيكودي
        arabic_text = ArabicText.from_string(reality.raw_text)
        token_analyses = self._analyse_tokens(arabic_text.tokens())

        # بيانات المستويات
        level_data: Dict[str, Any] = {}

        if level in (TraceLevel.SURFACE, TraceLevel.FULL):
            level_data["surface"] = self._surface_analysis(arabic_text)

        if level in (TraceLevel.PHONEMIC, TraceLevel.FULL):
            level_data["phonemic"] = self._phonemic_analysis(arabic_text)

        if level in (TraceLevel.MORPHEMIC, TraceLevel.FULL):
            level_data["morphemic"] = self._morphemic_analysis(arabic_text)

        if level in (TraceLevel.SYNTACTIC, TraceLevel.FULL):
            level_data["syntactic"] = self._syntactic_analysis(arabic_text)

        if level in (TraceLevel.SEMANTIC, TraceLevel.FULL):
            level_data["semantic"] = self._semantic_analysis(arabic_text)

        rich = RichTrace(
            base=base_trace,
            arabic_text=arabic_text,
            token_analyses=token_analyses,
            level_data=level_data,
        )

        if use_cache:
            self._cache[cache_key] = rich

        return rich

    def extract_full(self, reality: Reality) -> RichTrace:
        """استختصار لـ extract(reality, TraceLevel.FULL)."""
        return self.extract(reality, TraceLevel.FULL)

    # ------------------------------------------------------------------
    # تحليل الكلمات
    # ------------------------------------------------------------------

    def _analyse_tokens(
        self, token_units: List[TokenUnit]
    ) -> List[Dict[str, Any]]:
        """يُحلِّل كل كلمة ويُعيد قاموس تفصيلي."""
        analyses = []
        for tok in token_units:
            unit_data = []
            for u in tok.units:
                unit_data.append({
                    "char": u.char,
                    "codepoint": u.codepoint_str,
                    "utf8": u.utf8_hex(),
                    "kind": u.kind.value,
                    "name_ar": u.name_ar,
                    "cause": u.cause,
                    "effect": u.effect,
                    "function": u.function,
                })
            analyses.append({
                "token": tok.raw,
                "letters_only": tok.letters_only(),
                "harakat": tok.harakat_sequence(),
                "codepoints": tok.codepoints(),
                "units": unit_data,
            })
        return analyses

    # ------------------------------------------------------------------
    # مستوى السطح
    # ------------------------------------------------------------------

    @staticmethod
    def _surface_analysis(text: ArabicText) -> Dict[str, Any]:
        """تحليل سطحي: عد الحروف والحركات والكلمات."""
        stats = text.stats()
        return {
            "method": "surface",
            "stats": stats,
            "has_harakat": stats["by_kind"].get(UnitKind.HARAKA.value, 0) > 0
            or stats["by_kind"].get(UnitKind.TANWIN.value, 0) > 0,
            "has_shadda": stats["by_kind"].get(UnitKind.SHADDA.value, 0) > 0,
        }

    # ------------------------------------------------------------------
    # مستوى الصوت
    # ------------------------------------------------------------------

    @staticmethod
    def _phonemic_analysis(text: ArabicText) -> Dict[str, Any]:
        """
        تحليل صوتي جزئي — يُحدِّد تسلسل الحركات.
        الربط الكامل بمحركات C2a سيكون في v0.2.
        """
        harakat_seq = []
        for unit in text.units:
            if unit.is_diacritic():
                harakat_seq.append({
                    "char": unit.char,
                    "name": unit.name_ar,
                    "position": unit.position,
                })

        return {
            "method": "phonemic_partial",
            "harakat_sequence": harakat_seq,
            "has_tanwin": any(u.kind == UnitKind.TANWIN for u in text.units),
            "has_shadda": any(u.kind == UnitKind.SHADDA for u in text.units),
            "note": "ربط C2a كامل في v0.2",
        }

    # ------------------------------------------------------------------
    # مستوى الصرف
    # ------------------------------------------------------------------

    @staticmethod
    def _morphemic_analysis(text: ArabicText) -> Dict[str, Any]:
        """
        تحليل صرفي — placeholder لربط محرك RootExtractor.
        يُعيد بيانات أساسية وترك ربط C2b لـ v0.2.
        """
        tokens = [tok.letters_only() for tok in text.tokens()]
        return {
            "method": "morphemic_placeholder",
            "bare_tokens": tokens,
            "note": "ربط RootExtractor (C2b) في v0.2",
        }

    # ------------------------------------------------------------------
    # مستوى النحو
    # ------------------------------------------------------------------

    @staticmethod
    def _syntactic_analysis(text: ArabicText) -> Dict[str, Any]:
        """
        تحليل نحوي — placeholder لربط SyntaxTheory.
        """
        return {
            "method": "syntactic_placeholder",
            "token_count": len(text.tokens()),
            "note": "ربط SyntaxTheory في v0.2",
        }

    # ------------------------------------------------------------------
    # مستوى الدلالة
    # ------------------------------------------------------------------

    @staticmethod
    def _semantic_analysis(text: ArabicText) -> Dict[str, Any]:
        """
        تحليل دلالي — placeholder لربط محركات المعجم.
        """
        return {
            "method": "semantic_placeholder",
            "note": "ربط LexiconEngines في v0.2",
        }
