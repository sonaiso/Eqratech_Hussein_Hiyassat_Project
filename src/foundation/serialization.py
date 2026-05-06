"""
التسلسل والإخراج — Serialization
===================================
يُوفِّر هذا الملف أدوات تحويل StagedAnalysis إلى:
- JSON (قابل للحفظ والنقل)
- نص عربي مقروء (للعرض)
- dict (للمعالجة البرمجية)

وكذلك إعادة تحميل التحليل من JSON.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, Optional, Union

from .pipeline import StagedAnalysis, PipelineStage, STAGE_NAMES_AR, STAGE_NAMES_EN
from .outputs import OutputKind


# ---------------------------------------------------------------------------
# تسلسل
# ---------------------------------------------------------------------------

def serialize_analysis(
    analysis: StagedAnalysis,
    *,
    indent: int = 2,
    ensure_ascii: bool = False,
) -> str:
    """
    يُحوِّل StagedAnalysis إلى JSON نصي.

    المعاملات:
        analysis      — نتيجة التحليل
        indent        — مسافة JSON (افتراضي: 2)
        ensure_ascii  — هل يُهرِّب الأحرف غير ASCII؟ (افتراضي: False)

    يُعيد: str (JSON)

    مثال:
        analysis = pipeline.run("الكِتَابُ")
        json_str = serialize_analysis(analysis)
        print(json_str)
    """
    data = analysis.to_dict()
    # تأكد من قابلية التسلسل
    data = _make_serializable(data)
    return json.dumps(data, indent=indent, ensure_ascii=ensure_ascii)


def save_analysis(
    analysis: StagedAnalysis,
    path: Union[str, Path],
    *,
    indent: int = 2,
) -> Path:
    """
    يحفظ التحليل إلى ملف JSON.

    يُعيد: Path الملف المحفوظ.
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    json_str = serialize_analysis(analysis, indent=indent)
    path.write_text(json_str, encoding="utf-8")
    return path


def load_analysis(source: Union[str, Path, dict]) -> Dict[str, Any]:
    """
    يُحمِّل تحليلاً محفوظاً من JSON ملف أو نص أو dict.

    يُعيد: dict (البنية الخام للتحليل)
    ملاحظة: يُعيد dict لا StagedAnalysis — لأن إعادة بناء الكائنات
    الكاملة تتطلب تشغيل السلسلة مجدداً في v0.1.
    """
    if isinstance(source, dict):
        return source
    if isinstance(source, Path):
        if source.exists():
            return json.loads(source.read_text(encoding="utf-8"))
        raise FileNotFoundError(f"File not found: {source}")
    if isinstance(source, str):
        # هل هو مسار ملف موجود؟
        p = Path(source)
        try:
            if p.exists():
                return json.loads(p.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            pass
        # افترض أنه JSON نصي مباشر
        return json.loads(source)
    raise TypeError(f"Unsupported source type: {type(source)}")


# ---------------------------------------------------------------------------
# إخراج نصي للعرض
# ---------------------------------------------------------------------------

def format_analysis_text(analysis: StagedAnalysis) -> str:
    """
    يُحوِّل التحليل إلى نص عربي مقروء.

    يُعيد: str
    """
    lines = [
        "╔══════════════════════════════════════════════════════════╗",
        f"║  النص المُحلَّل: {analysis.input_text}",
        f"║  uid الواقع:   {analysis.reality.uid}",
        "╠══════════════════════════════════════════════════════════╣",
        "║  مراحل الدالة الجامعة:",
        "╠══════════════════════════════════════════════════════════╣",
    ]

    icons = {
        OutputKind.SHAHADA: "✓",
        OutputKind.HYPOTHESIS: "~",
        OutputKind.EPISTEMIC_ZERO: "✗",
    }

    for sr in analysis.stage_results:
        icon = icons.get(sr.output.kind, "?")
        conf_bar = _conf_bar(sr.output.confidence)
        lines.append(
            f"║  [{sr.stage.value:2d}] {STAGE_NAMES_AR[sr.stage]:22s}  "
            f"{icon} [{conf_bar}] {sr.output.confidence:.0%}"
        )
        if sr.output.justification:
            lines.append(
                f"║       ↳ {sr.output.justification[:50]}"
            )

    lines.append("╠══════════════════════════════════════════════════════════╣")

    if analysis.final_output:
        icon = icons.get(analysis.final_output.kind, "?")
        lines.append(
            f"║  النتيجة النهائية: {icon} {analysis.final_output.kind.value}"
            f"  (ثقة: {analysis.final_output.confidence:.0%})"
        )

    lines.append("╚══════════════════════════════════════════════════════════╝")
    return "\n".join(lines)


def format_trace_units(analysis: StagedAnalysis) -> str:
    """
    يُخرِج جدول وحدات يونيكود للأثر.
    """
    if analysis.rich_trace is None:
        return "(لا أثر)"

    lines = [
        f"وحدات يونيكود لـ: {analysis.input_text}",
        f"{'الحرف':^6} {'كود':^8} {'التصنيف':^12} {'الاسم':^20} {'السبب':^20}",
        "-" * 72,
    ]

    for unit in analysis.rich_trace.arabic_text.units:
        lines.append(
            f"{unit.char:^6} {unit.codepoint_str:^8} {unit.kind.value:^12} "
            f"{unit.name_ar:^20} {unit.cause[:18]:^20}"
        )

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# دوال مساعدة
# ---------------------------------------------------------------------------

def _conf_bar(conf: float, width: int = 10) -> str:
    """يُنشئ شريط ثقة نصي."""
    filled = round(conf * width)
    return "█" * filled + "░" * (width - filled)


def _make_serializable(obj: Any) -> Any:
    """يُحوِّل الكائنات غير القابلة للتسلسل JSON إلى أنواع بسيطة."""
    if isinstance(obj, dict):
        return {k: _make_serializable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_make_serializable(i) for i in obj]
    if isinstance(obj, (int, float, str, bool, type(None))):
        return obj
    if isinstance(obj, bytes):
        return obj.hex()
    if isinstance(obj, frozenset):
        return list(obj)
    # الكائنات الأخرى تُحوَّل إلى str
    return str(obj)
