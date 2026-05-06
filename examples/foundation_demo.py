#!/usr/bin/env python3
"""
مثال تشغيلي — Foundation Demo
================================
يُوضِّح كيفية استخدام حزمة foundation لتحليل نص عربي
عبر الدالة الجامعة الإحدى عشرية.

التشغيل:
    python examples/foundation_demo.py
    python examples/foundation_demo.py --text "قَرَأَ الطَّالِبُ الدَّرْسَ"
    python examples/foundation_demo.py --text "كِتَابٌ" --level phonemic
    python examples/foundation_demo.py --text "الكِتَابُ مُفِيدٌ" --json

البيئة: PYTHONPATH=src (مُعدَّل في pytest.ini وقابل للتشغيل المباشر)
"""

import sys
import argparse
import json
from pathlib import Path

# تأكد من وجود src في المسار
_repo_root = Path(__file__).parent.parent
_src = _repo_root / "src"
if str(_src) not in sys.path:
    sys.path.insert(0, str(_src))

from foundation import (
    KnowledgeUniverse,
    Reality,
    TraceExtractor,
    AnalysisPipeline,
)
from foundation.ontology import TraceLevel
from foundation.serialization import (
    format_analysis_text,
    format_trace_units,
    serialize_analysis,
)


# ---------------------------------------------------------------------------
# أمثلة جاهزة
# ---------------------------------------------------------------------------

DEMO_EXAMPLES = [
    "الكِتَابُ مُفِيدٌ",
    "قَرَأَ الطَّالِبُ الدَّرْسَ",
    "لَا إِلَهَ إِلَّا اللَّهُ",
    "بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ",
]

LEVEL_MAP = {
    "surface": TraceLevel.SURFACE,
    "phonemic": TraceLevel.PHONEMIC,
    "morphemic": TraceLevel.MORPHEMIC,
    "full": TraceLevel.FULL,
}


# ---------------------------------------------------------------------------
# تشغيل مثال واحد
# ---------------------------------------------------------------------------

def run_example(
    text: str,
    level: TraceLevel = TraceLevel.SURFACE,
    output_json: bool = False,
    show_units: bool = False,
) -> None:
    print(f"\n{'='*64}")
    print(f"  النص: {text}")
    print(f"  المستوى: {level.value}")
    print("=" * 64)

    # --- 1. الكون المعرفي ---
    omega = KnowledgeUniverse()
    reality = Reality(raw_text=text)
    omega.register(reality)
    trace = omega.apply_trace_fn(reality)

    print(f"\n[Ω] الكون المعرفي: {omega}")
    print(f"[R] الواقع:        {reality}")
    print(f"[T] الأثر:         {trace}")

    # --- 2. تحليل يونيكود ---
    if show_units:
        extractor = TraceExtractor()
        rich_trace = extractor.extract(reality, level)
        print(f"\n{format_trace_units.__module__}")
        print(format_trace_units.__doc__ or "")
        from foundation.serialization import format_trace_units as _fmt
        print(_fmt.__doc__ or "")
        print("\n" + "─" * 64)
        from foundation.unicode_units import ArabicText
        at = ArabicText.from_string(text)
        print(f"{'الحرف':^6} {'كود':^8} {'نوع':^12} {'اسم':^18} {'سبب':^18}")
        print("─" * 64)
        for unit in at.units:
            print(
                f"{unit.char:^6} {unit.codepoint_str:^8} {unit.kind.value:^12} "
                f"{unit.name_ar:^18} {unit.cause[:16]:^18}"
            )

    # --- 3. الدالة الجامعة ---
    pipeline = AnalysisPipeline(trace_level=level)
    analysis = pipeline.run(text)

    if output_json:
        print("\n[JSON Output]")
        print(serialize_analysis(analysis, indent=2))
    else:
        print("\n" + format_analysis_text(analysis))

    # --- 4. ملخص المخرجات ---
    print(f"\n[إحصاء] الشهادات={len(analysis.outputs.shahadas())} | "
          f"الفرضيات={len(analysis.outputs.hypotheses())} | "
          f"الصفريات={len(analysis.outputs.zeros())}")


# ---------------------------------------------------------------------------
# تشغيل جميع الأمثلة
# ---------------------------------------------------------------------------

def run_all_examples() -> None:
    print("╔══════════════════════════════════════════════════════════╗")
    print("║   حزمة الأساس الرياضي v0.1 — Foundation Package Demo     ║")
    print("║   «الوثيقة الرياضية التأسيسية للعقل الباني»             ║")
    print("╚══════════════════════════════════════════════════════════╝")

    for text in DEMO_EXAMPLES:
        run_example(text)
        print()

    print("\n✓ انتهت جميع الأمثلة بنجاح.")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="تشغيل الدالة الجامعة على نص عربي"
    )
    parser.add_argument(
        "--text", "-t",
        default=None,
        help="النص العربي المُراد تحليله (إذا لم يُعطَ تُشغَّل الأمثلة الجاهزة)",
    )
    parser.add_argument(
        "--level", "-l",
        default="surface",
        choices=list(LEVEL_MAP.keys()),
        help="مستوى التحليل (افتراضي: surface)",
    )
    parser.add_argument(
        "--json", "-j",
        action="store_true",
        help="إخراج JSON بدلاً من النص المُنسَّق",
    )
    parser.add_argument(
        "--units", "-u",
        action="store_true",
        help="عرض جدول وحدات يونيكود",
    )

    args = parser.parse_args()

    level = LEVEL_MAP[args.level]

    if args.text:
        run_example(args.text, level=level, output_json=args.json, show_units=args.units)
    else:
        run_all_examples()


if __name__ == "__main__":
    main()
