"""
Minimal CLI for FVAFK pipeline.

Usage:
    python -m fvafk.cli "كِتَابٌ" --json
    python -m fvafk.cli "كَاتِبٌ" --morphology --json
    python -m fvafk.cli "text" --verbose
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from typing import Any, Dict, List, Optional

from fvafk.c1 import C1Encoder
from fvafk.c1.unit import Unit, UnitCategory
from fvafk.c2a import (
    GateDeletion,
    GateEpenthesis,
    GateFramework,
    GateHamza,
    GateIdgham,
    GateMadd,
    GateShadda,
    GateSukun,
    GateWaqf,
)
from fvafk.c2a.gate_framework import GateOrchestrator, GateResult, PhonologicalGate
from fvafk.c2a.syllable import Segment
from fvafk.c2b import PatternMatcher, RootExtractor
from fvafk.c2b.morpheme import PatternType, Root, RootType


class MinimalCLI:
    """
    Minimal command-line interface for FVAFK.

    Runs the full pipeline: C1 (encoding) → C2a (phonology) → C2b (morphology)
    """

    def __init__(self, verbose: bool = False, json_output: bool = False) -> None:
        """Initialize CLI with encoder and gate orchestrator."""
        self.c1_encoder = C1Encoder()
        self._verbose_default = verbose
        self._json_output_default = json_output

        gates = [
            GateSukun(),
            GateShadda(),
            GateHamza(),
            GateWaqf(),
            GateIdgham(),
            GateMadd(),
            GateDeletion(),
            GateEpenthesis(),
        ]

        self.orchestrator = GateOrchestrator(gates=gates)

    def run(
        self,
        text: str,
        verbose: bool = False,
        morphology: bool = False,
        multi_word: bool = False
    ) -> Dict[str, Any]:
        """Run full FVAFK pipeline."""
        start = time.perf_counter()

        c1_start = time.perf_counter()
        segments = self.c1_encoder.encode(text)
        c1_time = (time.perf_counter() - c1_start) * 1000

        c2a_start = time.perf_counter()
        final_segments, gate_results = self.orchestrator.run(segments)
        paired_gate_results = list(
            zip(self.orchestrator.gates[: len(gate_results)], gate_results)
        )

        syllable_count = self._count_syllables(final_segments)
        c2a_time = (time.perf_counter() - c2a_start) * 1000

        morphology_result: Optional[Dict[str, Any]] = None
        c2b_time = 0.0

        if morphology:
            c2b_start = time.perf_counter()
            if multi_word:
                morphology_result = self._analyze_morphology_multi_word(text)
            else:
                morphology_result = self._analyze_morphology(text)
            c2b_time = (time.perf_counter() - c2b_start) * 1000

        total_time = (time.perf_counter() - start) * 1000

        unit_rows = [self._segment_to_unit(s) for s in segments]

        result: Dict[str, Any] = {
            "input": text,
            "success": True,
            "c1": {
                "num_units": len(unit_rows),
                "units": [self._unit_to_dict(u) for u in unit_rows] if verbose else None,
            },
            "c2a": {
                "gates": [
                    self._gate_result_to_dict(gate, gr)
                    for gate, gr in paired_gate_results
                ],
                "syllables": {
                    "count": syllable_count,
                    "syllables": None,
                },
            },
            "stats": {
                "c1_time_ms": c1_time,
                "c2a_time_ms": c2a_time,
                "c2b_time_ms": c2b_time if morphology else None,
                "total_time_ms": total_time,
                "gates_count": len(paired_gate_results),
            },
        }

        if morphology_result:
            result["c2b"] = morphology_result

        return result

    def process(self, text: str) -> Dict[str, Any]:
        """Backward-compatible `process` entry point from legacy CLI."""
        return self.run(text=text, verbose=self._verbose_default)

    def _segment_to_unit(self, segment: Segment) -> Unit:
        from fvafk.c2a.syllable import SegmentKind

        category = UnitCategory.LETTER
        if segment.kind == SegmentKind.VOWEL:
            category = UnitCategory.DIAC
        return Unit(text=segment.text, category=category)

    def _analyze_morphology(self, text: str) -> Dict[str, Any]:
        root_extractor = RootExtractor()
        root = root_extractor.extract(text)

        if not root:
            return {
                "root": None,
                "pattern": None,
                "error": "Could not extract root from input text"
            }

        letters = list(root.letters)
        root_type = root.root_type
        if len(letters) == 4 and letters[1] == letters[2]:
            letters = [letters[0], letters[1], letters[3]]
            root_type = RootType.TRILATERAL

        analysis_root = Root(letters=tuple(letters), root_type=root_type)
        pattern_matcher = PatternMatcher()
        pattern = pattern_matcher.match(text, analysis_root)

        result: Dict[str, Any] = {
            "root": {
                "letters": letters,
                "formatted": "-".join(letters),
                "type": root_type.name.lower(),
                "length": len(letters),
            }
        }

        if pattern:
            result["pattern"] = {
                "template": pattern.template,
                "type": pattern.pattern_type.value,
                "category": self._get_pattern_category(pattern.pattern_type),
                "stem": pattern.stem,
            }
        else:
            result["pattern"] = {
                "template": None,
                "type": "unknown",
                "category": "unknown",
                "error": "Could not match pattern"
            }

        return result

    def _analyze_morphology_multi_word(self, text: str) -> Dict[str, Any]:
        """تحليل نص متعدد الكلمات - يستخرج الجذر لكل كلمة."""
        import re
        
        # تقسيم النص إلى كلمات (حذف علامات الترقيم والرموز)
        words = re.findall(r'[\u0600-\u06FF]+', text)
        
        root_extractor = RootExtractor()
        pattern_matcher = PatternMatcher()
        
        words_analysis: List[Dict[str, Any]] = []
        
        for word in words:
            if not word or len(word) < 2:
                continue
                
            root = root_extractor.extract(word)
            
            if not root:
                words_analysis.append({
                    "word": word,
                    "root": None,
                    "pattern": None,
                    "error": "Could not extract root"
                })
                continue
            
            letters = list(root.letters)
            root_type = root.root_type
            
            # معالجة الجذور الرباعية المضعفة
            if len(letters) == 4 and letters[1] == letters[2]:
                letters = [letters[0], letters[1], letters[3]]
                root_type = RootType.TRILATERAL
            
            analysis_root = Root(letters=tuple(letters), root_type=root_type)
            pattern = pattern_matcher.match(word, analysis_root)
            
            word_result: Dict[str, Any] = {
                "word": word,
                "root": {
                    "letters": letters,
                    "formatted": "-".join(letters),
                    "type": root_type.name.lower(),
                    "length": len(letters),
                }
            }
            
            if pattern:
                word_result["pattern"] = {
                    "template": pattern.template,
                    "type": pattern.pattern_type.value,
                    "category": self._get_pattern_category(pattern.pattern_type),
                }
            else:
                word_result["pattern"] = {
                    "template": None,
                    "type": "unknown",
                    "category": "unknown",
                }
            
            words_analysis.append(word_result)
        
        return {
            "words_count": len(words_analysis),
            "words": words_analysis
        }

    def _get_pattern_category(self, pattern_type: PatternType) -> str:
        verb_forms = {
            PatternType.FORM_I,
            PatternType.FORM_II,
            PatternType.FORM_III,
            PatternType.FORM_IV,
            PatternType.FORM_V,
            PatternType.FORM_VI,
            PatternType.FORM_VII,
            PatternType.FORM_VIII,
            PatternType.FORM_IX,
            PatternType.FORM_X,
        }

        if pattern_type in verb_forms:
            return "verb"

        if "PLURAL" in pattern_type.value.upper():
            return "plural"

        return "noun"

    def _count_syllables(self, segments: List[Segment]) -> int:
        from fvafk.c2a.syllable import SegmentKind

        count = 0
        for seg in segments:
            if seg.kind == SegmentKind.VOWEL:
                count += 1
        return count

    def _unit_to_dict(self, unit: Unit) -> Dict[str, Any]:
        return {
            "text": unit.text,
            "category": unit.category.name if unit.category else None,
        }

    def _gate_result_to_dict(self, gate: PhonologicalGate, gate_result: GateResult) -> Dict[str, Any]:
        return {
            "gate_id": gate.gate_id,
            "status": gate_result.status.name,
            "time_ms": gate_result.latency_ms,
            "deltas": len(gate_result.deltas),
            "reason": gate_result.reason,
        }


def _print_human_readable(result: Dict[str, Any]) -> None:
    print(f"\n{'='*70}")
    print(f"  FVAFK Analysis: {result['input']}")
    print(f"{'='*70}\n")

    print(f"📝 Phase C1 (Encoding):")
    print(f"   Units: {result['c1']['num_units']}")
    print(f"   Time:  {result['stats']['c1_time_ms']:.3f}ms\n")

    print(f"🔊 Phase C2a (Phonology):")
    print(f"   Syllables: {result['c2a']['syllables']['count']}")
    print(f"   Gates:     {result['stats']['gates_count']}")

    modified_gates = [
        g for g in result['c2a']['gates']
        if g['status'] == 'REPAIR' and g['deltas'] > 0
    ]

    if modified_gates:
        print(f"   Modified by:")
        for gate in modified_gates:
            print(f"      • {gate['gate_id']}: {gate['deltas']} change(s)")

    print(f"   Time:  {result['stats']['c2a_time_ms']:.3f}ms\n")

    if 'c2b' in result:
        print(f"📖 Phase C2b (Morphology):")
        morph = result['c2b']

        if morph.get('root'):
            root = morph['root']
            print(f"   Root:    {root['formatted']} ({root['type']}, {root['length']} letters)")
        else:
            print(f"   Root:    Could not extract")

        if morph.get('pattern') and morph['pattern'].get('template'):
            pat = morph['pattern']
            print(f"   Pattern: {pat['template']}")
            print(f"   Type:    {pat['type']} ({pat['category']})")
        else:
            print(f"   Pattern: Could not match")

        if result['stats']['c2b_time_ms']:
            print(f"   Time:    {result['stats']['c2b_time_ms']:.3f}ms\n")

    print(f"⏱️  Performance Summary:")
    print(f"   Total:  {result['stats']['total_time_ms']:.3f}ms")

    breakdown = [
        f"C1: {result['stats']['c1_time_ms']:.1f}ms",
        f"C2a: {result['stats']['c2a_time_ms']:.1f}ms",
    ]
    if result['stats'].get('c2b_time_ms'):
        breakdown.append(f"C2b: {result['stats']['c2b_time_ms']:.1f}ms")

    print(f"   Breakdown: {' + '.join(breakdown)}")
    print(f"\n{'='*70}\n")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="FVAFK: Arabic phonological and morphological analysis",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python -m fvafk.cli "كِتَابٌ" --json
  python -m fvafk.cli "كَاتِبٌ" --morphology --json
  python -m fvafk.cli "text" --verbose --json
  python -m fvafk.cli "مُحَمَّدٌ رَسُولُ اللَّهِ" --morphology --multi-word --json
        """
    )

    parser.add_argument("text", help="Arabic text to analyze")
    parser.add_argument("--verbose", action="store_true", help="Include detailed unit and segment information")
    parser.add_argument("--json", action="store_true", help="Output results as JSON (default: human-readable)")
    parser.add_argument("--morphology", action="store_true", help="Include morphological analysis (root extraction + pattern matching)")
    parser.add_argument("--multi-word", action="store_true", help="Analyze each word separately in multi-word text (requires --morphology)")

    args = parser.parse_args()

    try:
        cli = MinimalCLI()
        result = cli.run(
            text=args.text,
            verbose=args.verbose,
            morphology=args.morphology,
            multi_word=getattr(args, 'multi_word', False)
        )

        if args.json:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        else:
            _print_human_readable(result)

        sys.exit(0)

    except Exception as e:
        error_result = {
            "success": False,
            "error": str(e),
            "input": args.text
        }

        if args.json:
            print(json.dumps(error_result, ensure_ascii=False, indent=2))
        else:
            print(f"Error: {e}", file=sys.stderr)

        sys.exit(1)


if __name__ == "__main__":
    main()
