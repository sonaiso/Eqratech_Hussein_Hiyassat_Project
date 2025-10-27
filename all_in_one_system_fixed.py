#!/usr/bin/env python3
"""
Unified CLI for Eqratech Arabic Diana Project

This module provides a command-line interface with two main subcommands:
1. phonetics - Run comprehensive phonetics analysis on Arabic text
2. export-grammar - Export the multilayer grammar workbook
"""

import argparse
import sys
import os
import json
import re
from typing import Optional, Dict, List, Any
import pandas as pd


def analyze_text_phonetics(text: str) -> Dict[str, Any]:
    """
    Analyze Arabic text for phonetic properties.
    
    Returns a dictionary with:
    - text: original text
    - words: list of words with their analysis
    - syllables: syllable breakdown
    - phonemes: phoneme analysis
    - harakat: diacritical marks analysis
    """
    from phonemes_engine import PhonemesEngine
    
    # Load phoneme data
    try:
        phoneme_df = PhonemesEngine.make_df_from_csv()
    except Exception as e:
        print(f"Warning: Could not load phoneme data: {e}", file=sys.stderr)
        phoneme_df = pd.DataFrame()
    
    # Split text into words
    words = text.strip().split()
    
    # Analyze each word
    word_analyses = []
    total_phonemes = 0
    total_harakat = 0
    
    # Arabic letter pattern
    LETTER_PATTERN = re.compile(r'[\u0621-\u064A\u0660-\u0669]')
    HARAKA_PATTERN = re.compile(r'[\u064B-\u0652\u0670]')
    
    for word in words:
        if not word:
            continue
            
        # Extract letters (phonemes) and harakat
        letters = [ch for ch in word if LETTER_PATTERN.match(ch)]
        harakat = [ch for ch in word if HARAKA_PATTERN.match(ch)]
        
        # Simple syllable detection (basic implementation)
        syllables = []
        current_syllable = ""
        for i, ch in enumerate(word):
            current_syllable += ch
            # Simple heuristic: syllable ends with haraka or is final letter
            if HARAKA_PATTERN.match(ch) or i == len(word) - 1:
                if current_syllable.strip():
                    syllables.append(current_syllable)
                current_syllable = ""
        
        word_analysis = {
            'word': word,
            'letters': letters,
            'letter_count': len(letters),
            'harakat': harakat,
            'harakat_count': len(harakat),
            'syllables': syllables,
            'syllable_count': len(syllables)
        }
        word_analyses.append(word_analysis)
        total_phonemes += len(letters)
        total_harakat += len(harakat)
    
    return {
        'text': text,
        'word_count': len(words),
        'total_phonemes': total_phonemes,
        'total_harakat': total_harakat,
        'words': word_analyses
    }


def analyze_quran_file(filepath: str, max_chars: Optional[int] = None) -> Dict[str, Any]:
    """
    Analyze text from a Quran file.
    
    Args:
        filepath: Path to the Quran text file
        max_chars: Maximum characters to process (for limiting analysis)
    
    Returns:
        Analysis results dictionary
    """
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"Quran file not found: {filepath}")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        text = f.read()
    
    if max_chars:
        text = text[:max_chars]
    
    return analyze_text_phonetics(text)


def format_report_pretty(analysis: Dict[str, Any]) -> str:
    """Format analysis results as a pretty text report."""
    lines = []
    lines.append("=" * 70)
    lines.append("  ARABIC PHONETICS ANALYSIS REPORT")
    lines.append("=" * 70)
    lines.append(f"\nOriginal Text: {analysis['text'][:100]}{'...' if len(analysis['text']) > 100 else ''}")
    lines.append(f"\nStatistics:")
    lines.append(f"  - Total Words: {analysis['word_count']}")
    lines.append(f"  - Total Phonemes (Letters): {analysis['total_phonemes']}")
    lines.append(f"  - Total Harakat (Diacritics): {analysis['total_harakat']}")
    lines.append(f"\nWord Analysis:")
    lines.append("-" * 70)
    
    for i, word in enumerate(analysis['words'][:10], 1):  # Show first 10 words
        lines.append(f"\n{i}. Word: {word['word']}")
        lines.append(f"   Letters: {' '.join(word['letters'])} (count: {word['letter_count']})")
        lines.append(f"   Harakat: {' '.join(word['harakat'])} (count: {word['harakat_count']})")
        lines.append(f"   Syllables: {len(word['syllables'])} detected")
    
    if len(analysis['words']) > 10:
        lines.append(f"\n... and {len(analysis['words']) - 10} more words")
    
    lines.append("\n" + "=" * 70)
    return "\n".join(lines)


def format_report_markdown(analysis: Dict[str, Any]) -> str:
    """Format analysis results as Markdown."""
    lines = []
    lines.append("# Arabic Phonetics Analysis Report\n")
    lines.append(f"**Original Text:** {analysis['text'][:100]}{'...' if len(analysis['text']) > 100 else ''}\n")
    lines.append("## Statistics\n")
    lines.append(f"- **Total Words:** {analysis['word_count']}")
    lines.append(f"- **Total Phonemes (Letters):** {analysis['total_phonemes']}")
    lines.append(f"- **Total Harakat (Diacritics):** {analysis['total_harakat']}\n")
    lines.append("## Word Analysis\n")
    
    for i, word in enumerate(analysis['words'][:10], 1):
        lines.append(f"### {i}. {word['word']}\n")
        lines.append(f"- **Letters:** {' '.join(word['letters'])} (count: {word['letter_count']})")
        lines.append(f"- **Harakat:** {' '.join(word['harakat'])} (count: {word['harakat_count']})")
        lines.append(f"- **Syllables:** {len(word['syllables'])} detected\n")
    
    if len(analysis['words']) > 10:
        lines.append(f"*... and {len(analysis['words']) - 10} more words*\n")
    
    return "\n".join(lines)


def export_to_csv(analysis: Dict[str, Any], csv_path: str):
    """Export word/syllable summary to CSV."""
    rows = []
    for word_data in analysis['words']:
        rows.append({
            'Word': word_data['word'],
            'Letters': ' '.join(word_data['letters']),
            'Letter_Count': word_data['letter_count'],
            'Harakat': ' '.join(word_data['harakat']),
            'Harakat_Count': word_data['harakat_count'],
            'Syllable_Count': word_data['syllable_count']
        })
    
    df = pd.DataFrame(rows)
    df.to_csv(csv_path, index=False, encoding='utf-8-sig')
    print(f"CSV exported to: {csv_path}")


def cmd_phonetics(args):
    """Handle the phonetics subcommand."""
    # Determine source of text
    if args.text:
        analysis = analyze_text_phonetics(args.text)
    elif args.quran_file:
        analysis = analyze_quran_file(args.quran_file, args.max_chars)
    else:
        print("Error: Either --text or --quran_file must be provided", file=sys.stderr)
        return 1
    
    # Generate report in requested format
    if args.report == 'pretty':
        print(format_report_pretty(analysis))
    elif args.report == 'md':
        print(format_report_markdown(analysis))
    elif args.report == 'json':
        print(json.dumps(analysis, ensure_ascii=False, indent=2))
    else:
        print(f"Unknown report format: {args.report}", file=sys.stderr)
        return 1
    
    # Export CSV if requested
    if args.csv:
        export_to_csv(analysis, args.csv)
    
    return 0


def cmd_export_grammar(args):
    """Handle the export-grammar subcommand."""
    output_path = args.output or "full_multilayer_grammar.xlsx"
    
    print(f"Exporting multilayer grammar to: {output_path}")
    print("This may take several minutes as it processes all grammar engines...")
    
    # Import and run the export functionality
    try:
        from export_full_multilayer_grammar_minimal import main as export_main
        
        # Temporarily override the output path if specified
        if args.output:
            # The export script writes to a hardcoded filename, so we'll rename it after
            export_main()
            import shutil
            if os.path.exists("full_multilayer_grammar.xlsx") and args.output != "full_multilayer_grammar.xlsx":
                shutil.move("full_multilayer_grammar.xlsx", args.output)
                print(f"\nGrammar workbook successfully exported to: {args.output}")
        else:
            export_main()
            print(f"\nGrammar workbook successfully exported to: full_multilayer_grammar.xlsx")
        
        return 0
    except ImportError as e:
        print(f"Error: Missing required module for grammar export: {e}", file=sys.stderr)
        print("Some engine modules may be missing. Please ensure all dependencies are available.", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error exporting grammar: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


def main():
    """Main entry point for the CLI."""
    parser = argparse.ArgumentParser(
        description="Unified CLI for Eqratech Arabic Diana Project",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze inline text with pretty report
  python all_in_one_system_fixed.py phonetics --text "الطَّالِبُ الْمُجْتَهِدُ يَدْرُسُ فِي الْجَامِعَةِ." --report pretty
  
  # Analyze Quran file with Markdown report
  python all_in_one_system_fixed.py phonetics --quran_file quran.txt --report md --max_chars 6000
  
  # Export grammar workbook
  python all_in_one_system_fixed.py export-grammar --output my_grammar.xlsx
        """
    )
    
    subparsers = parser.add_subparsers(dest='command', help='Available commands')
    
    # Phonetics subcommand
    phonetics_parser = subparsers.add_parser(
        'phonetics',
        help='Run comprehensive phonetics pipeline on Arabic text'
    )
    phonetics_parser.add_argument(
        '--text',
        type=str,
        help='Inline Arabic text to analyze'
    )
    phonetics_parser.add_argument(
        '--quran_file',
        type=str,
        help='Path to Quran text file to analyze'
    )
    phonetics_parser.add_argument(
        '--report',
        type=str,
        choices=['pretty', 'md', 'json'],
        default='pretty',
        help='Report format (default: pretty)'
    )
    phonetics_parser.add_argument(
        '--max_chars',
        type=int,
        help='Maximum characters to process from file'
    )
    phonetics_parser.add_argument(
        '--csv',
        type=str,
        help='Export word/syllable summary to CSV file'
    )
    
    # Export-grammar subcommand
    export_parser = subparsers.add_parser(
        'export-grammar',
        help='Export multilayer grammar workbook'
    )
    export_parser.add_argument(
        '--output',
        type=str,
        help='Output Excel file path (default: full_multilayer_grammar.xlsx)'
    )
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return 1
    
    # Dispatch to appropriate handler
    if args.command == 'phonetics':
        return cmd_phonetics(args)
    elif args.command == 'export-grammar':
        return cmd_export_grammar(args)
    else:
        print(f"Unknown command: {args.command}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
