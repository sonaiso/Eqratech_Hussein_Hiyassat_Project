#!/usr/bin/env python3
"""
Coq Tactic Policy Checker for CI

This script checks that only allowed tactics are used in Coq proofs.
It fails the build if forbidden tactics are detected.

Usage:
    python check_coq_tactics.py [--dir coq/theories]
    
Exit codes:
    0: All checks passed
    1: Forbidden tactics found
    2: Error in execution
"""

import os
import re
import sys
import argparse
from pathlib import Path
from typing import List, Tuple, Set


# Tactics that are ALLOWED in kernel proofs
ALLOWED_TACTICS = {
    'exact', 'apply', 'intro', 'intros', 'split',
    'left', 'right', 'exists', 'reflexivity', 'simpl',
    'unfold', 'induction', 'destruct', 'rewrite', 'assumption',
    'constructor', 'discriminate', 'injection', 'inversion'
}

# Tactics that are FORBIDDEN (too opaque or unsound)
FORBIDDEN_TACTICS = {
    'auto', 'tauto', 'omega', 'lia', 'ring', 'field',
    'admit', 'give_up', 'Admitted'
}

# Additional tactics to warn about (not forbidden but discouraged)
DISCOURAGED_TACTICS = {
    'eauto', 'trivial', 'firstorder', 'congruence'
}


class TacticViolation:
    """Represents a violation of the tactic policy"""
    
    def __init__(self, filepath: str, line_num: int, tactic: str, 
                 line_content: str, severity: str = 'error'):
        self.filepath = filepath
        self.line_num = line_num
        self.tactic = tactic
        self.line_content = line_content.strip()
        self.severity = severity
    
    def __str__(self):
        return (f"{self.severity.upper()}: {self.filepath}:{self.line_num}: "
                f"Forbidden tactic '{self.tactic}' used\n"
                f"  Line: {self.line_content}")


def extract_tactics_from_line(line: str) -> List[str]:
    """
    Extract tactics from a line of Coq code.
    Returns list of tactic names found.
    """
    # Remove comments
    line = re.sub(r'\(\*.*?\*\)', '', line)
    
    # Match tactic keywords (word boundaries)
    tactics = []
    
    # Check for each tactic
    all_tactics = ALLOWED_TACTICS | FORBIDDEN_TACTICS | DISCOURAGED_TACTICS
    for tactic in all_tactics:
        # Use word boundaries to match exact tactic names
        pattern = r'\b' + re.escape(tactic) + r'\b'
        if re.search(pattern, line, re.IGNORECASE):
            tactics.append(tactic.lower())
    
    return tactics


def check_coq_file(filepath: Path) -> List[TacticViolation]:
    """
    Check a single Coq file for tactic policy violations.
    Returns list of violations found.
    """
    violations = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        in_proof = False
        in_comment = False
        
        for line_num, line in enumerate(lines, start=1):
            # Track multi-line comments
            # Note: This is a simplified check, doesn't handle nested comments
            original_line = line
            temp_line = line
            
            # Remove single-line comments and parts of multi-line comments
            while '(*' in temp_line or '*)' in temp_line:
                if '(*' in temp_line and '*)' in temp_line:
                    # Both on same line
                    start = temp_line.find('(*')
                    end = temp_line.find('*)', start) + 2
                    temp_line = temp_line[:start] + temp_line[end:]
                elif '(*' in temp_line:
                    # Start of multi-line comment
                    in_comment = True
                    temp_line = temp_line[:temp_line.find('(*')]
                    break
                elif '*)' in temp_line:
                    # End of multi-line comment
                    in_comment = False
                    temp_line = temp_line[temp_line.find('*)') + 2:]
                else:
                    break
            
            # Skip if we're inside a multi-line comment
            if in_comment:
                continue
            
            line = temp_line
            
            # Track if we're in a proof
            if re.search(r'\bProof\b', line):
                in_proof = True
            if re.search(r'\b(Qed|Defined|Abort)\b', line):
                in_proof = False
            
            # Only check tactics within proofs
            if not in_proof:
                continue
            
            # Extract tactics from line (comments already removed)
            tactics = extract_tactics_from_line(line)
            
            # Check for forbidden tactics
            for tactic in tactics:
                if tactic in FORBIDDEN_TACTICS:
                    violations.append(TacticViolation(
                        str(filepath), line_num, tactic, original_line, 'error'
                    ))
                elif tactic in DISCOURAGED_TACTICS:
                    violations.append(TacticViolation(
                        str(filepath), line_num, tactic, original_line, 'warning'
                    ))
    
    except Exception as e:
        print(f"Error reading {filepath}: {e}", file=sys.stderr)
    
    return violations


def check_directory(directory: Path) -> Tuple[List[TacticViolation], List[TacticViolation]]:
    """
    Check all .v files in a directory recursively.
    Returns (errors, warnings) tuple.
    """
    errors = []
    warnings = []
    
    # Find all .v files
    v_files = list(directory.rglob('*.v'))
    
    if not v_files:
        print(f"Warning: No .v files found in {directory}", file=sys.stderr)
        return errors, warnings
    
    print(f"Checking {len(v_files)} Coq files...")
    
    for filepath in v_files:
        violations = check_coq_file(filepath)
        for v in violations:
            if v.severity == 'error':
                errors.append(v)
            else:
                warnings.append(v)
    
    return errors, warnings


def main():
    parser = argparse.ArgumentParser(
        description='Check Coq files for tactic policy violations'
    )
    parser.add_argument(
        '--dir',
        type=str,
        default='coq/theories',
        help='Directory to check (default: coq/theories)'
    )
    parser.add_argument(
        '--strict',
        action='store_true',
        help='Treat warnings as errors'
    )
    parser.add_argument(
        '--list-allowed',
        action='store_true',
        help='List allowed tactics and exit'
    )
    
    args = parser.parse_args()
    
    if args.list_allowed:
        print("Allowed tactics:")
        for tactic in sorted(ALLOWED_TACTICS):
            print(f"  - {tactic}")
        print("\nForbidden tactics:")
        for tactic in sorted(FORBIDDEN_TACTICS):
            print(f"  - {tactic}")
        print("\nDiscouraged tactics (warnings):")
        for tactic in sorted(DISCOURAGED_TACTICS):
            print(f"  - {tactic}")
        return 0
    
    # Check directory
    directory = Path(args.dir)
    if not directory.exists():
        print(f"Error: Directory {directory} does not exist", file=sys.stderr)
        return 2
    
    errors, warnings = check_directory(directory)
    
    # Report results
    if warnings:
        print(f"\n⚠️  Found {len(warnings)} warning(s):")
        for w in warnings:
            print(f"  {w}")
    
    if errors:
        print(f"\n❌ Found {len(errors)} error(s):")
        for e in errors:
            print(f"  {e}")
        print("\nBuild FAILED: Forbidden tactics detected!")
        print("Please use only allowed tactics as defined in Policy.v")
        return 1
    
    if args.strict and warnings:
        print("\n❌ Build FAILED: Warnings treated as errors (--strict mode)")
        return 1
    
    if not errors and not warnings:
        print("✅ All checks passed! No forbidden tactics found.")
    elif not errors:
        print(f"✅ Checks passed with {len(warnings)} warning(s)")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
