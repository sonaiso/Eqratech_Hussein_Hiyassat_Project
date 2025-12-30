#!/usr/bin/env python3
"""
Comment-Aware Admitted/Axiom Scanner for Coq Kernel

This script provides robust detection of Admitted and Axiom declarations,
ignoring instances that appear only in comments or documentation.
"""

import os
import re
import sys
from pathlib import Path

class CoqScanner:
    """Scanner that understands Coq comment syntax."""
    
    def __init__(self, content):
        self.content = content
        self.lines = content.split('\n')
        self.in_comment = False
        self.comment_depth = 0
    
    def is_in_comment(self, pos):
        """Check if a position in the content is inside a comment."""
        # Build comment ranges
        comment_ranges = []
        i = 0
        while i < len(self.content):
            if self.content[i:i+2] == '(*':
                start = i
                depth = 1
                i += 2
                while i < len(self.content) and depth > 0:
                    if self.content[i:i+2] == '(*':
                        depth += 1
                        i += 2
                    elif self.content[i:i+2] == '*)':
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                comment_ranges.append((start, i))
            else:
                i += 1
        
        # Check if position is in any comment range
        for start, end in comment_ranges:
            if start <= pos < end:
                return True
        return False
    
    def find_all(self, pattern):
        """Find all matches of pattern that are NOT in comments."""
        results = []
        for match in re.finditer(pattern, self.content):
            if not self.is_in_comment(match.start()):
                line_num = self.content[:match.start()].count('\n') + 1
                results.append({
                    'match': match.group(0),
                    'line': line_num,
                    'position': match.start()
                })
        return results

def check_file(filepath):
    """Check a single Coq file for Admitted/Axiom outside comments."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    scanner = CoqScanner(content)
    
    # Find Admitted statements (must be followed by '.')
    admitted_pattern = r'\bAdmitted\s*\.'
    admitted_list = scanner.find_all(admitted_pattern)
    
    # Find Axiom declarations
    axiom_pattern = r'\bAxiom\s+\w+'
    axiom_list = scanner.find_all(axiom_pattern)
    
    return admitted_list, axiom_list

def scan_kernel(kernel_dir):
    """Scan all Coq files in kernel directory."""
    kernel_path = Path(kernel_dir)
    results = {
        'admitted': {},
        'axiom': {},
        'total_admitted': 0,
        'total_axiom': 0
    }
    
    for coq_file in sorted(kernel_path.glob('*.v')):
        admitted, axiom = check_file(coq_file)
        
        if admitted:
            results['admitted'][str(coq_file.name)] = admitted
            results['total_admitted'] += len(admitted)
        
        if axiom:
            results['axiom'][str(coq_file.name)] = axiom
            results['total_axiom'] += len(axiom)
    
    return results

def main():
    kernel_dir = Path(__file__).parent / 'theories' / 'ArabicKernel'
    
    if not kernel_dir.exists():
        print(f"❌ Error: Kernel directory not found: {kernel_dir}")
        return 1
    
    print("🔍 Scanning Coq kernel for Admitted/Axiom (comment-aware)...")
    results = scan_kernel(kernel_dir)
    
    # Report findings
    has_issues = False
    
    if results['total_admitted'] > 0:
        has_issues = True
        print(f"\n❌ Found {results['total_admitted']} Admitted statement(s):")
        for filename, items in results['admitted'].items():
            for item in items:
                print(f"   {filename}:{item['line']}: {item['match']}")
    else:
        print("\n✅ No Admitted statements found in production code")
    
    if results['total_axiom'] > 0:
        has_issues = True
        print(f"\n❌ Found {results['total_axiom']} Axiom declaration(s):")
        for filename, items in results['axiom'].items():
            for item in items:
                print(f"   {filename}:{item['line']}: {item['match']}")
    else:
        print("\n✅ No Axiom declarations found in production code")
    
    if has_issues:
        print("\n❌ Kernel contains undeclared assumptions!")
        print("   All assumptions must be declared as Parameters with documentation.")
        return 1
    else:
        print("\n✅ Kernel is sound: 0 Admitted, 0 Axiom")
        return 0

if __name__ == '__main__':
    exit(main())
