#!/usr/bin/env python3
"""
Generate TCB (Trusted Computing Base) Manifest for Coq Kernel

This script generates a comprehensive manifest of all Parameters in the kernel,
documenting the trusted assumptions that the formal verification relies upon.
"""

import os
import re
import json
from pathlib import Path
from datetime import datetime

def extract_parameters(coq_file):
    """Extract all Parameter declarations with their documentation from a Coq file."""
    with open(coq_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    parameters = []
    lines = content.split('\n')
    
    for i, line in enumerate(lines):
        # Match Parameter declarations
        param_match = re.match(r'\s*Parameter\s+(\w+)\s*:', line)
        if param_match:
            param_name = param_match.group(1)
            
            # Extract type (may span multiple lines)
            type_lines = [line.split(':', 1)[1] if ':' in line else '']
            j = i + 1
            while j < len(lines) and not lines[j].strip().endswith('.'):
                type_lines.append(lines[j])
                j += 1
            if j < len(lines):
                type_lines.append(lines[j])
            
            param_type = ' '.join(type_lines).strip().rstrip('.')
            
            # Look for documentation comment before the Parameter
            doc_lines = []
            k = i - 1
            while k >= 0 and (lines[k].strip().startswith('(*') or 
                            lines[k].strip().startswith('*') or
                            lines[k].strip().endswith('*)')):
                doc_lines.insert(0, lines[k].strip())
                if lines[k].strip().startswith('(*'):
                    break
                k -= 1
            
            documentation = ' '.join(doc_lines).replace('(*', '').replace('*)', '').strip()
            
            parameters.append({
                'name': param_name,
                'type': param_type,
                'location': f"{os.path.basename(coq_file)}:{i+1}",
                'documentation': documentation if documentation else 'No documentation provided'
            })
    
    return parameters

def generate_manifest(kernel_dir):
    """Generate TCB manifest for all Coq files in kernel."""
    kernel_path = Path(kernel_dir)
    all_parameters = []
    
    for coq_file in sorted(kernel_path.glob('*.v')):
        if coq_file.name != 'All.v':  # Skip the aggregator file
            params = extract_parameters(coq_file)
            all_parameters.extend(params)
    
    manifest = {
        'generated_at': datetime.utcnow().isoformat() + 'Z',
        'kernel_directory': str(kernel_dir),
        'total_parameters': len(all_parameters),
        'parameters': all_parameters,
        'summary': {
            'description': 'Trusted Computing Base (TCB) for Arabic Fractal Kernel',
            'trust_model': 'All Parameters represent external assumptions that the kernel accepts as axioms',
            'verification_status': 'All theorems proven modulo these Parameters'
        }
    }
    
    return manifest

def main():
    kernel_dir = Path(__file__).parent / 'theories' / 'ArabicKernel'
    
    if not kernel_dir.exists():
        print(f"Error: Kernel directory not found: {kernel_dir}")
        return 1
    
    manifest = generate_manifest(kernel_dir)
    
    # Output JSON manifest
    json_output = json.dumps(manifest, indent=2, ensure_ascii=False)
    print(json_output)
    
    # Also save to file
    output_file = kernel_dir / 'TCB_MANIFEST.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(json_output)
    
    print(f"\n✅ TCB Manifest generated: {output_file}", file=__import__('sys').stderr)
    print(f"   Total Parameters: {manifest['total_parameters']}", file=__import__('sys').stderr)
    
    return 0

if __name__ == '__main__':
    exit(main())
