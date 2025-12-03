#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Extract Epistemological Roots from Quran
Roots: فهم (understand), علم (know), وعى (aware), بصر (see/perceive), نظر (observe)
"""

import re
import csv
from collections import defaultdict

def remove_diacritics(text):
    """Remove Arabic diacritics from text"""
    arabic_diacritics = re.compile("""
                             ّ    | # Tashdid
                             َ    | # Fatha
                             ً    | # Tanwin Fath
                             ُ    | # Damma
                             ٌ    | # Tanwin Damm
                             ِ    | # Kasra
                             ٍ    | # Tanwin Kasr
                             ْ    | # Sukun
                             ـ     # Tatwil/Kashida
                         """, re.VERBOSE)
    return re.sub(arabic_diacritics, '', text)

def load_quran(filename='quran-simple-enhanced.txt'):
    """Load Quran text from file"""
    with open(filename, 'r', encoding='utf-8') as f:
        verses = f.read().strip().split('\n')
    return verses

def extract_epistemological_roots(verses):
    """Extract epistemological roots with all their forms"""
    
    # Define roots - search for root letters in sequence
    roots = {
        'فهم': {
            'name': 'فهم',
            'english': 'understand/comprehend',
            'pattern': 'فهم',
            'occurrences': [],
            'examples': set()
        },
        'علم': {
            'name': 'علم',
            'english': 'know/knowledge',
            'pattern': 'علم',
            'occurrences': [],
            'examples': set()
        },
        'وعي': {
            'name': 'وعي',  
            'english': 'aware/conscious',
            'pattern': 'وعي',
            'occurrences': [],
            'examples': set()
        },
        'بصر': {
            'name': 'بصر',
            'english': 'see/perceive/insight',
            'pattern': 'بصر',
            'occurrences': [],
            'examples': set()
        },
        'نظر': {
            'name': 'نظر',
            'english': 'observe/look/contemplate',
            'pattern': 'نظر',
            'occurrences': [],
            'examples': set()
        }
    }
    
    # Search each verse
    for verse_num, verse in enumerate(verses, 1):
        # Remove diacritics for searching
        clean_verse = remove_diacritics(verse)
        
        for root_key, root_data in roots.items():
            pattern = root_data['pattern']
            if pattern in clean_verse:
                # Count occurrences
                count = clean_verse.count(pattern)
                
                # Extract words containing the root
                words = verse.split()
                matching_words = [w for w in words if pattern in remove_diacritics(w)]
                
                roots[root_key]['occurrences'].append({
                    'verse': verse_num,
                    'count': count,
                    'text': verse[:100] + '...' if len(verse) > 100 else verse,
                    'words': matching_words
                })
                
                # Add unique word forms to examples
                for word in matching_words:
                    roots[root_key]['examples'].add(remove_diacritics(word))
    
    return roots

def create_network_analysis(roots_data):
    """Analyze co-occurrence patterns between roots"""
    
    # Build verse-to-roots mapping
    verse_roots = defaultdict(set)
    
    for root_key, root_data in roots_data.items():
        for occ in root_data['occurrences']:
            verse_roots[occ['verse']].add(root_key)
    
    # Find co-occurrences
    co_occurrences = defaultdict(int)
    
    for verse, roots_in_verse in verse_roots.items():
        if len(roots_in_verse) > 1:
            # Found co-occurrence
            roots_list = sorted(list(roots_in_verse))
            for i in range(len(roots_list)):
                for j in range(i + 1, len(roots_list)):
                    pair = f"{roots_list[i]}-{roots_list[j]}"
                    co_occurrences[pair] += 1
    
    return verse_roots, co_occurrences

def main():
    print("="*70)
    print("Epistemological Roots Extraction from Quran")
    print("="*70)
    
    # Load Quran
    verses = load_quran()
    print(f"\nLoaded {len(verses)} verses\n")
    
    # Extract roots
    roots_data = extract_epistemological_roots(verses)
    
    # Prepare CSV data
    csv_data = []
    
    # Statistics
    print("Root Analysis:")
    print("-" * 70)
    
    total_occurrences = 0
    for root_key in ['فهم', 'علم', 'وعي', 'بصر', 'نظر']:  # Order them
        root_data = roots_data[root_key]
        unique_verses = len(root_data['occurrences'])
        total_count = sum(occ['count'] for occ in root_data['occurrences'])
        total_occurrences += total_count
        
        print(f"\n{root_data['name']} ({root_data['english']}):")
        print(f"  Total occurrences: {total_count}")
        print(f"  Unique verses: {unique_verses}")
        print(f"  Unique word forms: {len(root_data['examples'])}")
        if len(root_data['examples']) > 0:
            examples_list = sorted(list(root_data['examples']))[:10]
            print(f"  Example forms: {', '.join(examples_list)}")
        
        # Add to CSV
        for occ in root_data['occurrences']:
            csv_data.append({
                'Root': root_data['name'],
                'English': root_data['english'],
                'Verse': occ['verse'],
                'Count': occ['count'],
                'Words': ', '.join(occ['words']),
                'Example': occ['text']
            })
    
    print(f"\n{'='*70}")
    print(f"Total epistemological terminology: {total_occurrences} occurrences")
    print(f"{'='*70}")
    
    # Network analysis
    verse_roots, co_occurrences = create_network_analysis(roots_data)
    
    print(f"\nCo-occurrence Analysis:")
    print("-" * 70)
    if co_occurrences:
        for pair, count in sorted(co_occurrences.items(), key=lambda x: x[1], reverse=True)[:10]:
            print(f"  {pair}: {count} verses")
        print(f"  Total pairs: {len(co_occurrences)}")
    else:
        print("  No co-occurrences found in same verses")
    
    # Save to CSV
    csv_filename = 'epistemological_roots_analysis.csv'
    with open(csv_filename, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=['Root', 'English', 'Verse', 'Count', 'Words', 'Example'])
        writer.writeheader()
        writer.writerows(csv_data)
    
    print(f"\n✅ Results saved to {csv_filename}")
    print(f"   Total entries: {len(csv_data)}")
    
    # Save network data
    network_csv = 'epistemological_roots_network.csv'
    with open(network_csv, 'w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['Verse', 'Roots', 'Root_Count', 'Root_Names'])
        for verse, roots in sorted(verse_roots.items()):
            if len(roots) > 1:  # Only verses with multiple roots
                root_names = ', '.join([roots_data[r]['name'] for r in sorted(roots)])
                writer.writerow([verse, ', '.join(sorted(roots)), len(roots), root_names])
    
    print(f"✅ Network data saved to {network_csv}")
    print(f"   Verses with multiple roots: {sum(1 for v in verse_roots.values() if len(v) > 1)}")

if __name__ == '__main__':
    main()
