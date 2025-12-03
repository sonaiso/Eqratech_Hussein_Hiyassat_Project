#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Extract all roots related to قرأ (read) and كتب (write) from the Quranic text.
This script performs morphological analysis to identify all derivations from these two roots.
"""

import re
from collections import defaultdict, Counter
import csv

def load_quran_text(filename='quran-simple-enhanced.txt'):
    """Load the Quranic text from file."""
    with open(filename, 'r', encoding='utf-8') as f:
        verses = [line.strip() for line in f if line.strip()]
    return verses

def normalize_arabic(text):
    """Normalize Arabic text by removing diacritics."""
    # Remove tashkeel (diacritics)
    arabic_diacritics = re.compile("""
        ّ    | # Shadda
        َ    | # Fatha
        ً    | # Tanween Fath
        ُ    | # Damma
        ٌ    | # Tanween Damm
        ِ    | # Kasra
        ٍ    | # Tanween Kasr
        ْ    | # Sukun
        ـ     # Tatweel
    """, re.VERBOSE)
    return arabic_diacritics.sub('', text)

def extract_qara_roots(verses):
    """
    Extract all words derived from root قرأ (q-r-ʾ).
    Includes: قرأ، قرآن، اقرأ، يقرأ، قارئ، قراءة, etc.
    """
    qara_words = defaultdict(list)
    
    for verse_num, verse in enumerate(verses, 1):
        # Split verse into words
        words = verse.split()
        
        for word in words:
            # Remove diacritics for pattern matching
            normalized = normalize_arabic(word)
            
            # Check if word contains قر pattern (core of the root)
            if 'قر' in normalized:
                # Further check for قرأ/قرآن patterns
                if any(pattern in normalized for pattern in ['قرا', 'قرء', 'قري', 'قرو']):
                    qara_words[word].append((verse_num, verse))
    
    return qara_words

def extract_kataba_roots(verses):
    """
    Extract all words derived from root كتب (k-t-b).
    Includes: كتب، كتاب، كاتب، كتابة، مكتوب، etc.
    """
    kataba_words = defaultdict(list)
    
    for verse_num, verse in enumerate(verses, 1):
        # Split verse into words
        words = verse.split()
        
        for word in words:
            # Remove diacritics for pattern matching
            normalized = normalize_arabic(word)
            
            # Check if word contains كتب pattern (all three letters of the root)
            if 'كتب' in normalized or 'كتاب' in normalized or 'كاتب' in normalized:
                kataba_words[word].append((verse_num, verse))
    
    return kataba_words

def analyze_and_display_results(qara_words, kataba_words):
    """Analyze and display the extracted roots."""
    print('=' * 100)
    print('استخراج جذور قرأ وكتب من القرآن الكريم')
    print('Extracting roots قرأ (read) and كتب (write) from the Quran')
    print('=' * 100)
    print()
    
    # Analyze قرأ root
    print('📖 جذر قرأ (Q-R-ʾ Root - Reading):')
    print('-' * 100)
    
    if qara_words:
        qara_counter = Counter({word: len(occurrences) for word, occurrences in qara_words.items()})
        total_qara = sum(qara_counter.values())
        
        for word, count in qara_counter.most_common():
            print(f'  {word:20} : {count:3} مرة')
            # Show first 3 occurrences
            for i, (verse_num, verse) in enumerate(qara_words[word][:3]):
                verse_preview = verse[:80] + '...' if len(verse) > 80 else verse
                print(f'      └─ آية {verse_num}: {verse_preview}')
            if len(qara_words[word]) > 3:
                print(f'      └─ ... و {len(qara_words[word]) - 3} أمثلة أخرى')
            print()
        
        print(f'  📊 المجموع الكلي: {total_qara} كلمة من جذر قرأ')
        print(f'  📊 عدد الأشكال المختلفة: {len(qara_counter)} شكل')
    else:
        print('  ⚠️  لم يتم العثور على كلمات من جذر قرأ')
    
    print()
    print('=' * 100)
    print()
    
    # Analyze كتب root
    print('✍️  جذر كتب (K-T-B Root - Writing):')
    print('-' * 100)
    
    if kataba_words:
        kataba_counter = Counter({word: len(occurrences) for word, occurrences in kataba_words.items()})
        total_kataba = sum(kataba_counter.values())
        
        for word, count in kataba_counter.most_common():
            print(f'  {word:20} : {count:3} مرة')
            # Show first 3 occurrences
            for i, (verse_num, verse) in enumerate(kataba_words[word][:3]):
                verse_preview = verse[:80] + '...' if len(verse) > 80 else verse
                print(f'      └─ آية {verse_num}: {verse_preview}')
            if len(kataba_words[word]) > 3:
                print(f'      └─ ... و {len(kataba_words[word]) - 3} أمثلة أخرى')
            print()
        
        print(f'  📊 المجموع الكلي: {total_kataba} كلمة من جذر كتب')
        print(f'  📊 عدد الأشكال المختلفة: {len(kataba_counter)} شكل')
    else:
        print('  ⚠️  لم يتم العثور على كلمات من جذر كتب')
    
    print()
    print('=' * 100)
    
    # Grand total
    total_all = sum(Counter({word: len(occurrences) for word, occurrences in qara_words.items()}).values()) + \
                sum(Counter({word: len(occurrences) for word, occurrences in kataba_words.items()}).values())
    print(f'📊 الإجمالي الكلي للجذرين: {total_all} كلمة')
    print('=' * 100)

def save_to_csv(qara_words, kataba_words, filename='quran_roots_qara_kataba.csv'):
    """Save results to CSV file."""
    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['Root', 'Word', 'Count', 'Verse_Numbers', 'Sample_Verse'])
        
        # Write قرأ words
        qara_counter = Counter({word: len(occurrences) for word, occurrences in qara_words.items()})
        for word, count in qara_counter.most_common():
            verse_nums = ', '.join(str(vn) for vn, _ in qara_words[word][:5])
            sample_verse = qara_words[word][0][1][:100] if qara_words[word] else ''
            writer.writerow(['قرأ', word, count, verse_nums, sample_verse])
        
        # Write كتب words
        kataba_counter = Counter({word: len(occurrences) for word, occurrences in kataba_words.items()})
        for word, count in kataba_counter.most_common():
            verse_nums = ', '.join(str(vn) for vn, _ in kataba_words[word][:5])
            sample_verse = kataba_words[word][0][1][:100] if kataba_words[word] else ''
            writer.writerow(['كتب', word, count, verse_nums, sample_verse])
    
    print(f'\n✅ النتائج محفوظة في: {filename}')

def main():
    """Main execution function."""
    print('🔍 جاري تحميل النص القرآني...')
    verses = load_quran_text()
    print(f'✅ تم تحميل {len(verses)} آية')
    print()
    
    print('🔍 جاري استخراج جذر قرأ...')
    qara_words = extract_qara_roots(verses)
    print(f'✅ تم العثور على {len(qara_words)} شكل مختلف من جذر قرأ')
    print()
    
    print('🔍 جاري استخراج جذر كتب...')
    kataba_words = extract_kataba_roots(verses)
    print(f'✅ تم العثور على {len(kataba_words)} شكل مختلف من جذر كتب')
    print()
    
    # Display results
    analyze_and_display_results(qara_words, kataba_words)
    
    # Save to CSV
    save_to_csv(qara_words, kataba_words)

if __name__ == '__main__':
    main()
