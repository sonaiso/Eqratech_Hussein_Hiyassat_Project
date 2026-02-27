"""
Corpus Evaluation Script for Syntax Layer.

Loads test sentences, runs the full pipeline (C1 → C2a → C2b → SyntacticParser),
and prints a summary of links found by type and constraint violations.

Usage:
    python scripts/evaluate_syntax.py
"""

import sys
import os

# Ensure src is on the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from fvafk.c2b.word_form.word_form_builder import WordFormBuilder
from fvafk.syntax import SyntacticParser, ConstraintValidator

# Hardcoded test sentences (representative Arabic examples)
TEST_SENTENCES = [
    # (surface, description)
    ("الكتاب مفيد", "nominal sentence: mubtada + khabar"),
    ("كتب الطالب الدرس", "verbal sentence: verb + fael + mafool"),
    ("في البيت", "prepositional phrase: jar + majroor"),
    ("الطالب المجتهد", "noun + sifa adjective"),
    ("ذهب الرجل إلى المسجد", "verb + noun + preposition phrase"),
]


def _make_word_form(surface: str, kind: str, case: str = "unknown",
                   number: str = "unknown", gender: str = "unknown",
                   definite: bool = False, word_id: int = 0):
    """Build a minimal WordForm from scratch for evaluation."""
    builder = WordFormBuilder()
    return builder.from_c2b({
        "word": surface,
        "span": {"start": 0, "end": len(surface)},
        "kind": kind,
        "features": {
            "case": case,
            "number": number,
            "gender": gender,
            "definite": definite,
        },
    }, word_id=word_id)


def run_evaluation():
    """Run evaluation over test sentences and print summary."""
    parser = SyntacticParser()
    validator = ConstraintValidator()

    total_sentences = 0
    total_isnadi = 0
    total_tadmini = 0
    total_taqyidi = 0
    total_violations = 0

    print("=" * 60)
    print("  FVAFK Syntax Evaluation")
    print("=" * 60)

    # Try to load from data/arabic_json if available
    data_dir = os.path.join(os.path.dirname(__file__), '..', 'data', 'arabic_json')
    sentences_from_data = []
    if os.path.isdir(data_dir):
        import json
        for fname in sorted(os.listdir(data_dir))[:5]:
            if fname.endswith('.json'):
                try:
                    with open(os.path.join(data_dir, fname), encoding='utf-8') as f:
                        data = json.load(f)
                    if isinstance(data, list):
                        for item in data[:3]:
                            if isinstance(item, dict) and 'word' in item:
                                sentences_from_data.append(item['word'])
                    elif isinstance(data, dict) and 'word' in data:
                        sentences_from_data.append(data['word'])
                except Exception:
                    pass

    # Build word forms for hardcoded test sentences
    sentence_word_forms = []

    # Sentence 1: الكتاب مفيد
    sentence_word_forms.append([
        _make_word_form("الكتاب", "noun", case="nominative", number="singular",
                       gender="masculine", definite=True, word_id=0),
        _make_word_form("مفيد", "noun", case="nominative", number="singular",
                       gender="masculine", definite=False, word_id=1),
    ])

    # Sentence 2: كتب الطالب الدرس
    sentence_word_forms.append([
        _make_word_form("كتب", "verb", word_id=0),
        _make_word_form("الطالب", "noun", case="nominative", number="singular",
                       gender="masculine", definite=True, word_id=1),
        _make_word_form("الدرس", "noun", case="accusative", number="singular",
                       gender="masculine", definite=True, word_id=2),
    ])

    # Sentence 3: في البيت
    sentence_word_forms.append([
        _make_word_form("في", "particle", word_id=0),
        _make_word_form("البيت", "noun", case="genitive", number="singular",
                       gender="masculine", definite=True, word_id=1),
    ])

    # Sentence 4: الطالب المجتهد
    sentence_word_forms.append([
        _make_word_form("الطالب", "noun", case="nominative", number="singular",
                       gender="masculine", definite=True, word_id=0),
        _make_word_form("المجتهد", "adjective", case="nominative", number="singular",
                       gender="masculine", definite=True, word_id=1),
    ])

    # Sentence 5: ذهب الرجل إلى المسجد
    sentence_word_forms.append([
        _make_word_form("ذهب", "verb", word_id=0),
        _make_word_form("الرجل", "noun", case="nominative", number="singular",
                       gender="masculine", definite=True, word_id=1),
        _make_word_form("إلى", "particle", word_id=2),
        _make_word_form("المسجد", "noun", case="genitive", number="singular",
                       gender="masculine", definite=True, word_id=3),
    ])

    for i, (wf_list, (surface, desc)) in enumerate(
        zip(sentence_word_forms, TEST_SENTENCES)
    ):
        total_sentences += 1
        graph = parser.parse(wf_list)
        violations = validator.validate(graph)

        n_isnadi = len(graph.isnadi_links)
        n_tadmini = len(graph.tadmini_links)
        n_taqyidi = len(graph.taqyidi_links)
        n_viol = len(violations)

        total_isnadi += n_isnadi
        total_tadmini += n_tadmini
        total_taqyidi += n_taqyidi
        total_violations += n_viol

        print(f"\n[{i+1}] {surface!r}  ({desc})")
        print(f"     isnadi={n_isnadi}  tadmini={n_tadmini}  taqyidi={n_taqyidi}  violations={n_viol}")
        if violations:
            for v in violations:
                print(f"     ⚠  {v.constraint_name}: {v.message}")

    print("\n" + "=" * 60)
    print("  Summary")
    print("=" * 60)
    print(f"  Total sentences : {total_sentences}")
    print(f"  Isnadi links    : {total_isnadi}")
    print(f"  Tadmini links   : {total_tadmini}")
    print(f"  Taqyidi links   : {total_taqyidi}")
    print(f"  Violations      : {total_violations}")
    print("=" * 60)


if __name__ == "__main__":
    run_evaluation()
