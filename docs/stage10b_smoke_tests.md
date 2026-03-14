# L10B Deep Syntax — Smoke Test Results

Canonical inputs and what to expect from L10B.

## Command

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
for text in [
    'كَتَبَ زَيْدٌ الرِّسَالَةَ',
    'الطَّالِبُ الْمُجْتَهِدُ حَاضِرٌ',
    'مَرَرْتُ بِالرَّجُلِ الْكَرِيمِ',
    'لَوْ اجْتَهَدَ الطَّالِبُ لَنَجَحَ',
    'جَاءَ الطَّالِبُ مُبْتَسِمًا',
    'في البيت',
    'كَاتِبٌ',
]:
    p = run(text, render_mode='detailed')
    lo = p.get('layer_outputs') or {}
    l10b = lo.get('L10B_DEEP_SYNTAX') or {}
    tr = l10b.get('transformation_result') or {}
    summary = tr.get('syntax_summary') or {}
    nodes = tr.get('dependency_nodes') or []
    edges = tr.get('dependency_edges') or []
    clauses = tr.get('clause_units') or []
    print(f'{repr(text)[:35]:35} | nodes={len(nodes)} edges={len(edges)} resolved={summary.get(\"resolved_edges\")} main={summary.get(\"main_clause_type\")} clauses={len(clauses)}')
"
```

## Expected Behavior

| Input | Nodes | Edges | Resolved | Main clause | Clause units | Notes |
|-------|--------|--------|----------|-------------|--------------|--------|
| كَتَبَ زَيْدٌ الرِّسَالَةَ | 4 | ≥0 | from L10 isnadi | verbal/mixed | ≥1 | Verb–subject–object from L10 links if present |
| الطَّالِبُ الْمُجْتَهِدُ حَاضِرٌ | 3 | ≥0 | 0 or from L10 | nominal | ≥1 | Idafa/naat candidates possible |
| مَرَرْتُ بِالرَّجُلِ الْكَرِيمِ | 4 | ≥0 | ≥1 (jar_majrur) | mixed | ≥1 | ب + الرجل → majrur |
| لَوْ اجْتَهَدَ الطَّالِبُ لَنَجَحَ | 5 | ≥0 | 0 or candidate | mixed | ≥1 | Conditional clause_unit possible |
| جَاءَ الطَّالِبُ مُبْتَسِمًا | 4 | ≥0 | from L10 | verbal | ≥1 | Hal candidate possible |
| في البيت | 2 | ≥0 | ≥1 | nominal | 1 | في → البيت majrur |
| كَاتِبٌ | 1 | 0 | 0 | nominal | 1 | Single token; no edges |

## Resolved Relations

- **Preposition → object**: When the first token is in HURUF_JAR (في, ب, ل, من, إلى, …) or L4 marks it as operator, the next token is attached as **majrur** with status **resolved** (confidence 0.75).
- **L10 isnadi links**: Mapped to dependency_edges with relation from link type (mubtada/khabar, fa'il, maf'ul_bih, etc.); confidence from L10 or default 0.75; status **resolved** if confidence ≥ 0.75.

## Unresolved Structures

- Single-word input: no edges; one node with status **unresolved**.
- Sentences without L10 links and without clear harf_jar: edges may be only **candidate** (idafa, etc.) or none.
- **Known weak cases**: complex embedding, multiple PPs (attachment ambiguity), full idafa chains (only adjacent pairs).

## Clause Detection Quality

- **main**: Always one main clause unit (start_token_id 0, end_token_id last).
- **conditional**: When the first token is لو / إن / إذا, a clause_unit with type **conditional** is added.
- **nominal/verbal/mixed**: Inferred from presence of L10 isnadi links and token count.

## Conservative Behavior

- No invented dependencies; no head for every token when evidence is missing.
- Candidate relations (idafa, naat, hal_candidate, etc.) are marked **candidate** and not promoted to resolved without stronger evidence.
