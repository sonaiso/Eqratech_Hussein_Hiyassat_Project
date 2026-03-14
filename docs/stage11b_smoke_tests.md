# L11B Causal I3rab — Smoke Test Results

Canonical inputs and what to expect from L11B.

## Command

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
for text in [
    'كَتَبَ زَيْدٌ الرِّسَالَةَ',
    'ضُرِبَ الرَّجُلُ',
    'مَرَرْتُ بِالرَّجُلِ',
    'الطَّالِبُ مُجْتَهِدٌ',
    'جَاءَ الطَّالِبُ مُبْتَسِمًا',
    'في البيت',
]:
    p = run(text, render_mode='detailed')
    tr = (p.get('layer_outputs') or {}).get('L11B_CAUSAL_I3RAB') or {}
    tr = tr.get('transformation_result') or {}
    s = tr.get('i3rab_summary') or {}
    reasoning = tr.get('token_i3rab_reasoning') or []
    roles = [(r.get('surface'), r.get('role'), r.get('role_status')) for r in reasoning]
    print(f'{repr(text)[:35]:35} | resolved={s.get(\"resolved_tokens\")} cand={s.get(\"candidate_tokens\")} roles={roles[:6]}')
"
```

## Expected Behavior

| Input | Resolved | Candidate | Example roles |
|-------|----------|-----------|----------------|
| كَتَبَ زَيْدٌ الرِّسَالَةَ | ≥1 | ≥0 | فاعل (زيد), مفعول به candidate (الرسالة) |
| ضُرِبَ الرَّجُلُ | ≥1 | ≥0 | نائب فاعل (الرجل) when passive wazn detected |
| مَرَرْتُ بِالرَّجُلِ | ≥1 | ≥0 | اسم مجرور (الرجل) when L10B majrur or prev harf jar |
| الطَّالِبُ مُجْتَهِدٌ | ≥0 | ≥1 | مبتدأ/خبر candidates in nominal clause |
| جَاءَ الطَّالِبُ مُبْتَسِمًا | ≥1 | ≥0 | فاعل (الطالب) |
| في البيت | ≥1 | ≥0 | اسم مجرور (البيت) |

## Resolved vs Candidate

- **Resolved:** Role from strong rule (e.g. L10B majrur edge, passive verb + noun, harf jar + noun, finite verb + subject).
- **Candidate:** Role from nominal clause, idafa, or object position heuristic; or weak text fallback.
- **Unresolved:** No sufficient evidence; limitations noted.

## Weak Points

- نعت/حال/مضاف إليه are first-scope candidates only; agreement and context not fully modeled.
- إن وأخواتها / كان وأخواتها require operator or strong evidence to appear as governing factor.
- Long sentences may have many unresolved tokens; no full dependency-based role propagation yet.
