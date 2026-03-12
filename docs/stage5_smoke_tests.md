# Stage 5 — Smoke tests (gates and eligibility)

## Command used

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
p = run('وَ')
# inspect p['layer_outputs']['L8_ROOT_EXTRACTION']['status'], gates_applied, etc.
"
```

Or for all five inputs:

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
for text in ['وَ', 'في', '!', 'يَا رَبِّ', 'كَاتِبٌ']:
    p = run(text)
    print(text, 'L8=', p['layer_outputs']['L8_ROOT_EXTRACTION']['status'], ...)
"
```

---

## Results (Stage 5 eligibility routing)

| Input | Label | L8_ROOT_EXTRACTION | L9_WAZN_MATCHING | L11_I3RAB | L12_SEMANTIC_RHETORICAL |
|-------|--------|--------------------|------------------|-----------|---------------------------|
| وَ | single operator | **skipped** | **skipped** | success | **partial** |
| في | preposition | **skipped** | **skipped** | success | **partial** |
| ! | punctuation | **skipped** | **skipped** | partial | **partial** |
| يَا رَبِّ | vocative | success | partial | success | success |
| كَاتِبٌ | single noun | success | success | success | **partial** |

---

## Interpretation

- **وَ, في:** No morphology/root candidate (operator/preposition) → L8 and L9 **skipped** (no fake success). L11 can still be success (i3rab for particle). L12 **partial** (single token, no rhetoric).
- **!:** No or minimal tokens → L8/L9 skipped; L11/L12 partial (no i3rab/sentence evidence).
- **يَا رَبِّ:** Content word present → L8 success; L9 partial if only one word has wazn; L12 success (two tokens, sentence-level evidence).
- **كَاتِبٌ:** Content word with root and wazn → L8, L9, L11 success; L12 **partial** (single token, no rhetoric).

---

## Definition of done (Stage 5)

- Minimal/pathological inputs **do not** get fake success for ineligible stages.
- L8 and L9 are **skipped** when there is no morphology candidate or no root candidate, with `gates_applied` and optional warnings.
- L11 may remain success when i3rab evidence exists (e.g. particle i3rab).
- L12 is **partial** when sentence-level evidence is weak (e.g. single token, no rhetoric).

See **docs/stage5_gates_and_routing.md** for gate definitions and per-stage rules.
