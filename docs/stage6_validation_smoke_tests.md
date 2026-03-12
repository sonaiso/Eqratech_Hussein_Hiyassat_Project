# Stage 6 — Validation smoke tests

## Command

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
p = run('وَ')
L13 = p['layer_outputs']['L13_VALIDATION']
print('status:', L13['status'])
print('global_validity:', L13['transformation_result']['global_validity'])
print('issues:', L13['transformation_result']['issues'])
print('final_validation:', p.get('final_validation'))
"
```

---

## Results (six inputs)

| Input | L13 status | global_validity | issue_codes | final_confidence |
|-------|------------|-----------------|-------------|-------------------|
| وَ | success | valid | [] | 1.0 |
| في | success | valid | [] | 1.0 |
| ! | success | valid | [] | 1.0 |
| يَا رَبِّ | success | valid | [] | 1.0 |
| كَاتِبٌ | success | valid | [] | 1.0 |
| إِنَّ اللَّهَ غَفُورٌ | success | valid | [] | 1.0 |

---

## Key stage statuses (reference)

With Stage 5 gates, minimal inputs get skipped/partial where appropriate, so L13 sees consistent outputs:

- **وَ, في, !**: L8, L9 skipped; L11 success or partial; L12 partial.
- **يَا رَبِّ, كَاتِبٌ, إِنَّ اللَّهَ غَفُورٌ**: L8/L9 success or partial as eligible; L13 finds no prerequisite or empty-success issues.

---

## When L13 would emit issues

- **EMPTY_SUCCESS**: If L8 (or L9) ever reported success but all roots (or wazn) were null.
- **MISSING_PREREQUISITE**: If L8/L9 reported success but L2 had no tokens.
- **I3RAB_MISSING**: If L11 reported success but no token had `i3rab_text`.
- **WEAK_SENTENCE_EVIDENCE**: If L12 reported success with single token and no rhetoric.
- **INCONSISTENT_STATUS**: If L10 reported failed (info only).

With current Stage 5 routing, ineligible stages are skipped, so these cases do not occur on the six smoke inputs; L13 correctly reports **valid** and empty issues.

---

## final_validation (top-level)

After L13 runs, `pipeline["final_validation"]` contains:

- `global_validity`
- `issues`
- `validated_layers_summary` (layer_id → status)
- `final_confidence` (when not invalid)

This is populated from L13’s transformation_result in the orchestrator.
