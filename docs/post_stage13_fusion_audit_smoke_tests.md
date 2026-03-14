# Post-Stage-13 Fusion Audit — Smoke Test Results

Canonical inputs and what to expect from the post-fusion audit.

## Command

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
for text in ['وَ', 'في', '!', 'يَا رَبِّ', 'كَاتِبٌ', 'إِنَّ اللَّهَ غَفُورٌ']:
    p = run(text, render_mode='detailed')
    pa = p.get('post_stage13_audit') or {}
    consistency = pa.get('fusion_consistency', '—')
    issues_count = len(pa.get('issues') or [])
    notes = pa.get('advisory_notes') or []
    conservative = p.get('meta', {}).get('conservative_fusion_mode')
    print(f'{repr(text)[:25]:25} | consistency={consistency} issues={issues_count} conservative={conservative} notes={len(notes)}')
"
```

## Expected Behavior

| Input | fusion_consistency | issues count | advisory_notes | Conservative behavior |
|-------|--------------------|--------------|----------------|------------------------|
| وَ | high / medium | 0 or low | often none | meta.conservative_fusion_mode may be False (MEDIUM readiness) |
| في | high / medium | 0 or low | often none | — |
| ! | low / medium | ≥0 | possible | conservative_fusion_mode True; fusion may have empty token_states |
| يَا رَبِّ | high / medium | 0 or low | often none | — |
| كَاتِبٌ | high | 0 | none | strong sources (ROOT, WAZN) present; no overreach |
| إِنَّ اللَّهَ غَفُورٌ | high / medium | 0 or low | possible | — |

## Documented Observations

- **كَاتِبٌ**: Typically **high** consistency; root and wazn present; no POS contradiction; strong_sources_respected True.
- **!**: May have **low** or **medium** (e.g. MISSING_FUSION_STATE or empty token_states); conservative mode expected.
- **إِنَّ اللَّهَ غَفُورٌ**: Sentence type and multiple tokens; consistency usually **high** or **medium**; issues count 0 or small.
- **Conservative behavior**: When readiness_band was LOW and fusion ran in conservative mode, the audit checks that fusion did not assign stable_role inappropriately (CONSERVATIVE_MODE_VIOLATION if it did).

## Notes

- Issue codes (e.g. UNRESOLVED_AMBIGUITY_MISMATCH, WEAK_SOURCE_OVERREACH) appear only when the corresponding condition is detected.
- advisory_notes may include "Conservative mode should not resolve syntactic roles" when CONSERVATIVE_MODE_VIOLATION is raised.
