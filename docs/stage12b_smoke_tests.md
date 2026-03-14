# Stage L12B — Smoke Test Results

Canonical inputs used for smoke testing the Analogical Reasoning layer.

## Command

```bash
PYTHONPATH=src python3 -c "
from orchestrator import run
for text in ['وَ', 'في', '!', 'يَا رَبِّ', 'كَاتِبٌ', 'إِنَّ اللَّهَ غَفُورٌ']:
    p = run(text, render_mode='detailed')
    lo = p.get('layer_outputs') or {}
    L12B = lo.get('L12B_ANALOGICAL_REASONING') or {}
    tr = L12B.get('transformation_result') or {}
    summary = tr.get('analogical_summary') or {}
    status = L12B.get('status')
    n = summary.get('total_inferences', 0)
    print(f'{repr(text)[:30]:30} | L12B status={status} | inferences={n}')
"
```

## Expected Behavior

| Input            | L12B status | Where inference appears |
|------------------|------------|-------------------------|
| وَ               | skipped or partial | No tokens or operator-only; may skip or produce no inference. |
| في               | partial or success | Particle; may have no morphological inference; conditional/surface i3rab possible. |
| !                | skipped    | No Arabic tokens; skipped. |
| يَا رَبِّ        | partial or success | Vocative; possible conditional or i3rab analogy. |
| كَاتِبٌ          | success    | Noun + فاعل-type wazn → strong morphological inference (ism fa'il). |
| إِنَّ اللَّهَ غَفُورٌ | success | Sentence type شرط → conditional inference; غَفُورٌ may get morphological inference; possible ambiguity resolution. |

## Documented Observations

* **كَاتِبٌ** — Typically yields at least one inference (morphological: ism fa'il pattern).
* **إِنَّ اللَّهَ غَفُورٌ** — Sentence type شرط triggers causal/temporal inference; غَفُورٌ may get فَعُول pattern inference; first-token resolution may appear.
* **وَ**, **في**, **!** — May be skipped (no tokens) or partial (no inference); L12B does not fail the pipeline.
* **يَا رَبِّ** — Content word(s) present; may get weak or proposed inferences.

Explainability trace includes `L12B_ANALOGICAL_REASONING` for all runs where the stage is not skipped. Presentation (detailed) includes section `analogical_reasoning` with inference count and top claims. Compact mode shows one line: `Analogical inference used: yes` or `no`.
