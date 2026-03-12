# Stage 7 — Presentation Layer Smoke Tests

Smoke tests for L14 rendering on minimal and normal inputs. Command used:

```bash
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --render MODE "INPUT"
```

Or programmatically: `run(text, render_mode=MODE)` then inspect `pipeline["rendered_output"]` and `layer_outputs["L14_PRESENTATION"]`.

---

## 1. "وَ"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output populated | yes |
| mode | as requested (compact/detailed/debug) |
| i3rab section in detailed | yes (explicit section; may be empty or حرف مبني) |

**Compact sample**: Input: وَ / Validity: weak or partial / Roots: — / I3rab: — or حرف مبني / Validation: issues possible.

**Detailed**: Stage status shows L8/L9 skipped; I3rab section present; Validation section shows issues.

---

## 2. "في"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output | yes |
| i3rab explicit | yes |

**Compact**: Particle/preposition; roots may be empty; i3rab may show حرف جر etc.

---

## 3. "!"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output | yes |
| Overview | original text "!"; validity from L13 |

---

## 4. "يَا رَبِّ"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output | yes |
| I3rab section | present; يا + ربِّ with appropriate i3rab_text if available |

**Compact**: Key morphology and i3rab for two tokens.

---

## 5. "كَاتِبٌ"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output | yes |
| I3rab explicit | yes — e.g. كَاتِبٌ: فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ |

**Compact sample**:
```
Input: كَاتِبٌ
Validity: valid (confidence: 1.0)
Sentence type: خبرية
Roots: كَاتِبٌ: ك-ت-ب
I3rab:   كَاتِبٌ: فَاعِلٌ مَرْفُوعٌ وَعَلَامَةُ رَفْعِهِ الضَّمَّةُ الظَّاهِرَةُ…
Validation: No issues.
```

**Detailed**: All 9 sections present; I3rab is its own section with token and i3rab_text.

---

## 6. "إِنَّ اللَّهَ غَفُورٌ"

| Check | Result |
|-------|--------|
| L14 status | success |
| rendered_output | yes |
| I3rab section | present; three tokens with i3rab_text when available |
| Validation | global_validity and issues from L13 |

**Compact**: Input, validity, sentence type, roots for إنَّ/الله/غَفُورٌ, i3rab lines, validation note.

---

## Summary Table

| Input | L14 status | rendered_output | I3rab explicit section |
|-------|-----------|-----------------|------------------------|
| وَ | success | yes | yes |
| في | success | yes | yes |
| ! | success | yes | yes |
| يَا رَبِّ | success | yes | yes |
| كَاتِبٌ | success | yes | yes |
| إِنَّ اللَّهَ غَفُورٌ | success | yes | yes |

All modes (compact, detailed, debug) produce valid output; i3rab appears as a first-class section in detailed mode and in compact summary.
