# Stage 8 — Explainability Smoke Tests

Smoke tests for evidence trace and explanation sections. Command:

```bash
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --render detailed "INPUT"
PYTHONPATH=src python3 scripts/run_orchestrator_skeleton.py --render compact "INPUT"
```

Or programmatically: `run(text, render_mode="detailed")` then inspect `pipeline["rendered_output"]["artifacts"]["evidence_trace"]` and the new sections.

---

## 1. "وَ"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries (L4–L13) |
| Skipped/partial | L8_ROOT_EXTRACTION, L9_WAZN_MATCHING skipped (gate: no morphology/root candidate) |
| Evidence Trace Overview | Stages skipped: L8_ROOT_EXTRACTION, L9_WAZN_MATCHING |
| Morphology Evidence | L8/L9 skipped with reason (gate) |
| Skipped/Partial Reasoning | Explains L8/L9 skip using gates_applied / limitation |
| Compact | Optional "Why:" line for root/wazn skipped |

---

## 2. "في"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries |
| Skipped | L8/L9 skipped (particle/preposition; no root candidate) |
| I3rab Evidence | L11 entry; source: c2e i3rab text; limitation: text-based |
| Validation Reasoning | global_validity, issue_count, final_confidence |

---

## 3. "!"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries |
| Skipped | L8/L9 skipped (non-word or no morphology candidate) |
| Validation | global_validity from L13 |

---

## 4. "يَا رَبِّ"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries |
| Morphology Evidence | L8/L9 may have roots for رب; or skipped for يا |
| I3rab Evidence | Token-level i3rab_text; limitation stated |
| Skipped/Partial | Depends on resolver (e.g. رب as noun with root) |

---

## 5. "كَاتِبٌ"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries |
| Morphology Evidence | L8: كَاتِبٌ root=ك-ت-ب; L9: template=فَاعِل |
| I3rab Evidence | كَاتِبٌ: i3rab_text=present; Source: c2e i3rab; Limitation: text-based |
| Validation Reasoning | valid; No issues; final_confidence |
| Skipped/Partial | L4 limited (no operator tokens) |
| Compact | No "Why" line (no root/wazn skip) |

**Detailed sample (excerpt)**  
- Evidence Trace Overview: Stages with decisive evidence include L8, L9, L11, L13; Stages skipped: none (or L4 limited).  
- Morphology Evidence: [L8_ROOT_EXTRACTION] Root(s) extracted… كَاتِبٌ: root=ك-ت-ب; [L9_WAZN_MATCHING] template=فَاعِل.  
- I3rab Evidence: I3rab per token from L11; Source: current c2e i3rab text payload; Limitation: I3rab evidence is text-based.

---

## 6. "إِنَّ اللَّهَ غَفُورٌ"

| Check | Expected |
|-------|----------|
| evidence_trace | 10 entries |
| Morphology Evidence | L8 roots (e.g. إنّ, الله null, غَفُور); L9 wazn per word |
| I3rab Evidence | Three tokens; i3rab_text present/absent per token |
| Validation Reasoning | global_validity; issues if any |
| Skipped/Partial | May include L4 limited; L12 partial possible |

---

## Summary Table

| Input | evidence_trace | Skipped/Partial explained | I3rab Evidence section | artifacts.evidence_trace |
|-------|----------------|---------------------------|-------------------------|---------------------------|
| وَ | 10 entries | L8, L9 gate | yes | yes |
| في | 10 entries | L8, L9 gate | yes | yes |
| ! | 10 entries | L8, L9 gate | yes | yes |
| يَا رَبِّ | 10 entries | as applicable | yes | yes |
| كَاتِبٌ | 10 entries | L4 limited | yes | yes |
| إِنَّ اللَّهَ غَفُورٌ | 10 entries | as applicable | yes | yes |

All runs must have `rendered_output.artifacts.evidence_trace` populated. Detailed mode must include: Evidence Trace Overview, Morphology Evidence, I3rab Evidence, Validation Reasoning, Skipped/Partial Reasoning. Skipped stages (e.g. L8/L9 for "وَ") must be explained using gate/eligibility, not invented linguistic reasons.
