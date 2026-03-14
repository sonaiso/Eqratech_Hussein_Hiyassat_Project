# Stage L11B — Causal I3rab Engine

## Why L11B Was Added

L11 provides **text-based i3rab** (human-readable إعراب from c2e). L11B adds a **structured causal reasoning layer**: it explains **what** the grammatical role is, **why** it was assigned, **what** case/mood is inferred, and **which** marker is expected, using only existing pipeline evidence (L2, L4, L5, L8, L9, L10, L10B, L11). L11 remains the legacy text layer; L11B coexists as the reasoned representation.

## Difference Between Text I3rab and Causal I3rab

| | L11 (text i3rab) | L11B (causal i3rab) |
|---|------------------|----------------------|
| Output | Human-readable i3rab text per token | Structured role, governing_factor, case_or_mood, marker, reasoning_steps |
| Source | c2e / morphology adapter | L10B + L11 + L4/L5/L9 rules |
| Use | Quick read-off | Downstream reasoning, fusion, validation |
| Weak evidence | Still shown as text | Marked candidate/unresolved with limitations |

## Supported Roles (First-Scope)

- **فاعل** — subject (active verb)
- **نائب فاعل** — substitute subject (passive)
- **مفعول به** — object
- **مبتدأ** — topic (nominal sentence), candidate
- **خبر** — predicate (nominal sentence), candidate
- **اسم مجرور بحرف الجر** — object of preposition
- **نعت** — adjective, candidate
- **حال** — circumstantial accusative, candidate
- **مضاف إليه** — idafa complement, candidate

## Supported Governing Factors

- **الفعل** — the verb
- **حرف الجر** — preposition
- **الابتداء** — nominal sentence onset
- **إن وأخواتها** — only if detectable from operators
- **كان وأخواتها** — only if strong evidence exists
- **فعل مبني للمجهول** — for نائب فاعل when passive hints are strong

## Case / Mood and Markers

- **Case/mood:** مرفوع، منصوب، مجرور، مجزوم، مبني، غير محسوم
- **Marker:** الضمة، الفتحة، الكسرة، السكون، مبني، غير محسوم

## Confidence Strategy

- **0.90** — strong direct rule with aligned evidence (e.g. L10B majrur → اسم مجرور)
- **0.75** — good rule with moderate syntax support (e.g. passive + noun → نائب فاعل)
- **0.60** — candidate role with limited support (e.g. nominal مبتدأ/خبر)
- **0.40** — weak fallback from text-based i3rab only
- **0.20** — unresolved but minimally informed  
All values in **[0.05, 0.98]**; never 1.0 or 0.0.

Confidence is lowered when parse_strength is low, only L11 text is available, role is candidate, or multiple plausible roles remain.

## Impact of parse_strength

L11B reads **L10B syntax_summary.parse_strength** and **advisory_notes**. When **parse_strength < 0.35**:

- A limitation **"deep syntax shallow"** is added to token reasoning where applicable.
- **Confidence** is reduced (e.g. resolved-band roles get at most CONF_GOOD or CONF_CANDIDATE).
- **Role status** is preferred as **candidate** over **resolved** unless evidence is independently strong (e.g. L10B resolved majrur edge).
- If L10B **advisory_notes** contain *"dependency parse shallow — interpret cautiously"*, that note is preserved in token **limitations**.

This avoids over-resolution when deep syntax is weak and keeps L11B aligned with L10B’s guarded output.

## Limitations

- First-scope roles only; no full Arabic i3rab coverage.
- Rule-constrained; no ML or external analyzers.
- Contradictory evidence → candidate + limitation, not override.
- Unresolved tokens left unresolved; no invented roles.

## Relation to L10B and L13

- **L10B:** L11B uses L10B dependency_edges (majrur, idafa) and main_clause_type to assign roles and governing factors.
- **L13 (Cognitive Fusion):** L11B output can be consumed as stronger syntactic/role evidence; fusion does not run L11B, it reads its result from the pipeline.
