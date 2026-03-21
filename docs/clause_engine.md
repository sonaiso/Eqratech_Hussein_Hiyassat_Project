# Clause Engine (Stage 16)

## Pass 1 — Conditional decomposition

When L4 marks a real conditional trigger (`COND`), the engine emits (when present):

- `shart_particle_*`, `feil_shart_*`, `jawab_particle_*`, `jawab_shart_*`

`ACC_TAWKID` / emphasis `إنَّ` must not be treated as conditional (see `clause_engine._is_conditional_trigger`).

## Pass 2 — Additive (hal / tamyiz / sila)

Runs **after** Pass 1. **Does not modify** existing Pass 1 rows; **appends** new rows and updates `clause_count` and flags:

- `hal_detected`, `tamyiz_detected`, `sila_detected`

All Pass 2 rows use `status: "candidate"` and `confidence < 0.85` unless otherwise noted.

### HAL (`hal_clause`)

- **واو الحال:** separate `و` / `وَ` + following **present** verb; or merged `وَهُوَ`-style token (second radical after `و` must be `ه`, not `ج` as in `وَجَاءُوا`).
- **Implicit:** present verb immediately after a SUBJ/OBJ dependent of the matrix verb (Stage 15 links); preceding token must **not** carry tanween fatḥ (avoids ظرف/تمييز confusion).
- **ظرف + مضارع:** accusative host with tanween + following present verb (e.g. `عِشَاءً يَبْكُونَ`).
- **Mufrad hal (conditional):** tanween fatḥ on a token **after** the feil matrix verb and **before** the jawab matrix verb → `parent_clause_id = feil_shart_0`.

### Tamyiz (`tamyiz_phrase`)

- **L12:** `tamyiz_relation` on `L12_GENDER_NUMBER.token_features`.
- **Lexeme:** number lexeme (aligned with L12 `_NUMBER_LEXEMES`) + following L5 **noun** → `tamyiz_type: "adad"`, `rule: number_lexeme_tamyiz_detection`.

تمييز النسبة (nisba) is **not** implemented in Pass 2; suspected cases may be logged later.

### SILA (`ism_mawsul` + `sila_mawsul`)

- Surface اسم موصول list (diacritic-tolerant): `الذي/التي/الذين/…`, `ما`, `من`, `مهما`, `أيّ`, etc.
- **Verb head:** prefer L8B/L5/`has_strong_true_verb_evidence`; **fallback** for `مَنْ`/`مَا` when the next token is not tagged as a verb but is the single overt predicate of the صلة.

`sila_mawsul` includes `antecedent_token_id`, `i3rab_note: "لا محل لها من الإعراب"`.

## Output schema (top-level)

In addition to Pass 1 fields:

| Field | Type | Description |
|-------|------|-------------|
| `hal_detected` | bool | Any `hal_clause` appended |
| `tamyiz_detected` | bool | Any `tamyiz_phrase` appended |
| `sila_detected` | bool | Any `ism_mawsul` / `sila_mawsul` appended |

## Presentation

- `scripts/analyze_sentence.py` — SECTION **4g** (flags + optional Pass 2 detail rows).
- `src/orchestrator/l14_presentation.py` — SECTION **4g** detailed mode.

## Tests

- `tests/orchestrator/test_clause_engine.py` — Pass 1
- `tests/orchestrator/test_clause_engine_pass2.py` — Pass 2
