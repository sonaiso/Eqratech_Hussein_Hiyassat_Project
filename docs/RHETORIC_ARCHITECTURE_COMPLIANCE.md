# Rhetoric Layer (Layer 5) — Architecture Compliance

This document records how each rhetoric rule complies with the strict layer order:
**Phonology → Morphology → Lexicon/Operators → Syntax → Rhetoric → Generation.**

Rhetoric must **consume** outputs from earlier layers (Lexicon, Syntax, sentence classification) and **not** re-invent or contradict them.

---

## Layer authority

- **Layer 3 (Lexicon):** Operator/particle identity (لا، هل، يا، إنّ، لعل، ليت، إنما، والله، …).
- **Layer 4 (Syntax / Sentence classification):** Sentence type (استفهام، نداء، قسم، توكيد، ترجي، تمني، أمر، نهي).
- **Layer 5 (Rhetoric):** Map structured results to rhetorical signals (interrogative, vocative, oath, emphasis, etc.) and attach confidence/evidence.

---

## Per-signal compliance

| Rule name        | Owning layer | Dependencies on earlier layers | Primary vs fallback | Duplicates earlier? |
|------------------|-------------|--------------------------------|----------------------|----------------------|
| **Interrogative** | Layer 5    | Layer 3: token as operator (استفهام). Layer 4: sentence_type = استفهام. | **Primary:** sentence_type or operator effect from Lexicon. **Fallback:** raw token in {هل، من، ما، …} only when word_analyses not provided. | No, when primary path used. Fallback is documented. |
| **Vocative**      | Layer 5    | Layer 3: يا (and like) as operator. Layer 4: sentence_type = نداء. | **Primary:** sentence_type or operator from Lexicon. **Fallback:** raw token يا when no context. | No, when primary. |
| **Oath**          | Layer 5    | Layer 3: والله، بالله، تالله as operators. Layer 4: sentence_type = قسم. | **Primary:** sentence_type or operator from Lexicon. **Fallback:** raw token match only without context. | No, when primary. |
| **Tarajji**       | Layer 5    | Layer 3: لعل (and variants) as operator. Layer 4: sentence_type = ترجي. | **Primary:** sentence_type or operator. **Fallback:** raw لعل when no context. | No, when primary. |
| **Tamanni**       | Layer 5    | Layer 3: ليت as operator. Layer 4: sentence_type = تمني. | **Primary:** sentence_type or operator. **Fallback:** raw ليت when no context. | No, when primary. |
| **Exclusivity**   | Layer 5    | Layer 3: إنما / أنما as operator. Syntax: ما … إلا pattern. | **Primary:** operator from Lexicon for إنما. **Fallback:** raw إنما or ما…إلا when no context. | No, when primary. |
| **Emphasis**      | Layer 5    | Layer 3: إنّ، أنّ، لقد as operators. Layer 4: sentence_type = توكيد. Morphology: نون التوكيد on verb (optional). | **Primary:** sentence_type توكيد or operator. **Fallback:** raw إن/أن/لقد; ل+همزة on **non-operator** token only (لا must never be lam al-tawkid). Nun al-tawkid from token shape only when morphology does not provide it. | No, when primary. **Critical:** لا is operator (Layer 3); rhetoric must never treat it as لام التوكيد. |
| **Imperative**    | Layer 5    | Layer 4: sentence_type = أمر. | **Primary only:** from sentence classification. No raw-token imperative detection in rhetoric. | No. |
| **Prohibition**   | Layer 5    | Layer 3: لا as operator. Layer 4: sentence_type = نهي (syntax/context). | **Primary only:** from sentence_type. Trigger token (لا) from Lexicon/word_analyses for span. | No. |

---

## Cross-layer discipline

- **No duplicated logic:** Interrogative/vocative/oath/tarajji/tamanni/exclusivity/emphasis are first derived from `sentence_type` (Layer 4) or from `word_analyses[i].kind` / `word_analyses[i].operator` (Layer 3). Raw-token matching runs only when `word_analyses` is not provided (explicit fallback).
- **No context theft:** Rhetoric does not interpret "لا" as emphasis (lam al-tawkid). If a token is classified as **operator** by Lexicon, rhetoric will not apply لام التوكيد to that token.
- **Earlier layer wins:** If Lexicon marks a token as operator, rhetoric uses that for signal type/trigger/span; it does not override with a different interpretation from token shape.
- **Fallback:** When rhetoric is invoked without `word_analyses` (e.g. standalone call), it may use documented raw-token fallbacks so that signals still appear; these are clearly marked as fallback in evidence and do not contradict Layer 3 when context is later available.

---

## Implementation notes

- `RhetoricSignalsExtractor.extract(tokens, sentence_type=..., word_analyses=...)` accepts optional `word_analyses` (list of c2b word dicts aligned with `tokens`).
- When `word_analyses` is provided, signals are derived from `sentence_type` and from `w["kind"]` / `w.get("operator")`; raw-token checks are skipped for operator-classified tokens and only used where no structured info exists.
- Lam al-tawkid: only considered for token at index `i` when `word_analyses` is None or `word_analyses[i].get("kind") != "operator"`.
