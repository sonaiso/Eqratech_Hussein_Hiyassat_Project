# Stage L10B — Deep Dependency Syntax Engine

## Why L10B Instead of Replacing L10

L10 (Syntax) remains the **shallow/legacy** syntax layer: word_forms and isnadi links from the existing FVAFK syntax adapter. L10B is a **controlled upgrade** that builds a dependency-oriented representation on top of L10 and other pipeline outputs, without rewriting the whole project. L10 and L10B **coexist**: L10 stays as primary syntax evidence for backward compatibility; L10B provides deeper structure (dependency nodes, edges, clause units, attachments) for i3rab, analogical reasoning, and cognitive fusion.

## Placement

- **After:** L10_SYNTAX  
- **Before:** L11_I3RAB  

L10B reads only from existing structured outputs (L2, L4, L5, L8, L9, L10). It does not re-run raw analyzers or parse raw text independently.

## Supported Relation Types

Controlled label set (stable, documented):

| Label | Description |
|-------|-------------|
| fa'il | Subject (verb → subject) |
| naib_fa'il | Substitute subject (passive) |
| maf'ul_bih | Object (verb → object) |
| mubtada | Topic (nominal sentence) |
| khabar | Predicate (nominal sentence) |
| naat | Adjective (noun → adjective) |
| idafa | Idafa complement (noun → noun) |
| harf_jar | Preposition |
| majrur | Object of preposition |
| zarf | Adverbial |
| jar_majrur_attachment | PP attachment |
| hal_candidate | Circumstantial accusative (candidate) |
| shart_marker | Conditional marker |
| jawab_shart_candidate | Apodosis of condition (candidate) |
| sila_candidate | Relative clause (candidate) |
| atf_candidate | Coordination (candidate) |
| unknown | Unresolved |

## Confidence Model

Deterministic bands (never 1.0; never 0.0 for existing candidate relations):

- **0.90** — Strong local rule with agreement (e.g. L10 isnadi with high confidence)
- **0.75** — Good pattern/rule match (e.g. harf_jar + majrur)
- **0.55** — Candidate relation (e.g. idafa from adjacent nouns)
- **0.30** — Weak tentative relation

## Clause Model

- **clause_units**: main clause plus optional conditional/jawab_shart, hal, sila, etc.
- **main_clause_type**: nominal | verbal | mixed | unknown (from L10 links and token sequence).
- Conditional: simple شرط/جواب الشرط boundaries when the sentence starts with لو / إن / إذا.

## Output Shape

- **dependency_nodes**: token_id, surface, pos_hint, head_id, relation, confidence, status (resolved | candidate | unresolved).
- **dependency_edges**: from_id, to_id, relation, confidence, status (resolved | candidate).
- **clause_units**: clause_id, type, start_token_id, end_token_id, head_token_id.
- **attachments**: token_id, attached_to, attachment_type, confidence.
- **syntax_summary**: resolved_edges, candidate_edges, unresolved_tokens, main_clause_type.

## Limitations

- **No full Arabic parse**: Partial but reliable structure; many tokens may remain unresolved.
- **Rule-based only**: No ML or corpus lookup; deterministic heuristics from L10 + morphology.
- **Uncertain relations** are marked **candidate**, not final.
- **Idafa/naat** use simple adjacency and POS hints; agreement is not fully modeled.
- **Conditional/clause boundaries** are best-effort (e.g. لو at start).

## Interaction with L11 and Fusion

- **L11 (i3rab)**: Reads L10B when present; adds `dependency_head_id` and `dependency_relation` to each token_result from L10B dependency_nodes. L11 remains primarily text-based (c2e i3rab_text).
- **Cognitive fusion**: Can use L10B dependency_nodes/edges as stronger syntax evidence in hierarchy (e.g. SYNTAX weight); fusion is not refactored here, only L10B is added.
- **Pre-Stage-13 audit**: L10B is included as a source (DEEP_SYNTAX); resolved_edges contribute to readiness.
