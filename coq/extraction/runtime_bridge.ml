(** * Runtime Bridge
    
    Bridge between extracted Coq code and runtime validation.
    Implements the link-time verification layer (Tier 2 of 3-tier system).
*)

(** Exception for architectural violations *)
exception ArchitecturalViolation of string

(** Validate four conditions at runtime *)
let validate_four_conditions reality brain sensing prior_knowledge =
  if reality = "" then
    raise (ArchitecturalViolation "Reality (form_stream) cannot be empty")
  else if brain = "" then
    raise (ArchitecturalViolation "Brain (executor) cannot be empty")
  else if sensing = "" then
    raise (ArchitecturalViolation "Sensing (channel) cannot be empty")
  else if List.length prior_knowledge = 0 then
    raise (ArchitecturalViolation "Prior Knowledge (lexicon_ids/ruleset_ids) cannot be empty")
  else
    true

(** Validate trace has required components *)
let validate_trace gates prior_ids =
  if List.length gates = 0 then
    raise (ArchitecturalViolation "Trace must have at least one gate (NO C2 without gates)")
  else if List.length prior_ids = 0 then
    raise (ArchitecturalViolation "Trace must have prior_ids (NO meaning without evidence)")
  else
    true

(** Validate meaning has trace *)
let validate_meaning_has_trace trace_id =
  if trace_id = "" then
    raise (ArchitecturalViolation "Meaning must have trace_id (NO C3 without C2)")
  else
    true

(** Validate meaning has evidence *)
let validate_meaning_has_evidence prior_ids =
  if List.length prior_ids = 0 then
    raise (ArchitecturalViolation "Meaning must have prior_ids (NO meaning without evidence)")
  else
    true

(** Build a validated gate *)
let make_validated_gate gate_id reality brain sensing prior_knowledge =
  if validate_four_conditions reality brain sensing prior_knowledge then
    (gate_id, reality, brain, sensing, prior_knowledge)
  else
    failwith "Unreachable: validation failed"

(** Build a validated trace *)
let make_validated_trace trace_id gates prior_ids =
  if validate_trace gates prior_ids then
    (trace_id, gates, prior_ids)
  else
    failwith "Unreachable: validation failed"

(** Build a validated meaning *)
let make_validated_meaning meaning_id trace_id concept prior_ids provenance =
  if validate_meaning_has_trace trace_id then
    if validate_meaning_has_evidence prior_ids then
      (meaning_id, trace_id, concept, prior_ids, provenance)
    else
      failwith "Unreachable: evidence validation failed"
  else
    failwith "Unreachable: trace validation failed"

(** Export validated constructors *)
let verified_gate = make_validated_gate
let verified_trace = make_validated_trace
let verified_meaning = make_validated_meaning
