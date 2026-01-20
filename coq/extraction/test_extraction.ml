(** * Extraction Tests
    
    Test suite for extracted code and runtime bridge.
*)

open Runtime_bridge

(** Test gate validation *)
let test_gate_validation () =
  print_endline "Testing gate validation...";
  
  (* Valid gate *)
  try
    let _gate = verified_gate 
      "G_ATTEND:001" 
      "السلام"  (* reality: Arabic text *)
      "main_executor" (* brain *)
      "text_channel"  (* sensing *)
      ["SIGNIFIER:FATHA"; "SIGNIFIER:KASRA"] (* prior knowledge *) in
    print_endline "  ✓ Valid gate accepted";
    true
  with ArchitecturalViolation msg ->
    print_endline ("  ✗ Valid gate rejected: " ^ msg);
    false

(** Test gate rejection - empty reality *)
let test_gate_rejection_reality () =
  print_endline "Testing gate rejection (empty reality)...";
  try
    let _gate = verified_gate "G_TEST:001" "" "executor" "channel" ["lex1"] in
    print_endline "  ✗ Empty reality accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Empty reality rejected: " ^ msg);
    true

(** Test gate rejection - empty prior knowledge *)
let test_gate_rejection_prior () =
  print_endline "Testing gate rejection (empty prior knowledge)...";
  try
    let _gate = verified_gate "G_TEST:002" "reality" "executor" "channel" [] in
    print_endline "  ✗ Empty prior knowledge accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Empty prior knowledge rejected: " ^ msg);
    true

(** Test trace validation *)
let test_trace_validation () =
  print_endline "Testing trace validation...";
  try
    let _trace = verified_trace
      "TRACE:123"
      [("G_ATTEND:001", "reality", "brain", "sensing", ["lex1"])]
      ["SIGNIFIER:FATHA"] in
    print_endline "  ✓ Valid trace accepted";
    true
  with ArchitecturalViolation msg ->
    print_endline ("  ✗ Valid trace rejected: " ^ msg);
    false

(** Test trace rejection - no gates *)
let test_trace_rejection_no_gates () =
  print_endline "Testing trace rejection (no gates)...";
  try
    let _trace = verified_trace "TRACE:124" [] ["lex1"] in
    print_endline "  ✗ Trace without gates accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Trace without gates rejected: " ^ msg);
    true

(** Test trace rejection - no prior_ids *)
let test_trace_rejection_no_prior_ids () =
  print_endline "Testing trace rejection (no prior_ids)...";
  try
    let _trace = verified_trace
      "TRACE:125"
      [("G_ATTEND:001", "reality", "brain", "sensing", ["lex1"])]
      [] in
    print_endline "  ✗ Trace without prior_ids accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Trace without prior_ids rejected: " ^ msg);
    true

(** Test meaning validation *)
let test_meaning_validation () =
  print_endline "Testing meaning validation...";
  try
    let _meaning = verified_meaning
      "MEANING:456"
      "TRACE:123"
      "book"
      ["SIGNIFIED:KITAB:BOOK"]
      [("CLASSICAL_CORPUS", 1.0)] in
    print_endline "  ✓ Valid meaning accepted";
    true
  with ArchitecturalViolation msg ->
    print_endline ("  ✗ Valid meaning rejected: " ^ msg);
    false

(** Test meaning rejection - no trace *)
let test_meaning_rejection_no_trace () =
  print_endline "Testing meaning rejection (no trace)...";
  try
    let _meaning = verified_meaning
      "MEANING:457"
      ""  (* NO C3 without C2 *)
      "concept"
      ["lex1"]
      [("source", 1.0)] in
    print_endline "  ✗ Meaning without trace accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Meaning without trace rejected: " ^ msg);
    true

(** Test meaning rejection - no evidence *)
let test_meaning_rejection_no_evidence () =
  print_endline "Testing meaning rejection (no evidence)...";
  try
    let _meaning = verified_meaning
      "MEANING:458"
      "TRACE:123"
      "concept"
      []  (* NO meaning without evidence *)
      [("source", 1.0)] in
    print_endline "  ✗ Meaning without evidence accepted (should fail)";
    false
  with ArchitecturalViolation msg ->
    print_endline ("  ✓ Meaning without evidence rejected: " ^ msg);
    true

(** Run all tests *)
let () =
  print_endline "=================================";
  print_endline "FractalHub Extraction Test Suite";
  print_endline "=================================";
  print_endline "";
  
  let tests = [
    ("Gate Validation", test_gate_validation);
    ("Gate Rejection (Reality)", test_gate_rejection_reality);
    ("Gate Rejection (Prior Knowledge)", test_gate_rejection_prior);
    ("Trace Validation", test_trace_validation);
    ("Trace Rejection (No Gates)", test_trace_rejection_no_gates);
    ("Trace Rejection (No Prior IDs)", test_trace_rejection_no_prior_ids);
    ("Meaning Validation", test_meaning_validation);
    ("Meaning Rejection (No Trace)", test_meaning_rejection_no_trace);
    ("Meaning Rejection (No Evidence)", test_meaning_rejection_no_evidence);
  ] in
  
  let results = List.map (fun (name, test_fn) ->
    print_endline "";
    test_fn ()
  ) tests in
  
  let passed = List.fold_left (fun acc result -> if result then acc + 1 else acc) 0 results in
  let total = List.length tests in
  
  print_endline "";
  print_endline "=================================";
  Printf.printf "Results: %d/%d tests passed\n" passed total;
  print_endline "=================================";
  
  if passed = total then begin
    print_endline "✅ All tests passed!";
    exit 0
  end else begin
    print_endline "❌ Some tests failed";
    exit 1
  end
