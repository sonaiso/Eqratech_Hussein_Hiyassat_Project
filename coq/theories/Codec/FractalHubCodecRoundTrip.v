(* Normalization removes diacritics in unvowelled mode *)
Definition normalize_token (t : FractalHubSpec.PositionToken) (m : Mode) : FractalHubSpec.PositionToken :=
  match m with
  | Vowelled => t
  | Unvowelled =>
      let au := FractalHubSpec.unpack_position t in
      {|
        FractalHubSpec.unpack_position := {|
          FractalHubSpec.consonant_code := FractalHubSpec.consonant_code au;
          FractalHubSpec.vowel_code := 0;          (* No vowel *)
          FractalHubSpec.position_index := FractalHubSpec.position_index au
        |}
      |}
  end.

(* Encode a PositionToken to an integer *)
Definition encode_position_token (t : FractalHubSpec.PositionToken) : nat :=
  let au := FractalHubSpec.unpack_position t in
  let c := FractalHubSpec.consonant_code au in
  let v := FractalHubSpec.vowel_code au in
  (* There is no shadda/tanwin in the current spec; encode as 0 for now *)
  let s := 0 in
  let tw := 0 in
  (c * 2^21) + (v * 2^17) + (s * 2^16) + (tw * 2^14).

(* Decode an integer back to PositionToken *)
Definition decode_position_token (n : nat) : FractalHubSpec.PositionToken :=
  let c := (n / 2^21) mod 256 in
  let v := (n / 2^17) mod 16 in
  (* shadda/tanwin absent in spec => ignore bits / set to defaults *)
  let pos := 0 in
  {|
    FractalHubSpec.unpack_position := {|
      FractalHubSpec.consonant_code := c;
      FractalHubSpec.vowel_code := v;
      FractalHubSpec.position_index := pos
    |}
  |}.