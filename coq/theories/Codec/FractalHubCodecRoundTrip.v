From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Arith.
Import ListNotations.

Require Import FractalHub.Core.FractalHubSpec.
Module FractalHubSpec := FractalHub.Core.FractalHubSpec.

Module FractalHubCodecRoundTrip.

(* Encoding mode *)
Inductive Mode := Vowelled | Unvowelled.

(* Normalization removes diacritics in unvowelled mode *)
Definition normalize_token (t : FractalHubSpec.PositionToken) (m : Mode)
  : FractalHubSpec.PositionToken :=
  match m with
  | Vowelled => t
  | Unvowelled =>
      let au := FractalHubSpec.unpack_position t in
      {|
        FractalHubSpec.unpack_position := {|
          FractalHubSpec.consonant_code := FractalHubSpec.consonant_code au;
          FractalHubSpec.vowel_code := 0;
          FractalHubSpec.position_index := FractalHubSpec.position_index au
        |}
      |}
  end.
  End FractalHubCodecRoundTrip.