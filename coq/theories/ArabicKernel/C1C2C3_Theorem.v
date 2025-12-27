(*
  ArabicKernel.C1C2C3_Theorem
  
  Formal specification of the C1-C2-C3 consciousness-inspired architecture
  for Arabic linguistic kernel.
  
  Core idea:
  - C2 (Reality): Entity/state in the world (physical/conceptual model)
  - C1 (Concept): Concept that refers to reality (may be accurate or not)
  - C3 (Language): Linguistic representation expressing the concept
  
  Structural integration (consciousness simulation):
  - No language without concept
  - No concept without reality reference (at least as C2-Model)
  - C3 is "naming/expression", not reality itself
  
  The consonant-vowel constraint is a miniature model of the same idea:
  - A consonant alone is "unpronunceable/unverifiable"
  - Needs a vowel before or after to become structurally valid
  - Parallels: any symbol in C3 needs C2 "nucleus" (reference/anchor)
    and C1 "concept" to be acceptable as representation
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

Import ListNotations.

Module C1C2C3_Theorem.

(* ========================= *)
(* 0) SAFE arithmetic tactic *)
(* ========================= *)
(* Only use lia for arithmetic - it's a decision procedure, but approved *)
Ltac FVAFK_lia := lia.

(* ========================= *)
(* 1) TYPES: C1 / C2 / C3    *)
(* ========================= *)

(* C2: Reality model (could be physical/world entity id) *)
Record Reality := MkReality { 
  r_id : nat 
}.

(* C1: Concept (semantic/intensional entity) *)
Record Concept := MkConcept { 
  c_id : nat 
}.

(* C3: Language token / statement id *)
Record Language := MkLanguage { 
  l_id : nat 
}.

(* Core relations *)
Record Link := MkLink {
  L_c1 : Concept;
  L_c2 : Reality;
  L_c3 : Language;

  (* "has nucleus": kernel insists nucleus present (C2 anchor) *)
  nucleus_trace : nat;   (* abstract trace id; 0 means missing *)

  (* "evidence": at least one outer context (C1 or C3) present *)
  outer_context : nat    (* 0 = none, >0 = present *)
}.

(* ========================= *)
(* 2) PHONETIC LAYER         *)
(* ========================= *)

(* Simplified phonetic representation *)
Inductive PhoneticUnit : Type :=
| Consonant (c : nat)
| Vowel (v : nat).

Definition is_consonant (p : PhoneticUnit) : bool :=
  match p with
  | Consonant _ => true
  | Vowel _     => false
  end.

Definition is_vowel (p : PhoneticUnit) : bool :=
  match p with
  | Vowel _     => true
  | Consonant _ => false
  end.

(* ========================= *)
(* 3) BOOLEAN PREDICATES     *)
(* ========================= *)

(* Check if C1 is present (concept exists) *)
Definition C1_present (lnk : Link) : bool :=
  match c_id (L_c1 lnk) with
  | 0    => false
  | S _  => true
  end.

(* Check if C2 is present (reality anchor exists) *)
Definition C2_present (lnk : Link) : bool :=
  match r_id (L_c2 lnk) with
  | 0    => false
  | S _  => true
  end.

(* Check if C3 is present (language token exists) *)
Definition C3_present (lnk : Link) : bool :=
  match l_id (L_c3 lnk) with
  | 0    => false
  | S _  => true
  end.

(* Check nucleus is present *)
Definition nucleus_ok (lnk : Link) : bool :=
  match nucleus_trace lnk with
  | 0    => false
  | S _  => true
  end.

(* Check outer context is present *)
Definition outer_ok (lnk : Link) : bool :=
  match outer_context lnk with
  | 0    => false
  | S _  => true
  end.

(* Link is valid: C2 must be present (nucleus), 
   and at least one of C1/C3 must be present *)
Definition link_ok (lnk : Link) : bool :=
  C2_present lnk && (C1_present lnk || C3_present lnk) && nucleus_ok lnk && outer_ok lnk.

(* ========================= *)
(* 4) CONSONANT-VOWEL CHECK  *)
(* ========================= *)

(* A phonetic sequence is valid if no consonant stands alone *)
Fixpoint has_adjacent_vowel (units : list PhoneticUnit) (idx : nat) : bool :=
  match units with
  | [] => false
  | u :: rest =>
      if Nat.eqb idx 0 then
        (* Check current position *)
        if is_consonant u then
          (* Consonant needs vowel before (impossible at idx 0) or after *)
          match rest with
          | [] => false  (* Consonant at end with nothing after *)
          | next :: _ => is_vowel next
          end
        else
          true  (* Vowel is always ok *)
      else
        has_adjacent_vowel rest (pred idx)
  end.

(* Check entire sequence: every consonant has adjacent vowel *)
Fixpoint no_consonant_without_vowel_check (units : list PhoneticUnit) : bool :=
  match units with
  | [] => true
  | Consonant _ :: [] => false  (* Isolated consonant *)
  | Consonant _ :: Vowel _ :: rest => no_consonant_without_vowel_check rest
  | Vowel _ :: rest => no_consonant_without_vowel_check rest
  | _ => false  (* Other invalid patterns like C C *)
  end.

(* Simplified version: check if sequence has at least one vowel per consonant *)
Fixpoint count_consonants (units : list PhoneticUnit) : nat :=
  match units with
  | [] => 0
  | Consonant _ :: rest => S (count_consonants rest)
  | Vowel _ :: rest => count_consonants rest
  end.

Fixpoint count_vowels (units : list PhoneticUnit) : nat :=
  match units with
  | [] => 0
  | Consonant _ :: rest => count_vowels rest
  | Vowel _ :: rest => S (count_vowels rest)
  end.

(* Simple check: vowels >= consonants (each consonant can have a vowel) *)
Definition enough_vowels (units : list PhoneticUnit) : bool :=
  Nat.leb (count_consonants units) (count_vowels units).

(* ========================= *)
(* 5) PROPOSITIONS           *)
(* ========================= *)

(* Propositional versions of the checks *)
Definition C1_present_prop (lnk : Link) : Prop :=
  c_id (L_c1 lnk) <> 0.

Definition C2_present_prop (lnk : Link) : Prop :=
  r_id (L_c2 lnk) <> 0.

Definition C3_present_prop (lnk : Link) : Prop :=
  l_id (L_c3 lnk) <> 0.

Definition nucleus_ok_prop (lnk : Link) : Prop :=
  nucleus_trace lnk <> 0.

Definition outer_ok_prop (lnk : Link) : Prop :=
  outer_context lnk <> 0.

Definition link_ok_prop (lnk : Link) : Prop :=
  C2_present_prop lnk /\ (C1_present_prop lnk \/ C3_present_prop lnk) 
  /\ nucleus_ok_prop lnk /\ outer_ok_prop lnk.

(* ========================= *)
(* 6) SOUNDNESS THEOREMS     *)
(* ========================= *)

(* Helper lemmas *)
Lemma nat_neq_0_cases : forall n, n <> 0 <-> exists m, n = S m.
Proof.
  intros n.
  split.
  - intros H.
    destruct n.
    + contradiction.
    + exists n. reflexivity.
  - intros [m Heq].
    rewrite Heq.
    discriminate.
Qed.

(* Soundness: C1_present true implies C1_present_prop *)
Theorem C1_present_sound : forall lnk,
  C1_present lnk = true -> C1_present_prop lnk.
Proof.
  intros lnk H.
  unfold C1_present in H.
  unfold C1_present_prop.
  destruct (c_id (L_c1 lnk)) eqn:E.
  - discriminate.
  - discriminate.
Qed.

(* Soundness: C2_present true implies C2_present_prop *)
Theorem C2_present_sound : forall lnk,
  C2_present lnk = true -> C2_present_prop lnk.
Proof.
  intros lnk H.
  unfold C2_present in H.
  unfold C2_present_prop.
  destruct (r_id (L_c2 lnk)) eqn:E.
  - discriminate.
  - discriminate.
Qed.

(* Soundness: C3_present true implies C3_present_prop *)
Theorem C3_present_sound : forall lnk,
  C3_present lnk = true -> C3_present_prop lnk.
Proof.
  intros lnk H.
  unfold C3_present in H.
  unfold C3_present_prop.
  destruct (l_id (L_c3 lnk)) eqn:E.
  - discriminate.
  - discriminate.
Qed.

(* Soundness: nucleus_ok true implies nucleus_ok_prop *)
Theorem nucleus_ok_sound : forall lnk,
  nucleus_ok lnk = true -> nucleus_ok_prop lnk.
Proof.
  intros lnk H.
  unfold nucleus_ok in H.
  unfold nucleus_ok_prop.
  destruct (nucleus_trace lnk) eqn:E.
  - discriminate.
  - discriminate.
Qed.

(* Soundness: outer_ok true implies outer_ok_prop *)
Theorem outer_ok_sound : forall lnk,
  outer_ok lnk = true -> outer_ok_prop lnk.
Proof.
  intros lnk H.
  unfold outer_ok in H.
  unfold outer_ok_prop.
  destruct (outer_context lnk) eqn:E.
  - discriminate.
  - discriminate.
Qed.

(* Main soundness theorem: link_ok true implies link_ok_prop *)
Theorem link_ok_sound : forall lnk,
  link_ok lnk = true -> link_ok_prop lnk.
Proof.
  intros lnk H.
  unfold link_ok in H.
  unfold link_ok_prop.
  (* Decompose the boolean conjunction *)
  apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [H1a H1b].
  apply andb_true_iff in H2 as [H2a H2b].
  
  split.
  - (* C2_present_prop *)
    apply C2_present_sound. exact H1a.
  - split.
    + (* C1_present_prop \/ C3_present_prop *)
      apply orb_true_iff in H1b as [Hc1 | Hc3].
      * left. apply C1_present_sound. exact Hc1.
      * right. apply C3_present_sound. exact Hc3.
    + split.
      * (* nucleus_ok_prop *)
        apply nucleus_ok_sound. exact H2a.
      * (* outer_ok_prop *)
        apply outer_ok_sound. exact H2b.
Qed.

(* ========================= *)
(* 7) FRACTAL ARABIC THEOREM *)
(* ========================= *)

(*
  Main theorem: Every valid linguistic construct in the Arabic kernel
  must satisfy the C1-C2-C3 constraint:
  - C2 (nucleus/reality) must be present
  - At least one of C1 (concept) or C3 (language) must be present
  - This mirrors the phonetic constraint: no consonant without vowel
*)

Theorem Fractal_Arabic_Soundness : forall lnk,
  link_ok lnk = true ->
  C2_present_prop lnk /\ (C1_present_prop lnk \/ C3_present_prop lnk).
Proof.
  intros lnk H.
  apply link_ok_sound in H.
  unfold link_ok_prop in H.
  destruct H as [HC2 [HC1C3 _]].
  split.
  - exact HC2.
  - exact HC1C3.
Qed.

(* Corollary: No isolated C3 without C2 *)
Theorem no_isolated_language : forall lnk,
  link_ok lnk = true -> C3_present_prop lnk -> C2_present_prop lnk.
Proof.
  intros lnk Hlnk HC3.
  apply Fractal_Arabic_Soundness in Hlnk.
  destruct Hlnk as [HC2 _].
  exact HC2.
Qed.

(* Corollary: No isolated C1 without C2 *)
Theorem no_isolated_concept : forall lnk,
  link_ok lnk = true -> C1_present_prop lnk -> C2_present_prop lnk.
Proof.
  intros lnk Hlnk HC1.
  apply Fractal_Arabic_Soundness in Hlnk.
  destruct Hlnk as [HC2 _].
  exact HC2.
Qed.

(* ========================= *)
(* 8) PHONETIC SOUNDNESS     *)
(* ========================= *)

(* If we have more vowels than consonants, 
   it's possible to pair each consonant with a vowel *)
Theorem enough_vowels_sound : forall units,
  enough_vowels units = true ->
  count_vowels units >= count_consonants units.
Proof.
  intros units H.
  unfold enough_vowels in H.
  apply Nat.leb_le in H.
  exact H.
Qed.

(* ========================= *)
(* 9) COMPLETENESS SKETCH    *)
(* ========================= *)

(*
  Note: Full completeness (prop implies bool = true) would require
  that we can decide all these properties, which we can for our
  nat-based definitions. This is left as future work to keep
  the kernel small.
*)

End C1C2C3_Theorem.

(* Export for use in other modules *)
Export C1C2C3_Theorem.
