(*
  ArabicKernel.SlotsTable
  A non-lexical, strong baseline for SlotsOf.
  - Works by C2Spec (kind/valency/voice/pattern) + generic particle "families".
  - Keeps the kernel small: this table can evolve without changing proofs elsewhere.

  NOTE:
  - For full-text processing you still need an external elaborator that maps tokens
    to C2Spec values (valency/voice/pattern/particle family).
  - This table provides *license sets* once C2Spec is known.
*)

From Coq Require Import Lists.List Bool.Bool.
Import ListNotations.

From ArabicKernel Require Import ArabicKernel.FractalCore.
From ArabicKernel Require Import ArabicKernel.Roles.

Module ArabicKernelSlotsTable.
Import ArabicKernelFractalCore.
Import ArabicKernelRoles.

(* --------
   1) Particle families (coarse but powerful)
   -------- *)

Inductive ParticleFamily : Type :=
| PF_SOURCE        (* من *)
| PF_GOAL          (* إلى / حتى *)
| PF_LOCATION      (* في / على *)
| PF_INSTRUMENT    (* بـ *)
| PF_BENEFICIARY   (* لـ *)
| PF_PURPOSE       (* كي / لام التعليل *)
| PF_CONDITION     (* إن / لو *)
| PF_NEGATION      (* ما/لا/لم/لن ... *)
| PF_CONJUNCTION   (* و/ف/ثم *)
| PF_EXCEPTION     (* إلا/حاشا/خلا/عدا *)
| PF_EMPHASIS      (* إنّ/أنّ/قد/لام التوكيد *)
| PF_QUESTION      (* هل/أ/أين/متى... *)
| PF_CALLING       (* يا *)
| PF_OATH.         (* واو القسم/تاء القسم *)

(* Extend C2Spec with a particle family when kind = C2_PARTICLE *)
Record C2SpecX : Type := {
  base : C2Spec;
  pfam : option ParticleFamily
}.

Definition is_particle (c2 : C2SpecX) : bool :=
  match kind (base c2) with
  | C2_PARTICLE => true
  | _ => false
  end.

(* --------
   2) Baseline SlotsOf (Definition)
   -------- *)

Definition SlotsOf_base (c2 : C2Spec) : list KRole :=
  match kind c2 with
  | C2_VERB =>
      match voice c2 with
      | ACTIVE =>
          match valency c2 with
          | V0 => [AGENT; TIME]
          | V1 => [AGENT; PATIENT; TIME]
          | V2 => [AGENT; THEME; BENEFICIARY; TIME]
          end
      | PASSIVE =>
          (* Passive promotes PATIENT/THEME and hides explicit AGENT *)
          match valency c2 with
          | V0 => [TIME]  (* passive in V0 is unusual; keep minimal *)
          | V1 => [PATIENT; TIME]
          | V2 => [THEME; BENEFICIARY; TIME]
          end
      end
  | C2_COPULA =>
      (* "كان وأخواتها" and copular predicates *)
      [AGENT; STATE; TIME]
  | C2_PARTICLE =>
      (* Without particle family, allow only generic pragmatic roles *)
      [ASSERTION_FORCE; MODALITY; NEGATION_SCOPE]
  end.

Definition SlotsOf_particle (pf : ParticleFamily) : list KRole :=
  match pf with
  | PF_SOURCE      => [SOURCE]
  | PF_GOAL        => [GOAL]
  | PF_LOCATION    => [PLACE]
  | PF_INSTRUMENT  => [INSTRUMENT]
  | PF_BENEFICIARY => [BENEFICIARY]
  | PF_PURPOSE     => [PURPOSE]
  | PF_CONDITION   => [MODALITY; ASSERTION_FORCE] (* used to open conditional scope *)
  | PF_NEGATION    => [NEGATION_SCOPE]
  | PF_CONJUNCTION => [ASSERTION_FORCE] (* structural link; semantics later *)
  | PF_EXCEPTION   => [ASSERTION_FORCE] (* scopal; semantics later *)
  | PF_EMPHASIS    => [ASSERTION_FORCE]
  | PF_QUESTION    => [ASSERTION_FORCE; FOCUS]
  | PF_CALLING     => [TOPIC]
  | PF_OATH        => [ASSERTION_FORCE]
  end.

Definition SlotsOfX (c2x : C2SpecX) : list KRole :=
  match kind (base c2x) with
  | C2_PARTICLE =>
      match pfam c2x with
      | Some pf => SlotsOf_particle pf
      | None    => SlotsOf_base (base c2x)
      end
  | _ => SlotsOf_base (base c2x)
  end.

(* --------
   3) Bridge: provide SlotsOf as required by ArabicKernelRoles
   --------
   We *define* SlotsOf here and can later switch back to Parameter if desired.
*)

Module ProvideSlotsOf.
  (* Override the parameter by a definition in a dedicated module. *)
  Definition SlotsOf (c2 : C2Spec) : list KRole := SlotsOf_base c2.
End ProvideSlotsOf.

End ArabicKernelSlotsTable.
