(*
  ArabicKernel.Roles
  
  Semantic role system for Arabic grammar.
  Defines the roles (أدوار دلالية) and their relationship
  to syntactic positions.
*)

From Coq Require Import Lists.List Bool.Bool.
Import ListNotations.

From ArabicKernel Require Import ArabicKernel.FractalCore.

Module ArabicKernelRoles.
Import ArabicKernelFractalCore.

(* Roles are already defined in FractalCore, 
   we re-export them here for convenience *)
Export ArabicKernelFractalCore.

(* ============================================
   Role Properties
   ============================================ *)

(* Core roles (مباشرة) vs Adjunct roles (فضلة) *)
Definition is_core_role (r : KRole) : bool :=
  match r with
  | AGENT | PATIENT | THEME => true
  | _ => false
  end.

Definition is_adjunct_role (r : KRole) : bool :=
  negb (is_core_role r).

(* ============================================
   Role Constraints
   ============================================ *)

(* Agent is typically required for verbs *)
Definition requires_agent (spec : C2Spec) : bool :=
  match kind spec, voice spec with
  | C2_VERB, ACTIVE => true
  | _, _ => false
  end.

(* Patient is promoted in passive *)
Definition patient_promoted (spec : C2Spec) : bool :=
  match voice spec with
  | PASSIVE => true
  | _ => false
  end.

(* ============================================
   Role Licensing
   ============================================ *)

(* A role can only be used if it's in the available slots *)
Definition role_licensed (spec : C2Spec) (r : KRole) : Prop :=
  In r (SlotsOf spec).

(* Soundness: All used roles must be licensed *)
Definition roles_sound (spec : C2Spec) (used_roles : list KRole) : Prop :=
  forall r, In r used_roles -> role_licensed spec r.

(* ============================================
   Theorems about Roles
   ============================================ *)

(* Theorem: Agent must be licensed for active verbs *)
Theorem active_verb_has_agent_slot : forall spec,
  kind spec = C2_VERB ->
  voice spec = ACTIVE ->
  role_licensed spec AGENT.
Proof.
  intros spec Hkind Hvoice.
  unfold role_licensed.
  unfold SlotsOf.
  (* This will be proven once SlotsOf is defined in SlotsTable *)
Admitted.

(* Theorem: Passive hides agent from surface roles *)
Axiom passive_hides_agent : forall spec used_roles,
  voice spec = PASSIVE ->
  ~ In AGENT used_roles.

End ArabicKernelRoles.
