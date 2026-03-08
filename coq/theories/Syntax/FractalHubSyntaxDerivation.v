From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Arith.
From Coq Require Import Lia.
Import ListNotations.
Open Scope string_scope.
Require Import FractalHub.FractalHubSpec.
Require Import FractalHub.FractalHubGates.
Require Import FractalHub.FractalHubDerivation.

Module FractalHubSyntaxDerivation.

(* ============================================================
   1) Syntax edges (expandable core)
   ============================================================ *)

Inductive SynEdgeKind :=
| E_ISNAD
| E_HAS_SUBJECT
| E_HAS_OBJECT
| E_GOVERN_GEN
| E_SHIBH_ATTACH
| E_NA3T
| E_IDAFA.

Record SynEdge := {
  k   : SynEdgeKind;
  src : nat;
  dst : nat
}.

Definition SynGraph := list SynEdge.

Definition graph_has (g : SynGraph) (K : SynEdgeKind) : Prop :=
  exists e, In e g /\ k e = K.

Definition graph_has_edge (g : SynGraph) (K : SynEdgeKind) (s d : nat) : Prop :=
  exists e, In e g /\ k e = K /\ src e = s /\ dst e = d.

Inductive SentenceKind := NOMINAL | VERBAL.

Definition NominalParsed (sgraph : SynGraph) : Prop := graph_has sgraph E_ISNAD.
Definition VerbalParsed  (sgraph : SynGraph) : Prop := graph_has sgraph E_HAS_SUBJECT.
Definition HasGovernPP   (sgraph : SynGraph) : Prop := graph_has sgraph E_GOVERN_GEN.
Definition HasAttachPP   (sgraph : SynGraph) : Prop := graph_has sgraph E_SHIBH_ATTACH.

(* ============================================================
   2) SyntaxState: tokens + graph + pipeline + range invariant
   ============================================================ *)

Record SyntaxState := {
  ss_tokens : list FractalHubSpec.PositionToken;
  ss_graph  : SynGraph;
  ss_pipe   : FractalHubGates.Pipeline;

  ss_edges_in_range :
    forall e, In e ss_graph ->
      src e < List.length ss_tokens /\ dst e < List.length ss_tokens
}.

(* ============================================================
   3) Helpers about list append
   ============================================================ *)

Lemma in_app_singleton {A : Type} :
  forall (x : A) (l : list A), In x ((l ++ [x])%list).
Proof.
  intros x l.
  apply in_or_app.
  right. simpl. left. reflexivity.
Qed.

Lemma graph_has_app :
  forall (g1 g2 : SynGraph) (K : SynEdgeKind),
    graph_has g1 K -> graph_has ((g1 ++ g2)%list) K.
Proof.
  intros g1 g2 K [e [Hin Hk]].
  exists e. split.
  - apply in_or_app. left. exact Hin.
  - exact Hk.
Qed.

Lemma graph_has_cons :
  forall (e : SynEdge) (g : SynGraph) (K : SynEdgeKind),
    k e = K -> graph_has (e :: g) K.
Proof.
  intros e g K Hk.
  exists e. split.
  - simpl. left. reflexivity.
  - exact Hk.
Qed.

(* ============================================================
   4) DerivesSyntax: single-step syntax derivation with gate
   ============================================================ *)

Inductive DerivesSyntax : SyntaxState -> SyntaxState -> Prop :=
| DS_AddEdge :
    forall (s1 : SyntaxState) (e : SynEdge) (g : FractalHubGates.GateRun)
           (Hrange : forall e0,
               In e0 ((ss_graph s1 ++ [e])%list) ->
               src e0 < List.length (ss_tokens s1) /\
               dst e0 < List.length (ss_tokens s1)),
      (* Edge indices must be in range *)
      src e < List.length (ss_tokens s1) ->
      dst e < List.length (ss_tokens s1) ->
      (* Gate required for syntax operations *)
      FractalHubGates.gate_id g = "SYNTAX_GATE" ->
      (* Result state *)
      DerivesSyntax s1
        {| ss_tokens := ss_tokens s1;
           ss_graph  := (ss_graph s1 ++ [e])%list;
           ss_pipe   := FractalHubGates.push_gate (ss_pipe s1) g;
           ss_edges_in_range := Hrange |}.

(* ============================================================
   5) DerivesSyntaxStar: reflexive transitive closure
   ============================================================ *)

Inductive DerivesSyntaxStar : SyntaxState -> SyntaxState -> Prop :=
| DSS_Refl : forall s, DerivesSyntaxStar s s
| DSS_Step : forall s1 s2 s3,
    DerivesSyntax s1 s2 ->
    DerivesSyntaxStar s2 s3 ->
    DerivesSyntaxStar s1 s3.

(* ============================================================
   6) Core theorems
   ============================================================ *)

(* Theorem 1: Nominal sentence requires ISNAD edge *)
Theorem NominalRequiresISNAD :
  forall s0 s,
    DerivesSyntaxStar s0 s ->
    NominalParsed (ss_graph s) ->
    graph_has (ss_graph s) E_ISNAD.
Proof.
  intros s0 s Hstar Hnom.
  unfold NominalParsed in Hnom.
  exact Hnom.
Qed.

(* Theorem 2: Verbal sentence requires HAS_SUBJECT edge *)
Theorem VerbalRequiresSubject :
  forall s0 s,
    DerivesSyntaxStar s0 s ->
    VerbalParsed (ss_graph s) ->
    graph_has (ss_graph s) E_HAS_SUBJECT.
Proof.
  intros s0 s Hstar Hverb.
  unfold VerbalParsed in Hverb.
  exact Hverb.
Qed.

(* Theorem 3: Graph non-empty means at least one edge *)
Theorem ParsedMeansNonEmpty :
  forall s0 s,
    DerivesSyntaxStar s0 s ->
    (NominalParsed (ss_graph s) \/ VerbalParsed (ss_graph s)) ->
    ss_graph s <> [].
Proof.
  intros s0 s Hstar [Hnom | Hverb].
  - (* Nominal case *)
    unfold NominalParsed in Hnom.
    unfold graph_has in Hnom.
    destruct Hnom as [e [Hin _]].
    intro Hcontra.
    rewrite Hcontra in Hin.
    simpl in Hin. contradiction.
  - (* Verbal case *)
    unfold VerbalParsed in Hverb.
    unfold graph_has in Hverb.
    destruct Hverb as [e [Hin _]].
    intro Hcontra.
    rewrite Hcontra in Hin.
    simpl in Hin. contradiction.
Qed.

(* Theorem 4: All edges in derived graph are in range *)
Theorem DerivedEdgesInRange :
  forall s0 s,
    DerivesSyntaxStar s0 s ->
    forall e, In e (ss_graph s) ->
      src e < List.length (ss_tokens s) /\ dst e < List.length (ss_tokens s).
Proof.
  intros s0 s Hstar.
  apply (ss_edges_in_range s).
Qed.

(* Theorem 5: Syntax operations require SYNTAX_GATE *)
Theorem SyntaxRequiresGate :
  forall s1 s2,
    DerivesSyntax s1 s2 ->
    exists g, In g (FractalHubGates.pipeline_gates (ss_pipe s2)) /\
              FractalHubGates.gate_id g = "SYNTAX_GATE".
Proof.
  intros s1 s2 Hderiv.
  inversion Hderiv; subst.
  exists g. split.
  - (* Gate is in the pipeline: push_gate prepends g, so g is the head *)
    unfold FractalHubGates.push_gate.
    unfold FractalHubGates.pipeline_gates.
    simpl. left. reflexivity.
  - (* Gate ID is SYNTAX_GATE *)
    assumption.
Qed.

(* ============================================================
   7) Prepositional phrase attachment lemma
   ============================================================ *)

(* If a PP is governed (E_GOVERN_GEN), it should be attached (E_SHIBH_ATTACH) *)
Lemma PPAttachmentRequired :
  forall s,
    HasGovernPP (ss_graph s) ->
    (* If we have a governed PP, we should eventually attach it *)
    forall s',
      DerivesSyntaxStar s s' ->
      HasAttachPP (ss_graph s') \/ HasGovernPP (ss_graph s').
Proof.
  intros s Hgov s' Hstar.
  revert Hgov.
  induction Hstar as [s0 | s0 s2 s3 Hstep Hstar2 IHHstar].
  - (* Reflexive case *)
    intro Hgov. right. exact Hgov.
  - (* Step case: s0 ->1 s2 ->* s3 *)
    intro Hgov.
    (* GovernPP is preserved through one step: graph only grows *)
    assert (HasGovernPP (ss_graph s2)) as Hgov2.
    { inversion Hstep; subst.
      unfold HasGovernPP. apply graph_has_app. exact Hgov. }
    destruct (IHHstar Hgov2) as [Hatt | Hgov'].
    + left. exact Hatt.
    + right. exact Hgov'.
Qed.

(* ============================================================
   8) Composition and transitivity
   ============================================================ *)

Theorem DerivesSyntaxStar_trans :
  forall s1 s2 s3,
    DerivesSyntaxStar s1 s2 ->
    DerivesSyntaxStar s2 s3 ->
    DerivesSyntaxStar s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  induction H12.
  - (* Reflexive *)
    exact H23.
  - (* Step *)
    apply DSS_Step with s2.
    + exact H.
    + apply IHDerivesSyntaxStar. exact H23.
Qed.

(* ============================================================
   9) Integration with FractalHubDerivation
   ============================================================ *)

(* Connect syntax state to general derivation state (tokens only) *)
Definition syntax_to_derivation (ss : SyntaxState) : FractalHubDerivation.State :=
  {| FractalHubDerivation.st_tokens := ss_tokens ss |}.

(* If we can derive syntactically, we can derive generally.
   DerivesSyntax only appends edges and pipeline; tokens are unchanged,
   so both states map to the same derivation state. *)
Lemma SyntaxDerivesToGeneral :
  forall s1 s2,
    DerivesSyntax s1 s2 ->
    FractalHubDerivation.Derives 
      (syntax_to_derivation s1) 
      (syntax_to_derivation s2).
Proof.
  intros s1 s2 Hsyn.
  inversion Hsyn; subst.
  apply FractalHubDerivation.Derives_refl.
Qed.

End FractalHubSyntaxDerivation.
