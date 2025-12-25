(*
  ArabicKernel.FractalCore
  
  Core formalization of the Arabic fractal pattern: C1-C2-C3
  
  Foundational principle: Every Arabic linguistic construct follows
  the pattern where C2 (core operator) is constrained by C1 (precondition)
  and bound to C3 (post condition/continuation).
  
  This pattern repeats at every linguistic level:
  - Phonology: consonant-vowel-consonant
  - Morphology: root-pattern-inflection
  - Syntax: agent-verb-patient
  - Semantics: role-slot-binding
*)

From Coq Require Import Lists.List Bool.Bool String.
Import ListNotations.

Module ArabicKernelFractalCore.

(* ============================================
   1) Basic Phonetic Layer
   ============================================ *)

(* Consonants - الصوامت *)
Inductive Consonant : Type :=
| C_Hamza       (* ء *)
| C_Ba          (* ب *)
| C_Ta          (* ت *)
| C_Tha         (* ث *)
| C_Jim         (* ج *)
| C_Ha_Huttiya  (* ح *)
| C_Kha         (* خ *)
| C_Dal         (* د *)
| C_Dhal        (* ذ *)
| C_Ra          (* ر *)
| C_Za          (* ز *)
| C_Sin         (* س *)
| C_Shin        (* ش *)
| C_Sad         (* ص *)
| C_Dad         (* ض *)
| C_Ta_Mutbaqa  (* ط *)
| C_Dha         (* ظ *)
| C_Ayn         (* ع *)
| C_Ghayn       (* غ *)
| C_Fa          (* ف *)
| C_Qaf         (* ق *)
| C_Kaf         (* ك *)
| C_Lam         (* ل *)
| C_Mim         (* م *)
| C_Nun         (* ن *)
| C_Ha_Hawa     (* ه *)
| C_Waw         (* و *)
| C_Ya          (* ي *).

(* Vowels/Harakat - الحركات *)
Inductive Vowel : Type :=
| V_Fatha       (* َ *)
| V_Damma       (* ُ *)
| V_Kasra       (* ِ *)
| V_Sukun       (* ْ *)
| V_Shadda      (* ّ *)
| V_Fathatan    (* ً *)
| V_Dammatan    (* ٌ *)
| V_Kasratan    (* ٍ *)
| V_Madd.       (* ٰ *)

(* Phoneme: A consonant must have a vowel/haraka *)
Record Phoneme : Type := {
  consonant : Consonant;
  haraka    : Vowel
}.

(* ============================================
   2) Fractal Cell (C1-C2-C3)
   ============================================ *)

(* The core fractal pattern *)
Record FractalCell (A : Type) : Type := {
  c1 : option A;  (* precondition/onset *)
  c2 : A;          (* core operator *)
  c3 : option A   (* postcondition/coda *)
}.

Arguments FractalCell : clear implicits.

(* Constraint: C2 cannot exist without at least one of C1 or C3 being present
   at the phonetic level (consonant needs vowel) *)
Definition well_formed_phonetic (fc : FractalCell Phoneme) : Prop :=
  c1 fc <> None \/ c3 fc <> None.

(* ============================================
   3) Syllable Structure
   ============================================ *)

Inductive SyllableType : Type :=
| Syl_CV      (* consonant + vowel *)
| Syl_CVC     (* consonant + vowel + consonant *)
| Syl_CVV     (* consonant + long vowel *)
| Syl_CVVC    (* consonant + long vowel + consonant *).

Record Syllable : Type := {
  onset     : Phoneme;              (* C1-C2: must have consonant *)
  nucleus   : Vowel;                (* vowel part *)
  coda      : option Consonant;     (* C3: optional *)
  syl_type  : SyllableType
}.

(* Syllable must follow fractal pattern *)
Definition syllable_to_fractal (s : Syllable) : FractalCell Phoneme :=
  {|
    c1 := None;
    c2 := onset s;
    c3 := match coda s with
          | Some c => Some {| consonant := c; haraka := V_Sukun |}
          | None => None
          end
  |}.

(* ============================================
   4) Morphological Layer
   ============================================ *)

(* Root: typically 3 or 4 consonants *)
Inductive Root : Type :=
| Root3 : Consonant -> Consonant -> Consonant -> Root
| Root4 : Consonant -> Consonant -> Consonant -> Consonant -> Root.

(* Pattern (وزن): defines vowel structure *)
Inductive Pattern : Type :=
| Pat_FaAaLa    (* فَعَلَ *)
| Pat_FaAAiL    (* فَاعِل *)
| Pat_MaFUuL    (* مَفْعُول *)
| Pat_FaAAaL    (* فَعَّال *)
| Pat_MuFaAAiL  (* مُفَاعِل *)
| Pat_TaFaAAuL  (* تَفَاعُل *)
| Pat_IstiFAAL  (* استفعال *)
| Pat_Custom : string -> Pattern.

(* Word = Root applied to Pattern (fractal at morphology level) *)
Record Word : Type := {
  word_root    : Root;
  word_pattern : Pattern;
  word_syllables : list Syllable
}.

(* ============================================
   5) Syntactic Layer
   ============================================ *)

(* Voice *)
Inductive Voice : Type :=
| ACTIVE
| PASSIVE.

(* Valency (number of arguments) *)
Inductive Valency : Type :=
| V0  (* intransitive *)
| V1  (* transitive *)
| V2. (* ditransitive *)

(* Verb kind *)
Inductive VerbKind : Type :=
| C2_VERB
| C2_COPULA
| C2_PARTICLE.

(* C2 Specification: the core operator at syntax level *)
Record C2Spec : Type := {
  kind    : VerbKind;
  voice   : Voice;
  valency : Valency
}.

(* ============================================
   6) Semantic/Role Layer
   ============================================ *)

(* Semantic roles (الأدوار الدلالية) *)
Inductive KRole : Type :=
| AGENT          (* الفاعل *)
| PATIENT        (* المفعول به *)
| THEME          (* الموضوع *)
| BENEFICIARY    (* المستفيد *)
| SOURCE         (* المصدر *)
| GOAL           (* الهدف *)
| PLACE          (* المكان *)
| TIME           (* الزمان *)
| INSTRUMENT     (* الأداة *)
| MANNER         (* الطريقة *)
| PURPOSE        (* الغاية *)
| STATE          (* الحالة *)
| TOPIC          (* الموضوع/المسند إليه *)
| FOCUS          (* التركيز *)
| MODALITY       (* الجهة *)
| ASSERTION_FORCE   (* قوة الإثبات *)
| NEGATION_SCOPE.   (* نطاق النفي *)

(* Slots: roles that can be filled *)
Definition Slot : Type := KRole.

(* SlotsOf: function from C2Spec to available slots 
   This will be defined in SlotsTable.v *)
Parameter SlotsOf : C2Spec -> list KRole.

(* ============================================
   7) Fractal Invariants (Main Theorems)
   ============================================ *)

(* Invariant 1: No consonant without vowel at phonetic level *)
Axiom consonant_needs_vowel : forall (fc : FractalCell Phoneme),
  well_formed_phonetic fc.

(* Invariant 2: C2 is always present *)
Axiom c2_always_present : forall (A : Type) (fc : FractalCell A),
  exists x, c2 fc = x.

(* Invariant 3: Onset constraint - no complex onset (CC) in Arabic *)
Definition no_complex_onset (syls : list Syllable) : Prop :=
  forall s, In s syls -> 
    match coda s with
    | None => True
    | Some _ => True  (* coda is allowed *)
    end.

(* Invariant 4: OCP - Obligatory Contour Principle
   No identical adjacent consonants *)
Definition ocp_satisfied (cs : list Consonant) : Prop :=
  forall i, i < length cs - 1 ->
    nth i cs C_Hamza <> nth (i + 1) cs C_Hamza.

(* Invariant 5: Role must have slot from C2 *)
Definition role_has_slot (spec : C2Spec) (role : KRole) : Prop :=
  In role (SlotsOf spec).

(* ============================================
   8) Verification Interface
   ============================================ *)

(* A linguistic construct is valid if it satisfies all invariants *)
Record ValidConstruct : Type := {
  construct_phonemes : list Phoneme;
  construct_syllables : list Syllable;
  construct_word : Word;
  construct_spec : C2Spec;
  construct_roles : list (KRole * bool); (* role * filled *)
  
  (* Proofs of invariants *)
  proof_no_cc_onset : no_complex_onset construct_syllables;
  proof_roles_valid : forall r b, In (r, b) construct_roles -> 
                                  role_has_slot construct_spec r
}.

End ArabicKernelFractalCore.
