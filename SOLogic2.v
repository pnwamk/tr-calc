

(*
Second order logic

TODO:
1. Make this a module/section/whatever.

*)

Set Implicit Arguments.

Require Import LibTactics.
Require Import Relations.
Require Import List.
Require Import ListSet.
Require Import Program.Wf.
Require Import LibTactics.
Require Import Bool.

Open Scope list_scope.

Variable id : Type.
Hypothesis id_eqdec : forall x y : id, 
                       {x=y}+{x<>y}.
Hint Resolve id_eqdec.

Variable X : Type.
Hypothesis X_eqdec : forall x y : X, 
                       {x=y}+{x<>y}.
Hint Resolve X_eqdec.
Hint Resolve bool_dec.

Record fact : Type := mkFact {
  fvar  : id;
  fprop : X
}.

Theorem fact_eqdec : forall x y : fact,
{x=y}+{x<>y}.
Proof.
  decide equality.
Defined.
Hint Resolve fact_eqdec.

(*
Variable Merge : X -> X -> X.

Variable Sub : relation X.
Hypothesis Sub_dec : forall (x y : X), 
                     {Sub x y} + {~Sub x y}.
<<<<<<< HEAD
*)

Inductive ff : Set :=.

Inductive ψ : Type :=
| ψfact : bool -> fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ff -> ψ
| ψtt   : ψ.
(* Bookmark - Changing ψ-names. I just added an actual
   way to prove false. Lets see if that and perhaps another
   simple addition help create a decidable logic provable as
   an Inductive Prop. *)
Theorem ψ_eqdec : forall p1 p2 : ψ,
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality. inversion f.
Defined.
Hint Resolve ψ_eqdec.

Inductive Atomic : ψ -> Prop :=
| A_True  : Atomic ψtt
| A_Fact  : forall b f, Atomic (ψfact b f).


Inductive Proves : list ψ -> ψ -> Prop :=
| L_Atom : 
    forall E p, 
      In p E -> Proves E p
| L_True :
    forall E, 
      Proves E ψtt
| L_False :
    forall E p contra,
      Proves E (ψff contra) ->
      Proves E p
| L_AndI :
    forall E p q,
      Proves E p ->
      Proves E q ->
      Proves E (ψand p q)
| L_AndE_l :
    forall E p q r,
      Proves (p :: E) r ->
      Proves ((ψand p q) :: E) r
| L_AndE_r :
    forall E p q r,
      Proves (q :: E) r ->
      Proves ((ψand p q) :: E) r
| L_ImpI :
    forall E p q,
      Proves (p :: E) q ->
      Proves E (ψimpl p q)
| L_ImpE :
    forall E p q,
      Proves E p ->
      Proves E (ψimpl p q) ->
      Proves E q
| L_OrI_l :
    forall E p q,
      Proves E p ->
      Proves E (ψor p q)
| L_OrI_r :
    forall E p q,
      Proves E q ->
      Proves E (ψor p q)
| L_OrE :
    forall E p q r,
      Proves (p :: E) r ->
      Proves (q :: E) r ->
      Proves ((ψor p q) :: E) r.
Hint Constructors Proves.

Theorem Proves_nil_dec : forall p,
{Proves nil p} + {~Proves nil p}.
Proof.
  induction p.
  right. intros contra.
  inversion contra; subst. tryfalse. inversion contra0.
  
Abort.
  
