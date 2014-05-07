

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

Record fact : Type := mkfact {
  fbool : bool;
  fvar  : id;
  fprop : X
}.

Theorem fact_eqdec : forall x y : fact,
{x=y}+{x<>y}.
Proof.
  decide equality.
Defined.
Hint Resolve fact_eqdec.

Inductive Contains {X:Type} : list X -> list X -> Prop :=
| containment : forall l1 l2, 
                  (forall x, In x l1 -> In x l2) ->
                  Contains l1 l2.

Inductive Extends {X:Type} : list X -> X -> list X -> Prop :=
| extension : forall l1 x l2,
                  Contains l1 l2 ->
                  (forall y, ((x <> y) /\ In y l2) -> In y l1) ->
                  In x l2 ->
                  Extends l1 x l2.
                

Inductive ψ : Type :=
| ψfact : fact -> ψ
| ψimp : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ.

Theorem ψ_eqdec : forall p1 p2 : ψ,
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality.
Defined.
Hint Resolve ψ_eqdec.

(* This still has the injection of implications --- bad? Rule just for
present implications (figure out a replacement for L-ImpE? *)

Inductive Proves : list ψ -> ψ -> Prop :=
| L_Atom_fact :
    forall E f,
      In (ψfact f) E ->
      Proves E (ψfact f)
| L_False : 
    forall E f,
      Proves E ψff ->
      Proves E (ψfact f)
| L_AndE_fact_l :
    forall E f Ep p q,
      Extends E p Ep ->
      Proves Ep (ψfact f) ->
      In (ψand p q) E ->
      Proves E (ψfact f)
| L_AndE_fact_r :
    forall E f Eq p q,
      Extends E q Eq ->
      Proves Eq (ψfact f) ->
      In (ψand p q) E ->
      Proves E (ψfact f)
| L_ImpE_fact :
    forall E f p,
      Proves E (ψimp p (ψfact f)) ->
      Proves E p -> 
      Proves E (ψfact f)
| L_OrE_fact :
    forall E Ep Eq p q f,
      Extends E p Ep ->
      Extends E q Eq ->
      Proves Ep (ψfact f) ->
      Proves Eq (ψfact f) ->
      In (ψor p q) E ->
      Proves E (ψfact f)
| L_Imp :
    forall E Ep p q,
      Extends E p Ep ->
      Proves Ep q ->
      Proves E (ψimp p q)
| L_Or_l :
    forall E p q,
     Proves E p ->
     Proves E (ψor p q)
| L_Or_r :
    forall E p q,
     Proves E q ->
     Proves E (ψor p q)
| L_And :
    forall E p q,
     Proves E p ->
     Proves E q ->
     Proves E (ψand p q)
| L_Atom_ff :
    forall E,
    In ψff E ->
    Proves E ψff
| L_ImpE_ff : 
    forall E p,
      Proves E p ->
      Proves E (ψimp p ψff) ->
      Proves E ψff
| L_AndE_ff_l :
    forall E Ep p q,
      Extends E p Ep ->
      Proves Ep ψff ->
      In (ψand p q) E ->
      Proves E ψff
| L_AndE_ff_r :
    forall E Eq p q,
      Extends E q Eq ->
      Proves Eq ψff ->
      In (ψand p q) E ->
      Proves E ψff
| L_OrE_ff :
    forall E Ep Eq p q,
      Extends E p Ep ->
      Extends E q Eq ->
      Proves Ep ψff ->
      Proves Eq ψff ->
      In (ψor p q) E ->
      Proves E ψff.

Hint Constructors Proves.


Lemma nil_extends_false : forall X l (x:X),
Extends l x nil -> False.
Proof.
  intros A l a ext.
  inversion ext. crush. 
Qed.
Hint Resolve nil_extends_false.

Lemma contains_nil : forall X (l:list X),
Contains nil l.
Proof.
  intros.
  apply containment.
  crush.
Qed.
Hint Resolve contains_nil.

Lemma nil_contains : forall X (l:list X),
Contains l nil -> l = nil.
Proof.
  intros.
  induction l. reflexivity.
  inversion H. subst.
  remember (H0 a). crush.
Qed.  
Hint Resolve nil_contains.

(* TODO
Theorem contains_proves : forall E1 E2 p,
Contained E1 E2 ->
Proves E1 p ->
Proves E2 p.
Proof.
  induction p.
  intros cont provesE1.
  inversion cont.
  inversion provesE1; subst; crush.
  apply L_AndE.
*)

Theorem Proves_nil_dec : forall p,
{Proves nil p} + {~Proves nil p}.
Proof.
  induction p.
  right. intros contra.
  inversion contra; subst; crush.
  inversion H1. tryfalse.
  
