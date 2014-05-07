

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

Definition finv (f:fact) : fact :=
mkfact (negb (fbool f))
       (fvar f)
       (fprop f).

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

Inductive Contained {X:Type} : list X -> list X -> Prop :=
| containment : forall l1 l2, 
                  (forall x, In x l1 -> In x l2) ->
                  Contained l1 l2.

Inductive Extended {X:Type} : list X -> X -> list X -> Prop :=
| extension : forall l1 x l2,
                  Contained l1 l2 ->
                  (forall y, ((x <> y) /\ In y l2) -> In y l1) ->
                  In x l2 ->
                  Extended l1 x l2.
                

Inductive ψ : Type :=
| ψfact : fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ.
(* Bookmark - Changing ψ-names. I just added an actual
   way to prove false. Lets see if that and perhaps another
   simple addition help create a decidable logic provable as
   an Inductive Prop. *)
Theorem ψ_eqdec : forall p1 p2 : ψ,
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality.
Defined.
Hint Resolve ψ_eqdec.

Inductive Proves : list ψ -> ψ -> Prop :=
| L_Atom : 
    forall E f,
      In (ψfact f) E -> Proves E (ψfact f)
| L_True :
    forall E, 
      Proves E ψtt
| L_False :
    forall E p,
      Proves E ψff ->
      Proves E p
| L_AndI :
    forall E p q,
      Proves E p ->
      Proves E q ->
      Proves E (ψand p q)
| L_AndE_l :
    forall E E' p q r,
      In p E ->
      Proves E r ->
      Extended E (ψand p q) E' ->
      Proves E' r
| L_AndE_r :
    forall E E' p q r,
      In r E ->
      Proves E r ->
      Extended E (ψand p q) E' ->
      Proves E' r
| L_ImpI :
    forall E E' p q,
      Contained E E' ->
      In p E' ->
      Proves E' q ->
      Proves E (ψimpl p q)
| L_ImpE :
    forall E p q,
      Proves E p ->
      In (ψimpl p q) E ->
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
    forall E Ep Eq E' p q r,
      Extended E p Ep ->
      Extended E q Eq ->
      Extended E ((ψor p q)) E' ->
      Proves E' r
| L_Cons : (* TODO this should be provable *)
    forall E p q,
     Proves E p ->
     Proves (q :: E) p.
Hint Constructors Proves.

(*
Lemma Proves_extended : forall E p1 p2,
Proves E p1 ->
Proves (p2 :: E) p1.
Proof.
  intros E p1 p2 IHp1. generalize dependent p2.
  induction IHp1; intros p2.
  apply L_Atom. right. auto.
  apply L_True.
  apply L_False. right. auto.
  apply L_AndI; auto.
  apply
*)

Lemma extended_nil_false : forall X l (x:X),
Extended l x nil -> False.
Proof.
  intros A l a ext.
  inversion ext. crush. 
Qed.
Hint Resolve extended_nil_false.


Lemma contains_nil : forall X (l:list X),
Contained nil l.
Proof.
  intros.
  apply containment.
  crush.
Qed.
Hint Resolve contains_nil.

Lemma nil_contains : forall X (l:list X),
Contained l nil -> l = nil.
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
  forwards*: extended_nil_false.
  forwards*: extended_nil_false.
  forwards*: extended_nil_false.
  destruct IHp1; destruct IHp2.
  left.
  apply (L_ImpI p1 (contains_nil ( p1 :: nil))). crush.
  apply L_Cons. auto.
  destruct (ψ_eqdec p1 ψff). subst.
  left. inversion p; subst. tryfalse. apply L_False. auto
  destruct p1. inversion H; subst.
  
  destruct (ψ_eqdec p1 p2); crush.
  right; intros contra.
  inversion contra; subst; crush.
  forwards*: extended_nil_false.
  forwards*: extended_nil_false.

  eauto.
  left; auto.
  

  assert (Contained nil (p :: nil)) as cont ; crush.
    apply containment. intros
  Check L_ImpI. eapply (L_ImpI nil (p :: nil) p1 p2).