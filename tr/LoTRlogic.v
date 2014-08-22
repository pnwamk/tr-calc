(*
The MIT License (MIT)

Copyright (c) 2014 Andrew M. Kent

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*)

Require Import LoTRbase.
Require Import Perm.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Permutation.
Require Import Morphisms.
Require Import Setoid.

Import ListNotations.

Inductive TypeConflict : relation type :=
| TC_Val :
    forall v1 v2,
      v1 <> v2
      -> TypeConflict (tVal v1) (tVal v2)
| TC_Valλ :
    forall v1 x t1 t2 pt pf oo,
      TypeConflict (tVal v1) (tλ x t1 t2 pt pf oo)
| TC_λVal :
    forall v1 x t1 t2 pt pf oo,
      TypeConflict (tλ x t1 t2 pt pf oo) (tVal v1).
Hint Constructors TypeConflict.

(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** ** Proves Relation*)
Inductive Proves : list prop -> prop -> Prop :=
| P_Perm : 
    forall P L1 L2,
      Permutation L1 L2
      -> Proves L1 P
      -> Proves L2 P
| P_Weak :
    forall P1 P2 L,
      Proves L P2
      -> Proves (P1::L) P2
| P_Axiom : 
    forall P L,
      Proves (P::L) P
| P_Top :
    forall L o t,
      Proves ((o ::= t)::L) (o ::= tTop)
| P_Bot :
    forall P o L,
      Proves ((o ::= tBot)::L) P
| P_Not :
    forall L o t1 t2,
      TypeConflict t1 t2
      -> Proves ((o ::= t1)::L) (o ::~ t2)
| P_Contradiction :
    forall L o t1 t2 P,
      Proves [(o ::= t1)] (o ::= t2)
      -> Proves ((o ::= t1)::(o ::~ t2)::L) P
| P_TypeConflict :
    forall L o t1 t2 P, 
      TypeConflict t1 t2
      -> Proves ((o ::= t1)::(o ::= t2)::L) P
| P_ExFalso :
    forall L P,
      Proves (FF::L) P
| P_Trivial :
    forall L,
      Proves L TT
| P_ReduceL :
    forall L P1 P2,
      CompoundProp P1
      -> Proves ((reduce P1)::L) P2
      -> Proves (P1::L) P2
| P_ReduceR :
    forall P L,
      CompoundProp P
      -> Proves L (reduce P)
      -> Proves L P
| P_Fun :
    forall L1 o x1 t1a t1r p1t p1f o1 x2 t2a t2r p2t p2f o2,
      Proves [(o ::= (subst_t (Some (var x2)) x1 t1r))] (o ::= t2r)
      -> Proves [(o ::= t2a)] (o ::= (subst_t (Some (var x2)) x1 t1a))
      -> Proves [(subst_p (Some (var x2)) x1 p1t)] p2t
      -> Proves [(subst_p (Some (var x2)) x1 p1f)] p2f
      -> SubObj (subst_o (Some (var x2)) x1 o1) o2
      -> Proves ((o ::= (tλ x1 t1a t1r p1t p1f o1))::L1) 
                (o ::= (tλ x2 t2a t2r p2t p2f o2))
| P_FunNot :
    forall L1 o x1 t1a t1r p1t p1f o1 x2 t2a t2r p2t p2f o2,
      Proves [(o ::= (tλ x2 t2a t2r p2t p2f o2))] 
             (o ::= (tλ x1 t1a t1r p1t p1f o1))
      -> Proves ((o ::~ (tλ x1 t1a t1r p1t p1f o1))::L1) 
                (o ::~ (tλ x2 t2a t2r p2t p2f o2))
| P_MP : 
    forall L P1 P2 P3,
      Proves ((P1 =-> P2)::L) P1
      -> Proves (P2::L) P3
      -> Proves ((P1 =-> P2)::L) P3
| P_CP : 
    forall L P1 P2,
      Proves (P1::L) P2
      -> Proves L (P1 =-> P2)
| P_Simpl : 
    forall L P1 P2 P3,
      Proves (P1::P2::L) P3
      -> Proves ((P1 && P2)::L) P3
| P_Conj :
    forall L P1 P2,
      Proves L P1
      -> Proves L P2
      -> Proves L (P1 && P2)
| P_DisjElim :
    forall L P1 P2 P3,
      Proves (P1::L) P3
      -> Proves (P2::L) P3
      -> Proves ((P1 || P2)::L) P3
| P_AddL : 
    forall L P1 P2,
      Proves L P1
      -> Proves L (P1 || P2)
| P_AddR : 
    forall L P1 P2,
      Proves L P2
      -> Proves L (P1 || P2)
| P_Cut : 
    forall L P1 P2,
      Proves L P2 
      -> Proves (P2::L) P1
      -> Proves L P1.

Ltac shuffle L :=
  apply (P_Perm _ L); [pauto|].

Instance Proves_compat : Proper (@Permutation _==>eq==>iff) Proves.
Proof.
  unfold Proper,respectful.
  intros L1 L2 HL P1 P2 HP.
  split.
  - intros H.
    rewrite <-HP.
    exact (P_Perm P1 L1 L2 HL H).
  - intros H.
    rewrite ->HP.
    exact (P_Perm P2 L2 L1 (Permutation_sym HL) H).
Qed.

(** ** SubType Relation*)

Definition SubType (t1 t2:type) :=
let o := (var (Id 0)) in
Proves [(o ::= t1)] (o ::= t2).

Lemma ST_Refl : forall t1,
SubType t1 t1.
Proof.
  intros t1.
  unfold SubType in *.
  apply P_Axiom.
Qed.

Lemma ST_Top : forall t1,
SubType t1 tTop.
Proof.
  intros t1.
  unfold SubType in *.
  apply P_Top.
Qed.

Lemma ST_Trans : forall t1 t2 t3,
SubType t1 t2
-> SubType t2 t3 
-> SubType t1 t3.
Proof.
  intros t1 t2 t3 H12 H23.
  unfold SubType in *.
  apply P_Cut with (P2 := ((var (Id 0)) ::= t2)); auto.
  rewrite perm_swap.
  apply P_Weak; auto.
Qed.

Lemma P_MP12 : forall P1 P2 P3 L,
Proves (P2::L) P3
-> Proves ((P1=->P2)::P1::L) P3.
Proof.
  intros P1 P2 P3 L HP.
  apply P_MP.
  rewrite perm_swap; apply P_Axiom.
  rewrite perm_swap; apply P_Weak; auto.
Qed.