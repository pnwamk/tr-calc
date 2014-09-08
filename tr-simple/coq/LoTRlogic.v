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
Open Scope list_scope.

Inductive TypeConflict : relation type :=
| TC_Val :
    forall b1 b2,
      b1 <> b2
      -> TypeConflict (Base b1) (Base b2)
| TC_Valλ :
    forall b1 x t1 t2 pt pf oo,
      TypeConflict (Base b1) (Abs x t1 t2 pt pf oo)
| TC_λVal :
    forall b1 x t1 t2 pt pf oo,
      TypeConflict (Abs x t1 t2 pt pf oo) (Base b1).
Hint Constructors TypeConflict.

(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** ** Proves Relation*)
Inductive Proves : list prop -> prop -> Prop :=
(* Traditional Logic Rules *)
| P_Axiom : 
    forall P L,
      In P L
      -> Proves L P
| P_ExFalso :
    forall L P,
      In FF L
      -> Proves L P
| P_Trivial :
    forall L,
      Proves L TT
| P_Simpl : 
    forall L P1 P2 P3,
      In (P1 && P2) L
      -> Proves (P1::P2::(rem_p (P1 && P2) L)) P3
      -> Proves L P3
| P_Conj :
    forall L P1 P2,
      Proves L P1
      -> Proves L P2
      -> Proves L (P1 && P2)
| P_DisjElim :
    forall L P1 P2 P3,
      In (P1 || P2) L
      -> Proves (P1::(rem_p (P1 || P2) L)) P3
      -> Proves (P2::(rem_p (P1 || P2) L)) P3
      -> Proves L P3
| P_AddL : 
    forall L P1 P2,
      Proves L P1
      -> Proves L (P1 || P2)
| P_AddR : 
    forall L P1 P2,
      Proves L P2
      -> Proves L (P1 || P2)
(* Type-specific Logic Rules *)
| P_Bot :
    forall P o L,
      In (o -: Bot) L
      -> Proves L P
| P_Conflict :
    forall L o t1 t2,
      TypeConflict t1 t2
      -> In (o -: t1) L
      -> Proves L (o -! t2)
| P_Contradiction :
    forall L o t1 t2 P,
      In (o -: t1) L
      -> In (o -! t2) L
      -> Proves [(o -: t1)] (o -: t2)
      -> Proves L P
| P_TypeConflict :
    forall L o t1 t2 P, 
      TypeConflict t1 t2
      -> In (o -: t1) L
      -> In (o -: t2) L
      -> Proves L P
| P_SubNot :
    forall L o t1 t2,
      In (o -! t1) L
      -> Proves [(o -: t2)] (o -: t1)
      -> Proves L (o -! t2)
(* Subtyping Logic Rules *)
| ST_Top :
    forall L o t,
      In (o -: t) L
      -> Proves L (o -: Top)
| ST_UnionSuperL :
    forall L o t1 t2,
      Proves L (o -: t1)
      -> Proves L (o -: (U t1 t2))
| ST_UnionSuperR :
    forall L o t1 t2,
      Proves L (o -: t2)
      -> Proves L (o -: (U t1 t2))
| ST_UnionSub :
    forall P L o t1 t2,
      In (o -: (U t1 t2)) L
      -> Proves ((o -: t1)::(rem_p (o -: (U t1 t2)) L)) P
      -> Proves ((o -: t2)::(rem_p (o -: (U t1 t2)) L)) P
      -> Proves L P
| ST_Fun :
    forall L o x1 t1a t1r p1t p1f o1 x2 t2a t2r p2t p2f o2,
      In (o -: (Abs x1 t1a t1r p1t p1f o1)) L
      -> Proves [(o -: (subst_t (Some (var x2)) x1 t1r))] (o -: t2r)
      -> Proves [(o -: t2a)] (o -: (subst_t (Some (var x2)) x1 t1a))
      -> Proves [(subst_p (Some (var x2)) x1 p1t)] p2t
      -> Proves [(subst_p (Some (var x2)) x1 p1f)] p2f
      -> SubObj (subst_o (Some (var x2)) x1 o1) o2
      -> Proves L (o -: (Abs  x2 t2a t2r p2t p2f o2)).

(** ** SubType Relation*)
Definition SubType (t1 t2:type) :=
let o := (var (Id 0)) in
Proves [(o -: t1)] (o -: t2).

Lemma ST_Refl : forall t1,
SubType t1 t1.
Proof.
  intros t1.
  unfold SubType in *.
  apply P_Axiom. crush.
Qed.

Fixpoint env_size (l:list prop) : nat :=
  match l with
    | nil => 0
    | p :: ps => (prop_size p) + (env_size ps)
  end.
