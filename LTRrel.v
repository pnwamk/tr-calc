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

Require Import LTRbase.
Require Import Relations.
Import ListNotations.
(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)


Inductive CommonSubtype : (type * type) -> Prop :=
| CST_Refl :
    forall t, CommonSubtype (t, t)
| CST_Top_rhs :
    forall t, CommonSubtype (t, tTop)
| CST_Top_lhs :
    forall t, CommonSubtype (tTop, t)
| CST_lhsUnion_lhs :
    forall t1 t2 t, 
      CommonSubtype (t1, t)
      -> CommonSubtype ((tU t1 t2), t)
| CST_lhsUnion_rhs :
    forall t1 t2 t, 
      CommonSubtype (t2, t)
      -> CommonSubtype ((tU t1 t2), t)
| CST_rhsUnion_lhs :
    forall t1 t2 t, 
      CommonSubtype (t, t1)
      -> CommonSubtype (t, (tU t1 t2))
| CST_rhsUnion_rhs :
    forall t1 t2 t, 
      CommonSubtype (t, t2)
      -> CommonSubtype (t, (tU t1 t2))
| CST_Abs :
    forall x y t1 t2 t3 t4 p1 p2 o1 o2,
      CommonSubtype ((tλ x t1 t2 p1 o1), (tλ y t3 t4 p2 o2))
| CST_Pair :
    forall t1 t2 t3 t4, 
      CommonSubtype (t1, t3)
      -> CommonSubtype (t2, t4)
      -> CommonSubtype ((tPair t1 t2), (tPair t3 t4))
| CST_Cons_lhs :
    forall t1 t2,
      CommonSubtype (tCons, (tPair t1 t2))
| CST_Cons_rhs :
    forall t1 t2,
      CommonSubtype ((tPair t1 t2), tCons).
Hint Resolve CST_Refl CST_Top_rhs CST_Top_lhs
             CST_Cons_lhs CST_Cons_rhs
             CST_Pair CST_Abs.


(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.


(** ** Proves Relation *)

Inductive Proves : list prop -> prop -> Prop :=
| P_Axiom :
    forall Γ f,
      In (Atom f) Γ
    -> Proves Γ (Atom f)
| P_Contradiction :
    forall Γ P t1 t2 o,
      In (o ::= t1) Γ
      -> In (o ::= t2) Γ
      -> (~CommonSubtype (t1, t2))
      -> Proves Γ P
| P_UnionElim :
    forall Γ P t1 t2 o ,
      In (o ::= (tU t1 t2)) Γ
      -> Proves ((o ::= t1)::(rem (o ::= (tU t1 t2)) Γ)) P
      -> Proves ((o ::= t2)::(rem (o ::= (tU t1 t2)) Γ)) P
      -> Proves Γ P
| P_PairElim :
    forall Γ P t1 t2 π x,
      In ((obj π x) ::= (tPair t1 t2)) Γ
      -> Proves (((obj π x) ::= tCons)
                    ::((obj (π ++ [car]) x) ::= t1)
                    ::((obj (π ++ [cdr]) x) ::= t2)
                    ::(rem ((obj π x) ::= (tPair t1 t2)) Γ)) 
                   P
      -> Proves Γ P
| P_Top :
  forall Γ t o,
    In (o ::= t) Γ
    -> Proves Γ (o ::= tTop)
| P_Union_lhs :
    forall Γ t1 t2 o,
      Proves Γ (o ::= t1)
      -> Proves Γ (o ::= (tU t1 t2))
| P_Union_rhs :
    forall Γ t1 t2 o,
      Proves Γ (o ::= t2)
      -> Proves Γ (o ::= (tU t1 t2))
| P_Pair :
    forall Γ t1 t2 π x,
      Proves Γ ((obj (π ++ [car]) x) ::= t1)
      -> Proves Γ ((obj (π ++ [cdr]) x) ::= t2)
      -> Proves Γ ((obj π x) ::= tCons)
      -> Proves Γ ((obj π x) ::= (tPair t1 t2))
| P_Fun :
    forall Γ x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 ox,
      In (ox ::= (tλ x1 t1a t1r p1 o1)) Γ
      -> Proves [(ox ::= (subst_t t1r (Some (var x2)) x1))] (ox ::= t2r)
      -> Proves [(ox ::= t2a)] (ox ::= (subst_t t1a (Some (var x2)) x1))
      -> Proves [(subst_p p1 (Some (var x2)) x1)] p2
      -> SubObj (subst_o o1 (Some (var x2)) x1) o2
      -> Proves Γ (ox ::= (tλ x2 t2a t2r p2 o2))
| P_Bot :
    forall Γ P o,
      In (o ::= tBot) Γ
      -> Proves Γ P
| P_True :
    forall Γ,
      Proves Γ TT
| P_False :
    forall Γ P,
      In FF Γ
      -> Proves Γ P
| P_Simpl :
    forall Γ R P Q,
      In (P && Q) Γ
      -> Proves (P::Q::(rem (P && Q) Γ)) R
      -> Proves Γ R
| P_DisjElim :
    forall Γ R P Q,
      In (P || Q) Γ
      -> Proves (P::(rem (P || Q) Γ)) R
      -> Proves (Q::(rem (P || Q) Γ)) R
      -> Proves Γ R
| P_MP :
     forall Γ R P Q,
       In (P --> Q) Γ
       -> Proves (rem (P --> Q) Γ) P
       -> Proves (P::Q::(rem (P --> Q) Γ)) R
       -> Proves Γ R
| P_Conj :
    forall Γ P Q,
      Proves Γ P
      -> Proves Γ Q
      -> Proves Γ (P && Q)
| P_Add_lhs :
    forall Γ P Q,
      Proves Γ P
      -> Proves Γ (P || Q)
| P_Add_rhs :
    forall Γ P Q,
      Proves Γ Q
      -> Proves Γ (P || Q)
 | P_CP :
     forall Γ P Q,
       Proves (P::Γ) Q
       -> Proves Γ (P --> Q).

Definition Subtype (t1 t2:type) := 
  Proves [((var (Id 0)) ::= t1)] ((var (Id 0)) ::= t2).