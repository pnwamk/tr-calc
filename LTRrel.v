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

Inductive Proves : list formula -> formula -> Prop :=
| P_Axiom :
    forall L P,
      In P L
    -> Proves L P
| P_Contradiction :
    forall L P t1 t2 o,
      In (o ::= t1) L
      -> In (o ::= t2) L
      -> (~CommonSubtype (t1, t2))
      -> Proves L P
| P_UnionElim :
    forall L P t1 t2 o ,
      In (o ::= (tU t1 t2)) L
      -> Proves ((o ::= t1)::(rem (o ::= (tU t1 t2)) L)) P
      -> Proves ((o ::= t2)::(rem (o ::= (tU t1 t2)) L)) P
      -> Proves L P
| P_PairElim :
    forall L P t1 t2 π x,
      In ((obj π x) ::= (tPair t1 t2)) L
      -> Proves (((obj π x) ::= tCons)
                    ::((obj (π ++ [car]) x) ::= t1)
                    ::((obj (π ++ [cdr]) x) ::= t2)
                    ::(rem ((obj π x) ::= (tPair t1 t2)) L)) 
                   P
      -> Proves L P
| P_Top :
  forall L t o,
    In (o ::= t) L
    -> Proves L (o ::= tTop)
| P_Union_lhs :
    forall L t1 t2 o,
      Proves L (o ::= t1)
      -> Proves L (o ::= (tU t1 t2))
| P_Union_rhs :
    forall L t1 t2 o,
      Proves L (o ::= t2)
      -> Proves L (o ::= (tU t1 t2))
| P_Pair :
    forall L t1 t2 π x,
      Proves L ((obj (π ++ [car]) x) ::= t1)
      -> Proves L ((obj (π ++ [cdr]) x) ::= t2)
      -> Proves L ((obj π x) ::= tCons)
      -> Proves L ((obj π x) ::= (tPair t1 t2))
| P_Fun :
    forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 ox,
      In (ox ::= (tλ x1 t1a t1r p1 o1)) L
      -> Proves [(ox ::= (subst_t t1r (Some (var x2)) x1))] (ox ::= t2r)
      -> Proves [(ox ::= t2a)] (ox ::= (subst_t t1a (Some (var x2)) x1))
      -> Proves [] (formulate ((subst_p p1 (Some (var x2)) x1) ---> p2))
      -> SubObj (subst_o o1 (Some (var x2)) x1) o2
      -> Proves L (ox ::= (tλ x2 t2a t2r p2 o2))
| P_Bot :
    forall L P o,
      In (o ::= tBot) L
      -> Proves L P
| P_True :
    forall L,
      Proves L TT
| P_False :
    forall L P,
      In FF L
      -> Proves L P
| P_Simpl :
    forall L R P Q,
      In (P && Q) L
      -> Proves (P::Q::(rem (P && Q) L)) R
      -> Proves L R
| P_DisjElim :
    forall L R P Q,
      In (P || Q) L
      -> Proves (P::(rem (P || Q) L)) R
      -> Proves (Q::(rem (P || Q) L)) R
      -> Proves L R
| P_MP :
     forall L R P Q,
       In (P --> Q) L
       -> Proves (rem (P --> Q) L) P
       -> Proves (P::Q::(rem (P --> Q) L)) R
       -> Proves L R
| P_Conj :
    forall L P Q,
      Proves L P
      -> Proves L Q
      -> Proves L (P && Q)
| P_Add_lhs :
    forall L P Q,
      Proves L P
      -> Proves L (P || Q)
| P_Add_rhs :
    forall L P Q,
      Proves L Q
      -> Proves L (P || Q)
 | P_CP :
     forall L P Q,
       Proves (P::L) Q
       -> Proves L (P --> Q).

Definition Subtype (t1 t2:type) := 
  Proves [((var (Id 0)) ::= t1)] ((var (Id 0)) ::= t2).

Definition Implies (p1 p2:prop) : Prop :=
Proves [] (formulate (p1 ---> p2)).