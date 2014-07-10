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



(** ** TypeOf *)

Inductive TypeOf : list prop -> exp -> type -> prop -> opt object -> Prop :=
| T_Nat :
    forall Γ n,
      TypeOf Γ (#n) tNat TT None
| T_Str :
    forall Γ s,
      TypeOf Γ (Str s) tStr TT None
| T_Const :
    forall τ Γ c x,
      τ = (const_type c x)
      -> TypeOf Γ (eOp (c_op c)) τ TT None
| T_True :
    forall Γ,
      TypeOf Γ #t tT TT None
| T_False :
    forall Γ,
      TypeOf Γ #f tF FF None
| T_Var :
    forall τ Γ x,
      Proves Γ ((var x) ::= τ)
      -> TypeOf Γ ($ x) τ ((var x) ::~ tF) (Some (var x))
| T_Abs :
    forall σ τ o Γ x ψ e,
      TypeOf (((var x) ::= σ)::Γ) e τ ψ o
      -> TypeOf Γ 
                (eλ x σ e) 
                (tλ x σ τ ψ o) 
                TT 
                None
| T_App :
    forall τ'' σ τ o'' o o' Γ e x fψ fo ψ e' ψ' ψf'',
      (subst_t τ o' x) = τ''
      -> (subst_p fψ o' x) = ψf''
      -> (subst_o fo o' x) = o''
      -> TypeOf Γ e (tλ x σ τ fψ fo) ψ o
      -> TypeOf Γ e' σ ψ' o'
      -> TypeOf Γ (Apply e e') τ'' ψf'' o''
| T_If :
    forall τ τ' o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ' ψ1 o1
      -> TypeOf (ψ1::Γ) e2 τ ψ2 o
      -> TypeOf ((Not ψ1)::Γ) e3 τ ψ3 o
      -> TypeOf Γ (If e1 e2 e3) τ ((ψ1 && ψ2) || ((Not ψ1) && ψ3)) o
| T_Cons :
    forall τ1 τ2 o1 o2 Γ e1 ψ1 e2 ψ2,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf Γ e2 τ2 ψ2 o2
      -> TypeOf Γ (Cons e1 e2) (tPair τ1 τ2) TT None
| T_Car :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [car] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [car] x)) o x) = o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
      -> TypeOf Γ (Car e) τ1 ψ o'
| T_Cdr :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [cdr] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [cdr] x)) o x) = o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
      -> TypeOf Γ (Cdr e) τ2 ψ o'
| T_Let :
    forall σ' τ σ o1' o0 o1 Γ e0 ψ0 e1 ψ1 x ψ1',
      (subst_t σ o0 x) = σ'
      -> (subst_p ψ1 o0 x) = ψ1'
      -> (subst_o o1 o0 x) = o1'
      -> TypeOf Γ e0 τ ψ0 o0
      -> TypeOf (((var x) ::= τ)
                   ::(((var x) ::~ tF) --> ψ0)
                   ::(((var x) ::= tF) --> (Not ψ0))
                   ::Γ) 
                e1
                σ
                ψ1
                o1
      -> TypeOf Γ (Let x e0 e1) σ' ψ1' o1'
| T_Subsume :
    forall τ' τ o' o Γ e ψ ψ',
      TypeOf Γ e τ ψ o
      -> Proves (ψ::Γ) ψ'
      -> Subtype τ τ'
      -> SubObj o o'
      -> TypeOf Γ e τ' ψ' o'.
