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
    forall Γ n ψ,
      Proves (TT::Γ) ψ
      -> TypeOf Γ (#n) tNat ψ None
| T_Str :
    forall Γ s ψ,
      Proves (TT::Γ) ψ
      -> TypeOf Γ (Str s) tStr ψ None
| T_Const :
    forall Γ c τ ψ x,
      Proves (TT::Γ) ψ
      -> τ = (const_type c x)
      -> TypeOf Γ (eOp (c_op c)) τ ψ None
| T_True :
    forall Γ ψ,
      Proves (TT::Γ) ψ
      -> TypeOf Γ #t tT ψ None
| T_False :
    forall Γ ψ,
      Proves (FF::Γ) ψ
      -> TypeOf Γ #f tF ψ None
| T_Var :
    forall Γ x τ ψ o,
      Proves Γ ((var x) ::= τ)
      -> Proves (((var x) ::~ tF) :: Γ) ψ
      -> SubObj (Some (var x)) o
      -> TypeOf Γ ($ x) τ ψ o
| T_Abs :
    forall Γ x σ e τ ψ o ψ',
      TypeOf (((var x) ::= σ)::Γ) e τ ψ o
      -> Proves (TT::Γ) ψ'
      -> TypeOf Γ 
                (eλ x σ e) 
                (tλ x σ τ ψ o) 
                ψ' 
                None
| T_App :
    forall Γ e e' τ'' ψf'' o'' τ o' x σ fψ fo o ψ ψ',
      Subtype (subst_t τ o' x) τ''
      -> Proves [(subst_p fψ o' x)] ψf''
      -> SubObj (subst_o fo o' x) o''
      -> TypeOf Γ e (tλ x σ τ fψ fo) ψ o
      -> TypeOf Γ e' σ ψ' o'
      -> TypeOf Γ (Apply e e') τ'' ψf'' o''
| T_If :
    forall Γ e1 e2 e3 τ ψ o τ' ψ1 o1 ψ2 ψ3,
      TypeOf Γ e1 τ' ψ1 o1
      -> TypeOf (ψ1::Γ) e2 τ ψ2 o
      -> TypeOf ((Not ψ1)::Γ) e3 τ ψ3 o
      -> Proves (((ψ1 && ψ2) || ((Not ψ1) && ψ3))::Γ) ψ
      -> TypeOf Γ (If e1 e2 e3) τ ψ o
| T_Cons :
    forall Γ e1 e2 τ1 τ2 ψ ψ1 o1 ψ2 o2,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf Γ e2 τ2 ψ2 o2
      -> Proves (TT::Γ) ψ
      -> TypeOf Γ (Cons e1 e2) (tPair τ1 τ2) ψ None
| T_Car :
    forall Γ e τ1 ψ o' x o τ2 ψ0,
      Proves [(subst_p ((obj [car] x) ::~ tF) o x)] ψ
      -> SubObj (subst_o (Some (obj [car] x)) o x) o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
      -> TypeOf Γ (Car e) τ1 ψ o'
| T_Cdr :
    forall Γ e τ2 ψ o' x o τ1 ψ0,
      Proves [(subst_p ((obj [cdr] x) ::~ tF) o x)] ψ
      -> SubObj (subst_o (Some (obj [cdr] x)) o x) o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
      -> TypeOf Γ (Car e) τ2 ψ o'
| T_Let :
    forall Γ x e0 e1 σ' ψ1' o1' σ o0 o1 τ ψ0 ψ1,
      Subtype (subst_t σ o0 x) σ'
      -> Proves [(subst_p ψ1 o0 x)] ψ1'
      -> SubObj (subst_o o1 o0 x) o1'
      -> TypeOf Γ e0 τ ψ0 o0
      -> TypeOf (((var x) ::= τ)
                   ::(((var x) ::~ tF) --> ψ0)
                   ::(((var x) ::= tF) --> (Not ψ0))
                   ::Γ) 
                e1
                σ
                ψ1
                o1
      -> TypeOf Γ (Let x e0 e1) σ' ψ1' o1'.