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

Require Import CpdtTactics.
Require Import LoTRbase.
Require Import LoTRlogic.
Require Import Perm.
Import ListNotations.

Ltac howboutno :=
try(solve[right; intros contra; inversion contra; crush]).


Lemma SO_dec : forall opto1 opto2,
{SubObj opto1 opto2} + {~SubObj opto1 opto2}.
Proof.
  intros.
  destruct opto2; destruct opto1; 
  try (solve[right; intros contra; inversion contra; crush]).
  destruct (obj_eqdec o o0). subst. left. apply SO_Refl.
  right; intros contra; inversion contra; crush.
  left; apply SO_Top. left; apply SO_Top.
Defined.

Lemma SO_trans : forall o1 o2 o3,
SubObj o1 o2
-> SubObj o2 o3
-> SubObj o1 o3.
Proof.
  intros.
  inversion H; inversion H0; crush.
Qed.

(** ** TypeOf *)
Inductive TypeOf : list prop -> exp -> type -> prop -> prop -> opt object -> Prop :=
| T_Nat :
    forall Γ n,
      TypeOf Γ (#n) tNat TT FF None
| T_Str :
    forall Γ s,
      TypeOf Γ (Str s) tStr TT FF None
| T_Const :
    forall Γ c t,
      t = (const_type c)
      -> TypeOf Γ (eOp (c_op c)) t TT FF  None
| T_True :
    forall Γ,
      TypeOf Γ #t tT TT FF None
| T_False :
    forall Γ,
      TypeOf Γ #f tF FF TT None
| T_Var :
    forall Γ x t,
      Proves Γ ((var x) ::= t)
      -> TypeOf Γ ($ x) t ((var x)::~tF) ((var x)::=tF) (Some (var x))
| T_TVar :
    forall Γ x t,
      Proves Γ ((var x) ::= t)
      -> TypeOf Γ 
                (t$ x t) 
                t 
                (((var x) ::= t) 
                   && ((var x) ::~ tF))
                ((var x) ::= tF)
                (Some (var x))
| T_Abs :
    forall Γ x e targ tret pt pf o,
      TypeOf (((var x) ::= targ)::Γ) e tret pt pf o
      -> TypeOf Γ
                (eλ x targ e)
                (tλ x targ tret pt pf o)
                TT
                FF
                None
| T_App :
    forall Γ e2 e1 x targ tret fpf fpt pt1 pf1 pt2 pf2 fo o1 o2 o pt pf t,
      TypeOf Γ e1 (tλ x targ tret fpt fpf fo) pt1 pf1 o1
      -> TypeOf Γ e2 targ pt2 pf2 o2
      -> t = (subst_t o2 x tret)
      -> pt = (subst_p o2 x fpt)
      -> pf = (subst_p o2 x fpf)
      -> o = (subst_o o2 x fo)
      -> TypeOf Γ (Apply e1 e2) t pt pf o
| T_If :
    forall Γ e1 e2 e3 t1 t2 t3 o t pt1 pf1 pt2 pf2 pt3 pf3 o1 o2 o3,
      TypeOf Γ e1 t1 pt1 pf1 o1
      -> TypeOf (pt1::Γ) e2 t2 pt2 pf2 o2
      -> TypeOf (pf1::Γ) e3 t3 pt3 pf3 o3
      -> TypeOf Γ 
                (If e1 e2 e3) 
                t 
                (pt2 || pt3)
                (pf2 || pf3)
                o
| T_Cons :
    forall Γ e1 e2 t1 t2 pt1 pf1 pt2 pf2 o1 o2,
      TypeOf Γ e1 t1 pt1 pf1 o1
      -> TypeOf Γ e2 t2 pt2 pf2 o2
      -> TypeOf Γ (Cons e1 e2) (tP t1 t2) TT FF None
| T_Car :
    forall Γ e t t2 o1 pt1 pf1 o pt pf,
      let x := (Id 0) in
      TypeOf Γ e (tP t t2) pt1 pf1 o1
      -> pt = (subst_p o1 x ((obj [car] x) ::~ tF))
      -> pf = (subst_p o1 x ((obj [car] x) ::= tF))
      -> o = (subst_o o1 x (Some (obj [car] x)))
      -> TypeOf Γ (Car e) t pt pf o
| T_Cdr :
    forall Γ e t o1 t1 pt1 pf1 pt pf o,
      let x := (Id 0) in
      TypeOf Γ e (tP t1 t) pt1 pf1 o1
      -> pt = (subst_p o1 x ((obj [cdr] x) ::~ tF))
      -> pf = (subst_p o1 x ((obj [cdr] x) ::= tF))
      -> o = (subst_o o1 x (Some (obj [cdr] x)))
      -> TypeOf Γ (Cdr e) t pt pf o
| T_Let :
    forall Γ x e0 e1 t o0 o1 t0 pt0 pf0 pt1 pf1 pt pf t1 o,
      TypeOf Γ e0 t0 pt0 pf0 o0
      -> TypeOf (((var x) ::= t0)
                   ::(((var x) ::~ tF) =-> pt0)
                   ::(((var x) ::= tF) =-> pf0)
                   ::Γ)
                e1
                t1
                pt1 
                pf1
                o1
      -> t = (subst_t o0 x t1)
      -> pt = (subst_p o0 x pt1)
      -> pf = (subst_p o0 x pf1)
      -> o = (subst_o o0 x o1)
      -> TypeOf Γ 
                (Let x e0 e1) 
                t
                pt
                pf
                o
| T_Subsume :
    forall Γ e t pt pf o t' pt' pf' o',
    TypeOf Γ e t pt pf o
    -> SubType t t'
    -> Proves (pt::Γ) pt'
    -> Proves (pf::Γ) pf
    -> SubObj o o'
    -> TypeOf Γ e t' pt' pf' o'.
Hint Constructors TypeOf.