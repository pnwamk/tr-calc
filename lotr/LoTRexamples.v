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
Require Import LoTRtype.
Require Import Perm.
Require Import Permutation.
Import ListNotations.

(** Macros *)
(** Unhygeinic Or macro *)
Notation TMP := (Id 0).
Notation X := (Id 1).
Notation Y := (Id 2).
Notation F := (Id 3).
Notation G := (Id 4).
Notation OR := (fun p q => 
                  (Let TMP p
                       (If (t$ TMP tBool)
                           (t$ TMP tBool)
                           q))).
(** And Macro *)
Notation AND := (fun p q =>
                (If p q #f)).
Hint Extern 10 (id) => exact X.
Hint Extern 10 (prop) => exact TT.

Hint Resolve P_Axiom P_Top P_Trivial P_ExFalso T_Var ST_Refl 
     T_Const T_Nat T_Str T_True T_False.
Hint Constructors CompoundType.
Hint Constructors CompoundProp.
Hint Constructors TypeOf.

Lemma ST_Unionlhs : forall t1 t2,
SubType t1 (tU t1 t2).
Proof.
  intros.
  apply P_ReduceR; crush.
  apply P_AddL; crush.
Qed.

Lemma ST_Unionrhs : forall t1 t2,
SubType t2 (tU t1 t2).
Proof.
  intros.
  apply P_ReduceR; crush.
  apply P_AddR; crush.
Qed.

Lemma P_UnionElimlhs : forall o t1 t2 L,
Proves ((o ::= (tU t1 t2))::(o ::~ t2)::L) (o ::= t1).
Proof.
  intros.
  apply P_ReduceL; crush.
  apply P_DisjElim; crush.
  apply P_Contradiction; crush.
Qed.


Lemma P_UnionElimrhs : forall o t1 t2 L,
Proves ((o ::= (tU t1 t2))::(o ::~ t1)::L) (o ::= t2).
Proof.
  intros.
  apply P_ReduceL; crush.
  apply P_DisjElim; crush.
  apply P_Contradiction; crush. 
Qed.

Lemma P_Unionlhs : forall o t1 t2 L,
Proves ((o ::= t1)::L) (o ::= (tU t1 t2)).
Proof.
  intros.
  apply P_ReduceR; crush.
  apply P_AddL; crush.
Qed.

Lemma P_Unionrhs : forall o t1 t2 L,
Proves ((o ::= t2)::L) (o ::= (tU t1 t2)).
Proof.
  intros.
  apply P_ReduceR; crush.
  apply P_AddR; crush.
Qed.


Ltac P_Direct := 
  first[solve[apply P_Axiom] | 
        solve[apply P_ExFalso] |
        solve[apply P_Top] | 
        solve[apply P_Unionlhs] | 
        solve[apply P_Unionrhs] | 
        solve[apply P_Weak; P_Direct]].

Ltac type_of :=
  match goal with
    | [ |- TypeOf _ (# ?n) _ _ _ _] => eapply T_Nat
    | [ |- TypeOf _ (#t) _ _ _ _] => eapply T_True
    | [ |- TypeOf _ (#f) _ _ _ _] => eapply T_False
    | [ |- TypeOf _ (Str _) _ _ _ _] => eapply T_Str
    | [ |- TypeOf _ ($ _) _ _ _ _] => eapply T_Var
    | [ |- TypeOf _ (t$ _ _) _ _ _ _] => eapply T_TVar
    | [ |- TypeOf _ (λ _ _ _) _ _ _ _] => eapply T_Abs
    | [ |- TypeOf _ (eOp (c_op _)) _ _ _ _] => eapply T_Const
    | [ |- TypeOf _ (Car _) _ _ _ _] => eapply T_Car
    | [ |- TypeOf _ (Cdr _) _ _ _ _] => eapply T_Cdr
    | [ |- TypeOf _ (If _ _ _) _ _ _ _] => eapply T_If
    | [ |- TypeOf _ (Apply _ _) _ _ _ _] => eapply T_App
    | [ |- TypeOf _ (Cons _ _) _ _ _ _] => eapply T_Cons
    | [ |- TypeOf _ (Let _ _ _) _ _ _ _] => eapply T_Let
    | [ |- _ = _] => crush
  end.

Ltac typecheck := repeat type_of.



(** *Typechecked Examples *)

Example example1:
exists pt pf o,
    TypeOf [((var X) ::= tTop)]
           (If (Nat? (t$ X tTop))
               (Add1 (t$ X tNat))
               (#0))
           tNat
           pt
           pf
           o.
Proof with crush.
  repeat eexists.
  typecheck...
Qed.


Example example2:
exists pt pf o,
    TypeOf []
           (λ X (tU tStr tNat)
              (If (Nat? ($ X))
                  (Add1 ($ X))
                  (StrLen ($ X))))
           (tλ X
               (tU tStr tNat) tNat
               pt pf
               o)
           TT FF
           None.
Proof with crush.
  repeat eexists.
  typecheck...
  compute. crush.
  compute.
  rewrite perm_swap. apply P_UnionElimlhs. 
Qed.  

Example example3:
exists pt pf o,
    TypeOf
      [((var Y) ::= tTop)]
      (Let X (Nat? (t$ Y tTop))
          (If (t$ X tBool)
              (t$ Y tNat)
              (# 0)))
      tNat
      pt 
      pf
      o.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute.
  apply P_Simpl.
  shuffle ([var X ::~ tF =-> var Y ::= tNat; var X ::~ tF;
            var X ::= tBool; var X ::= tBool;
            var X ::= tF =-> var Y ::~ tNat;
     var Y ::= tTop]).
  apply P_MP12; crush.
Qed.


Example example4:
exists pt pf o,
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT FF None))]
           (If (OR (Nat? (t$ X tTop)) (Str? (t$ X tTop)))
               (Apply (t$ F (tλ X (tU tStr tNat) tNat TT FF None)) 
                      (t$ X (tU tStr tNat)))
               (# 0))
           tNat
           pt
           pf
           o.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. 
  P_Direct. P_Direct. P_Direct.
  compute.
  repeat apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  apply P_Weak.
  shuffle ([(var TMP ::= tBool && var TMP ::~ tF && var TMP ::= tF
                 || var TMP ::= tF && var X ::~ tStr) 
              && var TMP ::= tBool 
              && (var TMP ::~ tF =-> var X ::= tNat) 
              && (var TMP ::= tF =-> var X ::~ tNat);
             var TMP ::~ tF; var TMP ::= tBool && var TMP ::~ tF;
            var X ::= tTop;
            var F ::= tλ X (tU tStr tNat) tNat TT FF None]).
  repeat apply P_Simpl.
  shuffle ([var TMP ::~ tF =-> var X ::= tNat; var TMP ::~ tF;
            var TMP ::= tBool && var TMP ::~ tF && var TMP ::= tF
                || var TMP ::= tF && var X ::~ tStr; var TMP ::= tBool;
            var TMP ::= tF =-> var X ::~ tNat;
            var TMP ::= tBool && var TMP ::~ tF; 
            var X ::= tTop; var F ::= tλ X (tU tStr tNat) tNat TT FF None]).
  apply P_MP12.
  P_Direct.
  apply P_Simpl. P_Direct.
Qed.


Example example5:
exists pt pf o,
    TypeOf [((var X) ::= tTop); 
             ((var Y) ::= tTop)]
           (If (AND (Nat? (t$ X tTop)) (Str? (t$ Y tTop)))
               (Plus (t$ X tNat) (StrLen (t$ Y tStr)))
               (# 0))
           tNat
           pt
           pf
           o.
Proof with crush.
  repeat eexists.
  typecheck...
  compute. 
  P_Direct.
  compute. P_Direct. 
  compute.
  apply P_DisjElim.
  apply P_Simpl; crush.
  apply P_Simpl; P_Direct. 
  compute.
  apply P_DisjElim; apply P_Simpl; P_Direct.
Qed.

Example example7:
exists pt pf o,
    TypeOf [((var X) ::= tTop); 
            ((var Y) ::= tTop)]
           (If (If (Nat? (t$ X tTop)) (Str? (t$ Y tTop)) #f)
               (Plus (t$ X tNat) (StrLen (t$ Y tStr)))
               (# 0))
           tNat
           pt
           pf
           o.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. 
  shuffle ([var Y ::= tTop; var X ::= tNat; var X ::= tTop]). crush.
  compute. P_Direct. 
  compute.
  apply P_DisjElim; apply P_Simpl; P_Direct. 
  apply P_DisjElim; apply P_Simpl; P_Direct.
Qed.
  

Example example8:
exists pt pf,
    TypeOf []
           (λ X tTop
              (OR (Str? (t$ X tTop)) (Nat? (t$ X tTop))))
           (tλ X
               tTop tBool
               pt
               pf
               None)
               TT
               FF 
               None
/\ Proves [pt] ((var X) ::= (tU tStr tNat))
/\ Proves [pf] ((var X) ::~ (tU tStr tNat)).
Proof with crush. 
  repeat eexists.
  typecheck...
  compute.
  apply P_Simpl; crush.
  shuffle ([var X ::= tTop; 
             var TMP ::= tF; var TMP ::= αsubst_t (Some (var X)) TMP tBool;
             var TMP ::~ tF =-> αsubst_p (Some (var X)) TMP (var TMP ::= tStr);
             var TMP ::= tF =-> αsubst_p (Some (var X)) TMP (var TMP ::~ tStr)]).
  crush.
  compute.
  apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  shuffle ([(var TMP ::= tBool && var TMP ::~ tF && var TMP ::= tF
        || var TMP ::= tF && var X ::~ tNat) 
     && var TMP ::= tBool &&
     (var TMP ::~ tF =-> var X ::= tStr) &&
     (var TMP ::= tF =-> var X ::~ tStr); var TMP ::= tBool; 
   var TMP ::~ tF; var TMP ::= tBool && var TMP ::~ tF]).
  repeat apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  shuffle ([var TMP ::~ tF =-> var X ::= tStr; var TMP ::~ tF;
             var TMP ::= tBool; var TMP ::= tF; var TMP ::= tBool; 
             var TMP ::= tF =-> var X ::~ tStr; var TMP ::= tBool; 
             var TMP ::~ tF; var TMP ::= tBool && var TMP ::~ tF]).
  apply P_MP12.
  P_Direct.
  apply P_Simpl.
  shuffle ([var TMP ::= tBool && var TMP ::~ tF; 
             var TMP ::= tF; var X ::~ tNat; var TMP ::= tBool;
             var TMP ::~ tF =-> var X ::= tStr; var TMP ::= tF =-> var X ::~ tStr;
             var TMP ::= tBool; var TMP ::~ tF]).
  apply P_Simpl. apply P_Weak.
  rewrite perm_swap; apply P_Contradiction; crush. 
  rewrite perm_swap; crush.
  apply P_Simpl. apply P_Weak. apply P_Weak.
  apply P_Simpl. P_Direct. 
  apply P_ReduceR; crush.
  apply P_Conj.
  compute.
  repeat apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  apply P_Weak.
  rewrite perm_swap; apply P_Contradiction; crush. 
  rewrite perm_swap; crush.
  repeat apply P_Simpl.
  do 3 apply P_Weak.
  apply P_MP. apply P_Weak; apply P_Simpl; P_Direct.
  crush.
  apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  apply P_Weak.
  rewrite perm_swap.
  apply P_Contradiction with (o:=(var TMP)) (t1:=tF) (t2:=tF); crush.
  rewrite perm_swap; crush.
  apply P_Simpl.
  do 2 apply P_Weak. apply P_Simpl. compute.
  P_Direct.
Qed.


Example example9:
exists pt pf o,
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT FF None))]
           (If (Let TMP (Nat? (t$ X tTop))
                    (If (t$ TMP tTop) (t$ TMP tTop) (Str? (t$ X tTop))))
               (Apply (t$ F (tλ X (tU tStr tNat) tNat TT FF None)) 
                      (t$ X (tU tStr tNat)))
               (# 0))
           tNat
           pt
           pf
           o.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. apply P_Simpl. crush.
  compute. P_Direct.
  compute. crush.
  compute. P_Direct.
  compute.
  repeat apply P_Simpl.
  apply P_DisjElim.
  repeat apply P_Simpl.
  shuffle ([(var TMP ::= tTop && var TMP ::~ tF && var TMP ::= tF
                 || var TMP ::= tF && var X ::~ tStr) 
              && var TMP ::= tBool
              && (var TMP ::~ tF =-> var X ::= tNat) 
              && (var TMP ::= tF =-> var X ::~ tNat);
             var TMP ::= tTop; var TMP ::~ tF; 
             var TMP ::= tTop && var TMP ::~ tF;
             var X ::= tTop;
     var F ::= tλ X (tU tStr tNat) tNat TT FF None]).
  repeat apply P_Simpl.
  do 2 apply P_Weak.
  shuffle ([var TMP ::~ tF =-> var X ::= tNat; var TMP ::~ tF; 
            var TMP ::= tF =-> var X ::~ tNat;
            var TMP ::= tTop; var TMP ::= tTop && var TMP ::~ tF;
            var X ::= tTop; var F ::= tλ X (tU tStr tNat) tNat TT FF None]).
  apply P_MP12; crush.
  P_Direct.
  apply P_Simpl. P_Direct.
Qed.


Example example10:
exists pt pf,
    TypeOf [((var X) ::= (tP tTop tTop))]
           (If (Nat? (Car (t$ X (tP tTop tTop))))
               (Add1 (Car (t$ X (tP tNat tTop))))
               (# 7))
           tNat
           pt
           pf
           None.
Proof with crush.
  repeat eexists.  
  typecheck...
  compute.
  rewrite perm_swap. apply P_ReduceL; crush.
  apply P_ReduceR; crush.
  repeat apply P_Simpl.
  repeat apply P_Conj; P_Direct. 
Qed.

Example example11:
exists pt pf,
    TypeOf [(var X) ::= (tP tTop tTop);
            ((var G) ::= (tλ X (tP tNat tNat) tNat TT FF None))]
           (If (AND (Nat? (Car (t$ X (tP tTop tTop)))) 
                    (Nat? (Cdr (t$ X (tP tNat tTop)))))
               (Apply (t$ G (tλ X (tP tNat tNat) tNat TT FF None)) 
                      (t$ X (tP tNat tNat)))
               (# 42))
           tNat
           pt
           pf
           None.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute.
  rewrite perm_swap.
  apply P_ReduceR; crush.
  apply P_ReduceL; crush.
  repeat apply P_Simpl.
  repeat apply P_Conj; P_Direct.
  compute. apply P_Unionrhs. 
  compute. P_Direct.
  compute.
  rewrite perm_swap.
  apply P_ReduceL; crush. repeat apply P_Simpl.
  apply P_ReduceR; crush.
  repeat apply P_Conj; compute; crush.
  do 3 apply P_Weak.
  apply P_DisjElim; apply P_Simpl; crush.
  P_Direct.
  do 3 apply P_Weak.
  apply P_DisjElim; apply P_Simpl; P_Direct. 
Qed.    

Example example12a:
exists pt pf,
    TypeOf []
           (λ X (tP tTop tTop)
              (Nat? (Car (t$ X (tP tTop tTop)))))
           (tλ X
               (tP tTop tTop) tBool
               pt
               pf
               None)
           TT 
           FF
           None
/\ Proves [pt] (obj [car] X ::= tNat)
/\ Proves [pf] (obj [car] X ::~ tNat).
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. crush.
  compute. crush.
Qed.

Example example12b:
exists pt pf,
    TypeOf []
           (λ X (tP tTop tTop)
              (Nat? (Cdr (t$ X (tP tTop tTop)))))
           (tλ X
               (tP tTop tTop) tBool
               pt
               pf
               None)
           TT 
           FF
           None
/\ Proves [pt] (obj [cdr] X ::= tNat)
/\ Proves [pf] (obj [cdr] X ::~ tNat).
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. crush.
  compute. crush.
Qed.


Example example13:
exists pt pf o,
    TypeOf [((var X) ::= tTop) && ((var Y) ::= (tU tNat tStr))]
           (If (AND (Nat? (t$ X tTop)) (Str? (t$ Y tTop)))
               (Plus (t$ X tNat) (StrLen (t$ Y tStr)))
               (If (Nat? (t$ X tTop))
                   (Plus (t$ X tNat) (t$ Y tNat))
                   (# 42)))
           tNat
           pt
           pf
           o.
Proof with crush. 
  repeat eexists.
  typecheck...
  apply P_Simpl; crush.
  compute.
  apply P_Weak; apply P_Simpl; crush.
  apply P_Weak; crush.
  compute. P_Direct. 
  compute.
  apply P_DisjElim; apply P_Simpl; P_Direct.
  compute.
  apply P_DisjElim; apply P_Simpl; P_Direct.
  compute.
  apply P_Weak; apply P_Simpl; P_Direct. 
  compute.
  rewrite perm_swap.
  apply P_DisjElim. apply P_Simpl.
  shuffle ([var X ::= tTop && var Y ::= tU tNat tStr;
             var Y ::~ tStr; var X ::= tNat; var X ::= tNat]).
  apply P_Simpl; apply P_Weak.
  apply P_UnionElimlhs.
  apply P_Simpl.
  rewrite perm_swap; apply P_Weak; 
  rewrite perm_swap; apply P_Contradiction; crush.
Qed.

Example example14:
exists pt pf o,
    TypeOf [((var X) ::= tTop);
            ((var Y) ::= (tP tTop (tU tNat tStr)))]
        (*cond *)
           (* (and (number? x) (string? (cdr y)) *)
           (If (AND (Nat? (t$ X tTop)) 
                    (Str? (Cdr (t$ Y (tP tTop (tU tNat tStr))))))
               (Plus (t$ X tNat) (StrLen (Cdr (t$ Y (tP tTop tStr)))))
           (* (number? x) *)
           (If (Nat? (t$ X tTop))
               (Plus (t$ X tNat) (Cdr (t$ Y (tP tTop (tU tNat tStr)))))
           (* else *)
               (# 42)))
           tNat
           pt
           pf
           o.
Proof with crush. 
  repeat eexists.
  typecheck...
  compute. P_Direct. P_Direct. 
  compute. P_Direct. 
  compute.
  apply P_DisjElim; apply P_Simpl; P_Direct.
  compute.
  apply P_ReduceR; crush; repeat apply P_Conj.
  apply P_DisjElim.
  do 2 apply P_Weak.
  apply P_ReduceL; crush. repeat apply P_Simpl; P_Direct. 
  apply P_Simpl; P_Direct.
  apply P_DisjElim.
  do 2 apply P_Weak.
  apply P_ReduceL; crush. repeat apply P_Simpl; P_Direct. 
  apply P_Simpl; P_Direct.
  apply P_DisjElim.
  apply P_Simpl; P_Direct.
  apply P_Simpl; P_Direct.
  compute.
  P_Direct.
  compute.
  P_Direct.
  crush.