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

Hint Resolve P_Axiom P_Top P_Trivial P_ExFalso T_Var
     T_Const T_Nat T_Str T_True T_False.
Hint Constructors CompoundType.
Hint Constructors CompoundProp.
Hint Constructors TypeOf.

Hint Extern 3 (SubType ?t ?t) => apply ST_Refl.
Hint Extern 3 (SubType ?t tTop) => apply ST_Top.
Hint Extern 3 (SubObj None ?o) => apply SO_Top.
Hint Extern 3 (SubObj ?o None) => apply SO_Top.

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
    | [ |- TypeOf _ (# ?n) _ _ _ _] => eapply T_Subsume; apply T_Nat
    | [ |- TypeOf _ (#t) _ _ _ _] => eapply T_Subsume; apply T_True
    | [ |- TypeOf _ (#f) _ _ _ _] => eapply T_Subsume; apply T_False
    | [ |- TypeOf _ (Str _) _ _ _ _] => eapply T_Subsume; apply T_Str
    | [ |- TypeOf _ ($ _) _ _ _ _] => eapply T_Subsume; apply T_Var
    | [ |- TypeOf _ (t$ _ _) _ _ _ _] => eapply T_Subsume; apply T_TVar
    | [ |- TypeOf _ (λ _ _ _) _ _ _ _] => eapply T_Subsume; apply T_Abs
    | [ |- TypeOf _ (eOp (c_op _)) _ _ _ _] => eapply T_Subsume; apply T_Const
    | [ |- TypeOf _ (Car _) _ _ _ _] => eapply T_Subsume; apply T_Car
    | [ |- TypeOf _ (Cdr _) _ _ _ _] => eapply T_Subsume; apply T_Cdr
    | [ |- TypeOf _ (If _ _ _) _ _ _ _] => eapply T_Subsume; apply T_If
    | [ |- TypeOf _ (Apply _ _) _ _ _ _] => eapply T_Subsume; apply T_App
    | [ |- TypeOf _ (Cons _ _) _ _ _ _] => eapply T_Subsume; apply T_Cons
    | [ |- TypeOf _ (Let _ _ _) _ _ _ _] => eapply T_Subsume; apply T_Let
    | [ |- _ = _] => crush
  end.

Ltac typecheck := repeat type_of.

(** *Typechecked Examples *)

Example example1:
    TypeOf [((var X) ::= tTop)]
           (If (Nat? (t$ X tTop))
               (Add1 (t$ X tNat))
               (#0))
           tNat
           TT
           FF
           None.
Proof with crush.
Admitted.

Example example2:
exists pt pf o,
    TypeOf []
           (λ X (tU tStr tNat)
              (If (Nat? (t$ X (tU tStr tNat)))
                  (Add1 (t$ X tNat))
                  (StrLen (t$ X tStr))))
           (tλ X
               (tU tStr tNat) tNat
               pt pf
               o)
           TT FF
           None.
Proof with crush.
Admitted.

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
Admitted.


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
Admitted.


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
Admitted.

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
Admitted.
  

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
Admitted.


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
Admitted.


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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.


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
Admitted.

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
Admitted.
