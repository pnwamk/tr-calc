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
Require Import LTRbase.
Require Import LTRutil.
Require Import LTRrel.
Require Import LTRfacts.
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
                       (If ($ TMP)
                           ($ TMP)
                           q))).
(** And Macro *)
Notation AND := (fun p q =>
                (If p q #f)).
Hint Extern 10 (id) => exact X.
Hint Extern 10 (prop) => exact TT.

Lemma subst_tBool : forall t X Y,
tBool = t
-> subst_t t (Some (var X)) Y = tBool.
Proof.
  intros.
  crush.
Qed.

Lemma subst_tNat : forall t X Y,
tNat = t
-> subst_t t (Some (var X)) Y = tNat.
Proof.
  intros.
  crush.
Qed.


(** *Typechecked Examples *)

Example example1:
    TypeOf [((var X) ::= tTop)]
           (If (Nat? ($ X))
               (Add1 ($ X))
               (#0))
           tNat
           TT
           None.
Proof. Admitted. 



Example example1':
exists p o,
    TypeOf [((var X) ::= tTop)]
           (If (Nat? ($ X))
               (Add1 ($ X))
               (#0))
           (tU tNat tNat)
           p
           o.
Proof.
  exists (subst_p (Atom (istype (var TMP) tNat)) (Some (var X)) TMP &&
   subst_p TT (Some (var X)) TMP || (Atom (istype (var X) tNat) --> FF) && TT). exists None.
  eapply T_If.
  eapply T_App.
  eapply T_Const.
  crush.
  eapply T_Var with (τ:= tTop); solve_it.
  solve_it. apply subst_tBool. crush.
  crush. crush.
  compute. 
  eapply T_App.
  eapply T_Const. crush.
  eapply T_Var with (τ:= tNat); solve_it.
  solve_it.
  apply subst_tNat. crush.
  crush.
  crush.
  simpl.
  eapply T_Nat.
  apply ojoin; crush.
  crush.
Qed.

Example example2:
    TypeOf []
           (λ X (tU tStr tNat)
              (If (Nat? ($ X))
                  (Add1 ($ X))
                  (StrLen ($ X))))
           (tλ X
               (tU tStr tNat) tNat
               TT
               None)
           TT
           None.
Proof. Admitted. 

Example example2':
    TypeOf []
           (λ X (tU tStr tNat)
              (If (Nat? ($ X))
                  (Add1 ($ X))
                  (StrLen ($ X))))
           (tλ X
               (tU tStr tNat) tNat
               TT
               None)
           TT
           None.
Proof. 
  apply T_Abs.
  apply T_If.

Admitted. 


Example example3:
    TypeOf
      [((var Y) ::= tTop)]
      (Let X (Nat? ($ Y))
          (If ($ X)
              ($ Y)
              (# 0)))
      tNat
      TT
      None.
Proof. Admitted. 

Example example4:
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT None))]
           (If (OR (Nat? ($ X)) (Str? ($ X)))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example5:
    TypeOf [((var X) ::= tTop); 
             ((var Y) ::= tTop)]
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example7:
  forall X y,
    TypeOf [((var X) ::= tTop); 
            ((var y) ::= tTop)]
           (If (If (Nat? ($ X)) (Str? ($ y)) #f)
               (Plus ($ X) (StrLen ($ y)))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example8:
    TypeOf []
           (λ X tTop
              (OR (Str? ($ X)) (Nat? ($ X))))
           (tλ X
               tTop (tU tStr tNat)
               ((var X) ::= (tU tStr tNat))
               None)
           TT
           None.
Proof. Admitted. 

Example example9:
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT None))]
           (If (Let TMP (Nat? ($ X))
                    (If ($ TMP) ($ TMP) (Str? ($ X))))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example10:
let p := (Id 23) in
    TypeOf [((var p) ::= (tPair tTop tTop))]
           (If (Nat? (Car ($ p)))
               (Add1 (Car ($ p)))
               (# 7))
           tNat
           TT
           None.
Proof. Admitted. 

Example example11:
let p := (Id 23) in
    TypeOf [(var p) ::= (tPair tTop tTop);
            ((var G) ::= (tλ X (tU tNat tNat) tNat TT None))]
           (If (AND (Nat? (Car ($ p))) (Nat? (Cdr ($ p))))
               (Apply ($ G) ($ p))
               (# 42))
           tNat
           TT
           None.
Proof. Admitted. 

Example example12:
    TypeOf []
           (λ X (tPair tTop tTop)
              (Nat? (Car ($ X))))
           (tλ Y
               (tPair tTop tTop) (tPair tTop tTop)
               ((var Y) ::= (tPair tNat tTop))
               None)
           TT
           None.
Proof. Admitted. 

Example example13:
    TypeOf [((var X) ::= tTop) && ((var Y) ::= (tU tNat tStr))]
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (If (Nat? ($ X))
                   (Plus ($ X) ($ Y))
                   (# 42)))
           tNat
           TT
           None.
Proof. Admitted. 

Example example14:
  forall X y,
    TypeOf [((var X) ::= tTop);
            ((var y) ::= (tPair tTop (tU tNat tStr)))]
           (If (AND (Nat? ($ X)) (Str? (Cdr ($ y))))
               (Plus ($ X) (StrLen ($ y)))
               (If (Nat? ($ X))
                   (Plus ($ X) (Cdr ($ y)))
                   (# 42)))
           tNat
           TT
           None.
Proof. Admitted. 