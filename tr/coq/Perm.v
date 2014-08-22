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
Require Import List.
Require Import Permutation.
Require Import Relations.
Require Import Morphisms.
Require Import Setoid.

Import ListNotations.

Lemma app_eq_compat_perm {X:Type} : 
forall l l1 l2:list X, 
Permutation l1 l2 
-> Permutation (l++l1) (l++l2).
Proof. intros. induction l; crush. Qed.

Instance app_compat {X:Type} : 
Proper (@Permutation X ==> @Permutation X ==> @Permutation X) (@app X).
Proof.
  unfold Proper,respectful.
  intros l1 l2 Hl12 l3 l4 Hl34.
  induction Hl12; crush.
  rewrite perm_swap. 
  do 2 apply Permutation_cons.
  apply app_eq_compat_perm; crush.
  apply Permutation_app; crush.
Qed.


Lemma app_order_1: forall (X:Type) 
                          (l1 l2 l3:list X),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. intros. crush. Qed.

Lemma app_order_2: forall (X:Type) 
                          (x1:X) 
                          (l2 l3:list X),
    (x1 :: l2) ++ l3 = x1 :: (l2 ++ l3).
Proof. crush. Qed.

Lemma app_order_3: forall (X:Type) 
                          (l1:list X), 
([]++l1) = l1.
Proof. crush. Qed.

Ltac app_order := repeat (
  rewrite app_order_1 || 
  rewrite app_order_2 ||
  rewrite app_order_3).

Lemma perm_1: forall (X:Type) 
                            (target l1 l2:list X),
Permutation (l1 ++ (target ++ l2)) (target ++ (l1 ++ l2)).
Proof.
  intros A target l1 l2.
  rewrite (app_assoc l1 target l2).
  rewrite (Permutation_app_comm l1 target).
  crush.  
Qed.

Lemma perm_2: forall (X:Type) 
                            (x1:X)
                            (target l1 l2:list X),
Permutation (x1 :: (target ++ l2)) (target ++ (x1 :: l2)).
Proof. intros. apply (perm_1 _ _ [x1]). Qed.

Lemma perm_3: forall (X:Type) 
                            (target l1 l2:list X),
Permutation (l1 ++ target) (target ++ l1).
Proof. intros. apply Permutation_app_comm. Qed.

Lemma perm_4: forall (X:Type) 
                            (target:list X) 
                            (x1:X),
Permutation (x1 :: target) (target ++ [x1]).
Proof. intros. apply (perm_3 _ _ [x1]); crush. Qed.

Lemma perm_5: forall (X:Type) 
                            (target:X)
                            (l1 l2:list X),
Permutation (l1 ++ (target :: l2)) (target :: (l1 ++ l2)).
Proof. intros. apply (perm_1 _ [target]). Qed.

Lemma perm_6: forall (X:Type) 
                            (target x1:X)
                            (l1:list X),
Permutation (x1 :: (target :: l1)) (target :: (x1 :: l1)).
Proof. intros. apply (perm_2 _ _ [target]); crush. Qed.

Lemma perm_7: forall (X:Type) 
                            (target:X) 
                            (l1 l2:list X),
Permutation (l1 ++ [target]) (target :: l1).
Proof. intros. apply (perm_3 _ [target]); crush. Qed.

Lemma perm_8: forall (X:Type) 
                            (x1 target:X) 
                            (l1 l2:list X),
    Permutation (x1 :: [target]) (target :: [x1]).
Proof. intros. apply (perm_4 _ [target]). Qed.

Ltac perm_reduce := app_order; repeat (
  rewrite app_nil_r ||
  match goal with
  | [ |- Permutation ?L1 ?L1 ] => reflexivity
  | [ |- Permutation (?L1++_) (?L1++_) ] => apply Permutation_app_head
  | [ |- Permutation (?L1::_) (?L1::_) ] => apply perm_skip
  | [ |- Permutation _ (?L1++_) ] => 
    (rewrite (perm_1 _ L1) at 1 ||
     rewrite (perm_2 _ L1) at 1 ||
     rewrite (perm_3 _ L1) at 1 ||
     rewrite (perm_4 _ L1) at 1)
  | [ |- Permutation _ (?L1::_) ] => 
    (rewrite (perm_5 _ L1) at 1 ||
     rewrite (perm_6 _ L1) at 1 ||
     rewrite (perm_7 _ L1) at 1 ||
     rewrite (perm_8 _ L1) at 1)
  | [ |- Permutation _ _ ] => fail
  end).

Ltac pauto :=
  match goal with
  | [ |- Permutation _ _ ] => perm_reduce; fail
  | [ |- _ ] => fail
  end.
