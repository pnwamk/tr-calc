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

Require Import List.
Require Import CpdtTactics.

Lemma find_witness: forall(T:Type) (P:T->Prop) (L:list T),
(forall x, {P x}+{~P x}) 
-> { x | In x L /\ P x } + { forall x, In x L -> ~P x }.
Proof.
intros.
induction L; crush.
destruct a0. left; exists x; crush.
destruct (X a). left; exists a. crush.
right; crush. apply (b x); auto.
Defined. 

Lemma find_In_witness: forall(T:Type) (P:T->Prop) (L:list T),
(forall x, In x L -> {P x}+{~P x}) 
-> { x | In x L /\ P x } + { forall x, In x L -> ~P x }.
Proof.
intros.
induction L; crush.
destruct IHL.
crush.
destruct s. left; exists x; crush.
destruct (X a); crush.
left; exists a; crush.
right; intros.
destruct H. crush.
apply (f x); crush.
Defined.
