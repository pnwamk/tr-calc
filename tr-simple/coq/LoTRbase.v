(* begin hide *)
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

Require Export CpdtTactics.
Require Export List.
Require Export Arith.
Require Import ZArith.
Require Export Relations.
Require Export Bool.
Require Export Coq.Program.Wf.
Require Export String.

Import ListNotations.
Open Scope list_scope.
(* end hide *)


(** * Basic Definitions for λTR *)

(** Identifiers and objects: *)

Notation opt := option.
Definition boolean {P Q:Prop} (sb: sumbool P Q) : bool :=
if sb then true else false.
Notation No := (right _).
Notation Yes := (left _).

Inductive id : Set :=
  Id : nat -> id.

Inductive object : Set :=
| obj : id -> object.
Hint Constructors object.

Notation var := obj.

(** Types and propositions: *)
Inductive type : Set :=
| Top  : type
| Bot  : type
| Base : nat -> type
| U    : type -> type -> type
| Abs    : id -> type -> type -> prop -> prop -> opt object -> type

with prop : Set :=
| Is : object -> type -> prop
| Isnt : object -> type -> prop
| And  : prop -> prop -> prop
| Or   : prop -> prop -> prop
| TT   : prop
| FF   : prop.

Notation Nat   := (Base 0).
Notation T  := (Base 1).
Notation F := (Base 2).
Notation Bool := (U T F).
Infix "-:" :=  Is (at level 20, right associativity).
Infix "-!" :=  Isnt (at level 20, right associativity).
Notation "P '&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Or P Q) (at level 50, left associativity).

Fixpoint type_size (t:type) : nat :=
  match t with
    | U t1 t2 => 2 + (type_size t1) + (type_size t2)
    | Abs x t1 t2 p1 p2 o => 1 + (type_size t1) 
                             + (type_size t2)
                             + (prop_size p1)
                             + (prop_size p2)
    | _ => 1
  end

with prop_size (p:prop) : nat :=
  match p with
    | Is o t => (type_size t)
    | Isnt o t => 1 + (type_size t)
    | And p q => 1 + (prop_size p) + (prop_size q)
    | Or p q => 1 + (prop_size p) + (prop_size q)
    | TT => 1
    | FF => 1
  end.

 Fixpoint not (p:prop) : prop :=
  match p with
    | o -: t => Isnt o t
    | o -! t => Is o t
    | p && q => (not p) || (not q)
    | p || q => (not p) && (not q)
    | TT => FF
    | FF => TT
  end.

Infix "=->" := (fun (P Q : prop) => ((~P) || Q)) (at level 51).

(** Expressions and primitive operations: *)
Inductive const_op :=
| opIsZero : const_op 
| opAdd1 : const_op
| opIsNat : const_op
| opIsBool : const_op
| opIsProc : const_op
| opPlus : const_op.
Hint Constructors const_op.

Inductive op : Type :=
| c_op : const_op -> op.
Hint Constructors op.

Inductive exp : Set :=
| eNat   : nat -> exp
| eTrue  : exp
| eFalse : exp
| eVar   : id -> exp
| eOp    : op -> exp
| eIf    : exp -> exp -> exp -> exp
| eλ     : id -> type -> exp -> exp
| eApp   : exp -> exp -> exp
| eLet   : id -> exp -> exp -> exp.

Hint Constructors exp.

Notation "$" := eVar.
Notation "#t" := eTrue.
Notation "#f" := eFalse.
Notation "#" := eNat.
Notation λ := eλ.
Notation If := eIf.
Notation Let := eLet.
Notation Apply := eApp.
Notation Add1 := (eApp (eOp (c_op opAdd1))).
Notation "Zero?" := (eApp (eOp (c_op opIsZero))).
Notation "Num?" := (eApp (eOp (c_op opIsNat))).
Notation "Bool?" := (eApp (eOp (c_op opIsBool))).
Notation "Proc?" := (eApp (eOp (c_op opIsProc))).
Notation Plus := (fun x y =>
                    (eApp (eApp (eOp (c_op opPlus)) x) y)).

(** Decidable equality of defined types thus far: *)

Hint Resolve eq_nat_dec.

Theorem id_eqdec : 
  forall (x y : id),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

Theorem obj_eqdec : 
  forall (x y: object),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with prop_eqdec (x y : prop) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec.

Hint Resolve eq_nat_dec.

Fixpoint exp_eqdec (x y : exp) : {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.
(** Environment Functions *)

Definition filter (t:type) : type :=
let x := (Id 0) in
let P := ((var x) -: t) in
(Abs x Top Bool P (not P) None).

Definition mapping (t:type) : type :=
let x := (Id 0) in
(Abs x t t TT TT None).

Definition binary_mapping (t:type) : type :=
let x := (Id 0) in
      (Abs x 
          Nat (Abs x t t TT TT None)
          TT TT
          None).

(** Constant types: *)
Definition const_type (c : const_op) : type :=
let x := (Id 0) in
  match c with
    | opIsNat => (filter Nat)
    | opIsProc => (filter (Abs x Bot Top TT TT None))
    | opIsBool => (filter Bool)
    | opAdd1 => (mapping Nat)
    | opIsZero =>
      (Abs x 
          Nat Bool
          TT TT
          None)
    | opPlus => (binary_mapping Nat)
  end.

(** * Utility Functions 
 Substitution, free variable checking, etc... *)

(** Free variable/substitution calculations: *)

Definition id_remove := remove id_eqdec.

Definition id_In_dec := In_dec id_eqdec.


Fixpoint fv_set_opto (o : opt object) : list id :=
  match o with
    | None => []
    | Some (obj x) => [x]
  end.

Fixpoint fv_set_t (t : type) : list id :=
  match t with
    | U t1 t2 => (fv_set_t t1) ++ (fv_set_t t2)
    | Abs x t1 t2 p1 p2 o =>
      app (fv_set_t t1)
          (id_remove
             x ((fv_set_t t2)
                ++ (fv_set_p p1)
                ++ (fv_set_p p2)
                ++ (fv_set_opto o)))
    | _ => nil
  end

(* free variables in propositions *)
with fv_set_p (p: prop) : list id :=
  match p with
    | (obj x) -: t =>  x::(fv_set_t t)
    | (obj x) -! t => x::(fv_set_t t)
    | p && q => app (fv_set_p p) (fv_set_p q)
    | p || q => app (fv_set_p p) (fv_set_p q)
    | _ => nil
  end.

(** Substitution functions: *)
Definition subst_o (newobj: opt object) (z:id) (o: opt object) : opt object :=
  match o with
    | None => None
    | Some (obj x) =>
      match id_eqdec x z, newobj with
        | Yes, None => None
        | Yes, Some (obj y) => Some (obj y)
        | No, _ => o
      end
  end.

(** Substitution functions: *)

Fixpoint subst_p
         (newo:opt object)
         (x:id) 
         (p:prop) : prop :=
  match p with
    | (obj z) -: t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => TT
            | Some (obj y) =>
              (obj y) -: (subst_t newo x t)
          end
        | No => if id_In_dec z (fv_set_t t)
                then TT
                else p
      end
    | (obj z) -! t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => TT
            | Some (obj y) =>
              (obj y) -! (subst_t newo x t)
          end
        | No => if id_In_dec z (fv_set_t t)
                then TT
                else p
      end
    | P || Q => (subst_p newo x P) || (subst_p newo x Q)
    | P && Q => (subst_p newo x P) && (subst_p newo x Q)
    | _ => p
  end

with subst_t
       (newo:opt object)
       (x:id) 
       (t:type): type :=
  match t with
    | U t1 t2 => U (subst_t newo x t1) (subst_t newo x t2)
    | Abs y t1 t2 p1 p2 opto =>
      if id_eqdec x y
      then Abs y
               (subst_t newo x t1) 
               t2
               p1 p2
               opto
      else Abs y
               (subst_t newo x t1)
               (subst_t newo x t2)
               (subst_p newo x p1)
               (subst_p newo x p2)
               (subst_o newo x opto)
    | _ => t
  end.

Definition rem_p (p:prop) (l:list prop) : (list prop) :=
remove prop_eqdec p l.