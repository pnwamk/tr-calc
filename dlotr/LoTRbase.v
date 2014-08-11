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

Inductive step : Set := 
| car : step
| cdr : step
| ref : nat -> step
| len : step.
Hint Constructors step.

Definition path : Set := list step.

Inductive object : Set :=
| obj : path -> id -> object.
Hint Constructors object.

Notation var := (obj []).

Inductive term :=
| Term : Z -> object -> term.

Inductive linexp :=
| LinExp : list term -> Z -> linexp.

Definition linexp_add1 (l:linexp) : linexp :=
  match l with
    | LinExp ts c => LinExp ts (1 + c)
  end.

Inductive lineq :=
| LIneq : linexp -> linexp -> lineq.

Definition not_lineq (l:lineq) : lineq :=
  match l with
      | LIneq lhs rhs => 
        LIneq (linexp_add1 rhs) lhs
  end.

Definition sli := list lineq.

Variable sli_satisfiable : sli -> bool.

(** Types and propositions: *)
Inductive type : Set :=
| tTop    : type
| tNum    : type
| tDNum   : object -> sli -> type
| tTrue   : type
| tFalse  : type
| tCons   : type
| tArray  : type
| tUnion  : tlist -> type
| tPair   : type -> type -> type
| tVec    : tlist -> type
| tλ      : id -> type -> type -> prop -> opt object -> type

with prop : Set :=
| IS    : object -> type -> prop
| ISNT  : object -> type -> prop
| AND   : prop -> prop -> prop
| OR    : prop -> prop -> prop
| IMP   : prop -> prop -> prop
| SLI   : sli -> prop
| TRUE  : prop
| FALSE : prop
| UNK   : prop

with tlist : Set :=
| tnil : tlist
| tcons : type -> tlist -> tlist.
Hint Constructors type prop tlist.

Fixpoint not_sli (s:sli) : prop :=
  match s with
    | nil => FALSE
    | l::ls => (OR (SLI ((not_lineq l)::nil)) (not_sli ls))
  end.

Fixpoint not (P:prop) : prop :=
  match P with
    | IS o t => ISNT o t
    | ISNT o t => IS o t
    | AND p q => OR (not p) (not q)
    | OR p q => AND (not p) (not q)
    | IMP p q => AND (not p) q
    | SLI sys => not_sli sys
    | TRUE => FALSE
    | FALSE => TRUE
    | UNK => UNK
  end.

Inductive CompoundType : type -> Prop :=
| CT_U :
    forall ts,
      CompoundType (tUnion ts)
| CT_P :
    forall t1 t2,
      CompoundType (tPair t1 t2)
| CT_V :
    forall ts,
      CompoundType (tVec ts).

Inductive CompoundProp : prop -> Prop :=
| CP_Is :
    forall o t,
      CompoundType t
      -> CompoundProp (IS o t)
| CP_Not :
    forall o t,
      CompoundType t
      -> CompoundProp (ISNT o t).
Hint Constructors CompoundProp.

Notation tBool := (tUnion (tcons tTrue (tcons tFalse tnil))).
Notation tBot := (tUnion tnil).

Infix "::=" := IS 
                 (at level 30, right associativity).
Infix "::~" := ISNT
                 (at level 30, right associativity).
Notation "P '&&' Q" := (AND P Q) (at level 40, left associativity).
Notation "P '||' Q" := (OR P Q) (at level 50, left associativity).
Notation "P '=->' Q" := (IMP P Q) (at level 51).

Definition car_at (o:object) : object :=
  match o with
    | obj π x => obj (π++[car]) x
  end.

Definition cdr_at (o:object) : object :=
  match o with
    | obj π x => obj (π++[cdr]) x
  end.

Definition ref_at (i:nat) (o:object) : object :=
  match o with
    | obj π x => obj (π++[(ref i)]) x
  end.

Fixpoint reduce_UnionList (o:object) (l:tlist) : prop :=
  match l with
    | tnil => FALSE
    | tcons t ts => (OR (o ::= t) (reduce_UnionList o ts)) 
  end.

Fixpoint reduce_VecList_refs (o:object) (i:nat) (l:tlist) : prop :=
  match l with
    | tnil => TRUE
    | tcons t ts => (AND ((ref_at i o) ::= t) 
                    (reduce_VecList_refs o (1 + i) ts)) 
  end.

Fixpoint reduce_IS (o:object) (t:type) : prop :=
  match t with
    | tUnion ts => (reduce_UnionList o ts)
    | tVec ts => (o ::= tArray) && (reduce_VecList_refs o 0 ts)
    | tPair t1 t2 => ((o ::= tCons) 
                      && (reduce_IS (car_at o) t1) 
                      && (reduce_IS (cdr_at o) t2))
    | _ => (IS o t)
  end.

Definition reduce_ISNT (o:object) (t:type) : prop :=
not (reduce_IS o t).


Fixpoint reduce (p:prop) : prop :=
  match p with
    | IS o t => (reduce_IS o t)
    | ISNT o t => (reduce_ISNT o t)
    | _ => p
  end.


(** Expressions and primitive operations: *)
Inductive const_op :=
| opEq  : Z -> const_op
| opLEq : Z -> const_op
| opAdd1 : const_op
| opIsZero : const_op 
| opIsNum : const_op
| opIsBool : const_op
| opIsProc : const_op
| opIsCons : const_op
| opPlus : const_op
| opIsVec : const_op
| opLen : const_op.
Hint Constructors const_op.

Inductive poly_op :=
| opCar : poly_op
| opCdr : poly_op
| opRef : nat -> poly_op.
Hint Constructors poly_op.

Inductive op : Type :=
| c_op : const_op -> op
| p_op : poly_op -> op.
Hint Constructors op.

Inductive exp : Set :=
| eNum   : Z -> exp
| eTrue  : exp
| eFalse : exp
| eVar   : id -> exp
| eOp    : op -> exp
| eIf    : exp -> exp -> exp -> exp
| eλ     : id -> type -> exp -> exp
| eApp   : exp -> exp -> exp
| eLet   : id -> exp -> exp -> exp
| eCons  : exp -> exp -> exp
| eVec   : elist -> exp

with elist : Set :=
| enil : elist
| econs : exp -> elist -> elist.
Hint Constructors exp elist.

Notation "$" := eVar.
Notation "#t" := eTrue.
Notation "#f" := eFalse.
Notation "#" := eNum.
Notation λ := eλ.
Notation If := eIf.
Notation Let := eLet.
Notation Apply := eApp.
Notation Car  := (eApp (eOp (p_op opCar))).
Notation Cdr := (eApp (eOp (p_op opCdr))).
Notation "Ref[ n ]" := (eApp (eOp (p_op (opRef n)))).
Notation "Eq[ z ]" := (eApp (eOp (c_op (opEq z)))).
Notation "LEq[ z ]" := (eApp (eOp (c_op (opLEq z)))).
Notation Add1 := (eApp (eOp (c_op opAdd1))).
Notation "Zero?" := (eApp (eOp (c_op opIsZero))).
Notation "Num?" := (eApp (eOp (c_op opIsNum))).
Notation "Bool?" := (eApp (eOp (c_op opIsBool))).
Notation "Proc?" := (eApp (eOp (c_op opIsProc))).
Notation "Cons?" := (eApp (eOp (c_op opIsCons))).
Notation "Vec?" := (eApp (eOp (c_op opIsCons))).
Notation Cons := eCons.
Notation Vec := eVec.
Notation Plus := (fun x y =>
                    (eApp (eApp (eOp (c_op opPlus)) x) y)).

(** Decidable equality of defined types thus far: *)

Hint Resolve eq_nat_dec.

Theorem id_eqdec : 
  forall (x y : id),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

Theorem step_eqdec : 
  forall (x y: step),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve step_eqdec.

Hint Resolve list_eq_dec.

Theorem path_eqdec : 
  forall (x y: path),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eqdec.

Theorem obj_eqdec : 
  forall (x y: object),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with prop_eqdec (x y : prop) : {x=y}+{x<>y}
with tlist_eqdec (x y : tlist) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec tlist_eqdec.

Hint Resolve Z_eq_dec.

Fixpoint exp_eqdec (x y : exp) : {x=y}+{x<>y}
with elist_eqdec (x y : elist) : {x=y}+{x<>y}.
Proof.
  repeat decide equality.
  repeat decide equality.
Defined.
(** Environment Functions *)

(** Constant types: *)
Definition const_type (c : const_op) : type :=
let x := (Id 0) in
  match c with
    | opEq n =>
      (tλ x 
          tNum tBool
          ((var x) ::= (tDNum (var x) 
                              [(LIneq (LinExp [] n)
                                      (LinExp [(Term 1 (var x))] 0));
                                (LIneq (LinExp [(Term 1 (var x))] 0)
                                       (LinExp [] n))]))
          None)
    | opLEq n =>
      (tλ x 
          tNum tBool
          ((var x) ::= (tDNum (var x) 
                              [(LIneq (LinExp [(Term 1 (var x))] 0)
                                      (LinExp [] n))]))
          None)
    | opIsNum =>
      (tλ x 
          tTop tBool
          ((var x) ::= tNum)
          None)
    | opIsProc =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tλ x tBot tTop) TRUE None)
          None)
    | opIsBool =>
      (tλ x 
          tTop tBool
          ((var x) ::= tBool)
          None)
    | opIsCons =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tPair tTop tTop))
          None)
    | opIsVec =>
      (tλ x 
          tTop tBool
          ((var x) ::= tArray)
          None)
    | opLen =>
      (tλ x 
          tArray tNum
          TRUE
          None)
    | opAdd1 =>
      (tλ x 
          tNum tNum
          TRUE
          None)
    | opIsZero =>
      (tλ x 
          tNum tBool
          TRUE
          None)
    | opPlus =>
      (tλ x 
          tNum
          (tλ x 
              tNum tNum
              TRUE
              None)
          TRUE
          None)
  end.

(** * Utility Functions 
 Substitution, free variable checking, etc... *)

Fixpoint app_all {X:Type}
         (l:list (list X)) : list X :=
  match l with
    | nil => nil
    | x :: xs => x ++ (app_all xs)
  end.

(** Free variable/substitution calculations: *)

Definition id_remove := remove id_eqdec.

Definition id_In_dec := In_dec id_eqdec.

Definition propify (b:bool) : prop := if b then TRUE else FALSE.

Fixpoint fv_set_opto (o : opt object) : list id :=
  match o with
    | None => []
    | Some (obj _ x) => [x]
  end.
(* BOOKMARK *)
Fixpoint fv_set_t (t : type) : list id :=
  match t with
    | tU lhs rhs =>
      app (fv_set_t lhs) 
          (fv_set_t rhs)
    | tλ x t1 t2 p1 p2 o =>
      app (fv_set_t t1)
          (id_remove
             x 
             (app_all 
                [(fv_set_t t2);
                  (fv_set_p p1);
                  (fv_set_p p2);
                  (fv_set_opto o)]))
    | tP t1 t2 =>
      app (fv_set_t t1)
          (fv_set_t t2)
    | _ => nil
  end

(* free variables in propositions *)
with fv_set_p (p: prop) : list id :=
  match p with
    | Is (obj _ x) t =>  x::(fv_set_t t)
    | Not (obj _ x) t => x::(fv_set_t t)
    | p && q => app (fv_set_p p) (fv_set_p q)
    | p || q => app (fv_set_p p) (fv_set_p q)
    | p =-> q => app (fv_set_p p) (fv_set_p q)
    | _ => nil
  end.

(** Substitution functions: *)
Definition subst_o (newobj: opt object) (z:id) (o: opt object) : opt object :=
  match o with
    | None => None
    | Some (obj pth1 x) =>
      match id_eqdec x z, newobj with
        | Yes, None => None
        | Yes, Some (obj pth2 y) => Some (obj (pth1 ++ pth2) y)
        | No, _ => o
      end
  end.


(** Substitution functions: *)
Fixpoint subst_p'
         (newo:opt object)
         (x:id) 
         (p:prop)
         (b:bool) : prop :=
  match p with
    | Is (obj pth1 z) t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => propify b
            | Some (obj pth2 y) =>
              Is (obj (pth1 ++ pth2) y) (subst_t' newo x t b)
          end
        | No => if id_In_dec z (fv_set_t t)
                then propify b
                else p
      end
    | Not (obj pth1 z) t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => propify b
            | Some (obj pth2 y) =>
              Not (obj (pth1 ++ pth2) y) (subst_t' newo x t b)
          end
        | No => if id_In_dec z (fv_set_t t)
                then propify b
                else p
      end
    | P || Q => (subst_p' newo x P b) || (subst_p' newo x Q b)
    | P && Q => (subst_p' newo x P b) && (subst_p' newo x Q b)
    | P =-> Q => (subst_p' newo x P (negb b)) =-> (subst_p' newo x Q b)
    | _ => p
  end

with subst_t'
       (newo:opt object)
       (x:id) 
       (t:type)
       (b:bool): type :=
  match t with
    | tU lhs rhs => tU (subst_t' newo x lhs b) 
                       (subst_t' newo x rhs b)
    | tλ y t1 t2 p1 p2 opto =>
      if id_eqdec x y
      then tλ y
              (subst_t' newo x t1 b) 
              t2
              p1 p2
              opto
      else tλ y
              (subst_t' newo x t1 b)
              (subst_t' newo x t2 b)
              (subst_p' newo x p1 b)
              (subst_p' newo x p2 b)
              (subst_o newo x opto)
    | tP t1 t2 => tP (subst_t' newo x t1 b)
                     (subst_t' newo x t2 b)
    | _ => t
  end.

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Definition subst_p := (fun newo x p => subst_p' newo x p true).
Definition subst_t := (fun newo x t => subst_t' newo x t true).

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 

(** substitution functions for an alpha-varied environment *)