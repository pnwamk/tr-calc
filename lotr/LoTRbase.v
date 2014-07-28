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

Inductive value : Set :=
  Val : nat -> value.

Inductive step : Set := car | cdr.
Hint Constructors step.

Definition path : Set := list step.

Inductive object : Set :=
| obj : path -> id -> object.
Hint Constructors object.

Notation var := (obj []).

(** Types and propositions: *)
Inductive type : Set :=
| tTop : type
| tBot : type
| tVal : value -> type
| tU   : type -> type -> type
| tP   : type -> type -> type
| tλ   : id -> type -> type -> prop -> prop -> opt object -> type

with prop : Set :=
| Is      : object -> type -> prop
| Not     : object -> type -> prop
| And     : prop -> prop -> prop
| Or      : prop -> prop -> prop
| Imp     : prop -> prop -> prop
| TT      : prop
| FF      : prop.
Hint Constructors type prop.

Inductive CompoundType : type -> Prop :=
| CT_U :
    forall t1 t2,
      CompoundType (tU t1 t2)
| CT_P :
    forall t1 t2,
      CompoundType (tP t1 t2).

Inductive CompoundProp : prop -> Prop :=
| CP_Is :
    forall o t,
      CompoundType t
      -> CompoundProp (Is o t)
| CP_Not :
    forall o t,
      CompoundType t
      -> CompoundProp (Not o t).
Hint Constructors CompoundProp.

Notation tT := (tVal (Val 0)).
Notation tF := (tVal (Val 1)).
Notation tNat := (tVal (Val 2)).
Notation tStr := (tVal (Val 3)).
Notation tCons := (tVal (Val 4)).

Notation tBool := (tU tT tF).

Infix "::=" := Is 
                 (at level 30, right associativity).
Infix "::~" := Not
                 (at level 30, right associativity).
Notation "P '&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Or P Q) (at level 50, left associativity).
Notation "P '=->' Q" := (Imp P Q) (at level 51).

Definition car_at (o:object) : object :=
  match o with
    | obj π x => obj (π++[car]) x
  end.

Definition cdr_at (o:object) : object :=
  match o with
    | obj π x => obj (π++[cdr]) x
  end.

Fixpoint reduce_Is (o:object) (t:type) : prop :=
  match t with
    | tU t1 t2 => ((o ::= t1) || (o ::= t2))
    | tP t1 t2 => ((o ::= tCons) 
                     && (reduce_Is (car_at o) t1) 
                     && (reduce_Is (cdr_at o) t2))
    | _ => (Is o t)
  end.

Fixpoint reduce_Not (o:object) (t:type) : prop :=
  match t with
    | tU t1 t2 => ((o ::~ t1) && (o ::~ t2))
    | tP t1 t2 => ((o ::~ tCons) 
                     || (reduce_Not (car_at o) t1) 
                     || (reduce_Not (cdr_at o) t2))
    | _ => (Is o t)
  end.

Fixpoint reduce (p:prop) : prop :=
  match p with
    | Is o t => (reduce_Is o t)
    | Not o t => (reduce_Not o t)
    | _ => p
  end.


(** Expressions and primitive operations: *)
Inductive const_op :=
  opAdd1 | opIsZero | opIsNat | opIsBool | opIsProc | 
  opIsCons | opIsStr | opStrLen | opPlus.
Hint Constructors const_op.

Inductive poly_op :=
 opCar | opCdr.
Hint Constructors poly_op.

Inductive op : Type :=
| c_op : const_op -> op
| p_op : poly_op -> op.
Hint Constructors op.

Inductive exp : Type :=
| eNat : nat -> exp
| eTrue  : exp
| eFalse : exp
| eStr : string -> exp
| eVar : id -> exp
| eTVar : id -> type -> exp
| eOp  : op -> exp
| eIf  : exp -> exp -> exp -> exp
| eλ : id -> type -> exp -> exp
| eApp : exp -> exp -> exp
| eLet : id -> exp -> exp -> exp
| eCons : exp -> exp -> exp.
Hint Constructors exp.

Inductive TypedExp : exp -> Prop :=
| TNat n : TypedExp (eNat n)
| TTrue : TypedExp eTrue
| TFalse : TypedExp eFalse
| TStr s : TypedExp (eStr s)
| TVar x t : TypedExp (eTVar x t)
| TIf e1 e2 e3 : TypedExp e1
                 -> TypedExp e2
                 -> TypedExp e3
                 -> TypedExp (eIf e1 e2 e3)
| Tλ x t e : TypedExp e -> TypedExp (eλ x t e)
| TApp e1 e2 : TypedExp e1
               -> TypedExp e2
               -> TypedExp (eApp e1 e2)
| TLet x e1 e2 : TypedExp e1
                 -> TypedExp e2
                 -> TypedExp (eLet x e1 e2)
| TCons e1 e2 : TypedExp e1
                -> TypedExp e2
                -> TypedExp (eCons e1 e2).

Inductive LTEq : exp -> exp -> Prop :=
| LTEq_Refl e  : LTEq e e
| LTEq_Var x t : LTEq (eTVar x t) (eVar x)
| LTEq_If e1 e2 e3 e1' e2' e3' : 
    LTEq e1 e1'
    -> LTEq e2 e2'
    -> LTEq e3 e3'
    -> LTEq (eIf e1 e2 e3) (eIf e1' e2' e3')
| LTEq_λ x t e e' : 
    LTEq e e'
    -> LTEq (eλ x t e) (eλ x t e')
| LTEq_App e1 e2 e1' e2' : 
    LTEq e1 e1'
    -> LTEq e2 e2'
    -> LTEq (eApp e1 e2) (eApp e1' e2')
| LTEq_Let x e1 e2 e1' e2' : 
    LTEq e1 e1'
    -> LTEq e2 e2'
    -> LTEq (eLet x e1 e2) (eLet x e1' e2')
| LTEq_Cons e1 e2 e1' e2' : 
    LTEq e1 e1'
    -> LTEq e2 e2'
    -> LTEq (eCons e1 e2) (eCons e1' e2').


Notation "$" := eVar.
Notation "t$" := eTVar.
Notation "#t" := eTrue.
Notation "#f" := eFalse.
Notation "#" := eNat.
Notation λ := eλ.
Notation Str := eStr.
Notation If := eIf.
Notation Let := eLet.
Notation Apply := eApp.
Notation Car  := (eApp (eOp (p_op opCar))).
Notation Cdr := (eApp (eOp (p_op opCdr))).
Notation Add1 := (eApp (eOp (c_op opAdd1))).
Notation "Zero?" := (eApp (eOp (c_op opIsZero))).
Notation "Nat?" := (eApp (eOp (c_op opIsNat))).
Notation "Bool?" := (eApp (eOp (c_op opIsBool))).
Notation "Proc?" := (eApp (eOp (c_op opIsProc))).
Notation "Cons?" := (eApp (eOp (c_op opIsCons))).
Notation Cons := eCons.
Notation "Str?" := (eApp (eOp (c_op opIsStr))).
Notation StrLen := (eApp (eOp (c_op opStrLen))).
Notation Plus := (fun x y =>
                    (eApp (eApp (eOp (c_op opPlus)) x) y)).


(** Weighting for types/props *)
Fixpoint type_weight (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      2 + (plus (type_weight t1) (type_weight t2))
    | tλ x t1 t2 p1 p2 _ => 
      2 + (type_weight t1) 
      + (type_weight t2)
      + (prop_weight p1)
      + (prop_weight p2)
                                               
    | tP t1 t2 => 4 + (plus (type_weight t1) (type_weight t2))
    | _ => 1
  end

with prop_weight (p:prop) : nat :=
  match p with
    | Is o t => type_weight t
    | Not o t => type_weight t
    | And P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Or P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Imp P Q => 1 + (prop_weight P) + (prop_weight Q)
    | TT => 1
    | FF => 0
  end.
Hint Unfold type_weight prop_weight.

Fixpoint env_weight (l:list prop) : nat :=
  match l with
    | nil => 0
    | p :: ps => (prop_weight p) + (env_weight ps)
  end.
Hint Unfold env_weight.

Definition proof_weight (p:(list prop) * prop) : nat :=
plus (env_weight (fst p)) (prop_weight (snd p)).
Hint Unfold proof_weight.


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
with prop_eqdec (x y : prop) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec.

Theorem exp_eqdec : forall e1 e2 : exp,
{e1 = e2} + {e1 <> e2}.
Proof.
  repeat decide equality.
Defined.
(** Environment Functions *)

(** Constant types: *)
Definition const_type (c : const_op) : type :=
let x := (Id 0) in
  match c with
    | opIsNat =>
      (tλ x 
          tTop tBool
          ((var x) ::= tNat)
          ((var x) ::~ tNat)
          None)
    | opIsProc =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tλ x tBot tTop) TT FF None)
          ((var x) ::~ (tλ x tBot tTop) TT FF None)
          None)
    | opIsBool =>
      (tλ x 
          tTop tBool
          ((var x) ::= tBool)
          ((var x) ::= tBool)
          None)
    | opIsCons =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tP tTop tTop))
          ((var x) ::~ (tP tTop tTop))
          None)
    | opAdd1 =>
      (tλ x 
          tNat tNat
          TT 
          FF
          None)
    | opIsZero =>
      (tλ x 
          tNat tBool
          TT 
          FF
          None)
    | opIsStr =>
      (tλ x 
          tTop tBool
          ((var x) ::= tStr)
          ((var x) ::~ tStr)
          None)
    | opStrLen =>
      (tλ x 
          tStr tNat
          TT 
          FF
          None)
    | opPlus =>
      (tλ x 
          tNat
          (tλ x 
              tNat tNat
              TT FF
              None)
          TT FF
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

Definition propify (b:bool) : prop := if b then TT else FF.

Fixpoint fv_set_opto (o : opt object) : list id :=
  match o with
    | None => []
    | Some (obj _ x) => [x]
  end.

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

Definition αsubst_o (newobj: opt object) (z:id) (o: opt object) : opt object :=
  match o with
    | None => None
    | Some (obj pth1 x) =>
      match id_eqdec x z, newobj with
        | Yes, None => o (* different - doesn't erase *)
        | Yes, Some (obj pth2 y) => Some (obj (pth1 ++ pth2) y)
        | No, _ => o
      end
  end.


(** Substitution functions: *)
Fixpoint αsubst_p'
         (newo:opt object)
         (x:id) 
         (p:prop)
         (b:bool) : prop :=
  match p with
    | Is (obj pth1 z) t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => p (* diff - no erase *)
            | Some (obj pth2 y) =>
              Is (obj (pth1 ++ pth2) y) (αsubst_t' newo x t b)
          end
        | No => if id_In_dec z (fv_set_t t)
                then p (* diff - no erase *)
                else p
      end
    | Not (obj pth1 z) t => 
      match id_eqdec x z with
        | Yes =>
          match newo with
            | None => p (* diff - no erase *)
            | Some (obj pth2 y) =>
              Not (obj (pth1 ++ pth2) y) (αsubst_t' newo x t b)
          end
        | No => if id_In_dec z (fv_set_t t)
                then p (* diff - no erase *)
                else p
      end
    | P || Q => (αsubst_p' newo x P b) || (αsubst_p' newo x Q b)
    | P && Q => (αsubst_p' newo x P b) && (αsubst_p' newo x Q b)
    | P =-> Q => (αsubst_p' newo x P (negb b)) =-> (αsubst_p' newo x Q b)
    | _ => p
  end

with αsubst_t'
       (newo:opt object)
       (x:id) 
       (t:type)
       (b:bool): type :=
  match t with
    | tU lhs rhs => tU (αsubst_t' newo x lhs b) 
                       (αsubst_t' newo x rhs b)
    | tλ y t1 t2 p1 p2 opto =>
      if id_eqdec x y
      then tλ y
              (αsubst_t' newo x t1 b) t2
              p1 p2
              opto
      else tλ y
              (αsubst_t' newo x t1 b)
              (αsubst_t' newo x t2 b)
              (αsubst_p' newo x p1 b)
              (αsubst_p' newo x p2 b)
              (subst_o newo x opto)
    | tP t1 t2 => tP (αsubst_t' newo x t1 b)
                     (αsubst_t' newo x t2 b)
    | _ => t
  end.

(** All uses of αsubst_p' and αsubst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Definition αsubst_p := (fun newo x p => αsubst_p' newo x p true).
Definition αsubst_t := (fun newo x t => αsubst_t' newo x t true).
