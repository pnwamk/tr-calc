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

Inductive step : Set := car | cdr.
Hint Constructors step.

Definition path : Set := list step.

Inductive object : Set :=
| obj : path -> id -> object.
Hint Constructors object.

Notation var := (obj []).

Inductive base : Set :=
  Base : nat ->base.

(** Types and propositions: *)
(** Types and propositions: *)
Inductive type : Set :=
| tTop  : type
| tBot  : type
| tBase : base -> type
| tU    : type -> type -> type
| tPair : type -> type -> type
| tλ    : id -> type -> type -> prop -> opt object -> type

with prop : Set :=
| Atom        : datum -> prop
| And         : prop -> prop -> prop
| Or          : prop -> prop -> prop
| Imp         : prop -> prop -> prop
| Truth       : prop
| Falsehood   : prop
| Unk         : prop

with datum : Set :=
| istype : object -> type -> datum.
Hint Constructors type prop datum.

Notation tT := (tBase (Base 0)).
Notation tF := (tBase (Base 1)).
Notation tNat := (tBase (Base 2)).
Notation tStr := (tBase (Base 3)).
Notation tCons := (tBase (Base 4)).
Notation tBool := (tU tT tF).

Fixpoint Not (P:prop) : prop :=
  match P with
    | Atom f => (Imp (Atom f) Falsehood)
    | And P Q => Or (Not P) (Not Q)
    | Or P Q  => And (Not P) (Not Q)
    | Imp P Q => And P (Not Q)
    | Falsehood => Truth
    | Truth => Falsehood
    | Unk => Unk
  end.

Infix ":::=" := (fun o t => Atom (istype o t)) 
                 (at level 30, right associativity).
Infix ":::~" := (fun o t => (Imp (Atom (istype o t)) Falsehood))
                 (at level 30, right associativity).
Notation "P '&&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '|||' Q" := (Or P Q) (at level 50, left associativity).
Notation "P '=-->' Q" := (Imp P Q) (at level 90).

Inductive formula : Set :=
| Elem      : datum -> formula
| Conj      : formula -> formula -> formula
| Disj      : formula -> formula -> formula
| Impl      : formula -> formula -> formula
| TT        : formula
| FF        : formula.

Infix "::=" := (fun o t => Elem (istype o t)) 
                 (at level 30, right associativity).
Infix "::~" := (fun o t => (Impl (Elem (istype o t)) FF))
                 (at level 30, right associativity).
Notation "P '&&' Q" := (Conj P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Disj P Q) (at level 50, left associativity).
Notation "P '=->' Q" := (Impl P Q) (at level 90).


Fixpoint Negate (F:formula) : formula :=
  match F with
    | Elem f => (Impl (Elem f) FF)
    | Conj P Q => Disj (Negate P) (Negate Q)
    | Disj P Q  => Conj (Negate P) (Negate Q)
    | Impl P Q => Conj P (Negate Q)
    | FF => TT
    | TT => FF
  end.

Definition unk_form (b:bool) : formula :=
  match b with
    | true => FF
    | false => TT
  end.

Fixpoint formulate' (b:bool) (p:prop) : formula :=
  match p with
    | Atom f => (Elem f)
    | And P Q => Conj (formulate' b P) (formulate' b Q)
    | Or P Q  => Disj (formulate' b P) (formulate' b Q)
    | Imp P Q => Disj (formulate' (negb b) P) (formulate' b Q)
    | Falsehood => FF
    | Truth => TT
    | Unk => unk_form b
  end.

(* Assumptions of Unk in positive position are
   mapped to FF, representing their inability
   to be proven non-trivially (i.e. w/o FF as an assumption) *)
Definition question := formulate' true.

(* Assumptions of Unk in positive position are
   mapped to TT, representing their inability
   to witness any particular fact *)
Definition assume   := formulate' false.


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
with datum_eqdec (x y : datum) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec datum_eqdec.

Theorem form_eqdec : forall f1 f2 : formula,
{f1 = f2} + {f1 <> f2}.
Proof.
  repeat decide equality.
Defined.


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
          ((var x) :::= tNat)
          (Some (var x)))
    | opIsProc =>
      (tλ x 
          tTop tBool
          ((var x) :::= (tλ x tBot tTop Truth None)) 
          None)
    | opIsBool =>
      (tλ x 
          tTop tBool
          ((var x) :::= tBool)
          None)
    | opIsCons =>
      (tλ x 
          tTop tBool
          ((var x) :::= (tPair tTop tTop))
          None)
    | opAdd1 =>
      (tλ x 
          tNat tNat
          Truth
          None)
    | opIsZero =>
      (tλ x 
          tNat tBool
          Truth
          None)
    | opIsStr =>
      (tλ x 
          tTop tBool
          ((var x) :::= tStr)
          None)
    | opStrLen =>
      (tλ x 
          tStr tNat
          Truth
          None)
    | opPlus =>
      (tλ x 
          tNat 
          (tλ x 
              tNat tNat
              Truth
              None)
          Truth
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

(** Free variable calculations: *)
(* free variables in objects *)
Definition fv_set_o (opto : opt object) : list id :=
  match opto with
    | None => []
    | Some (obj _ x) => [x]
  end.

(* free variables in types *)

Fixpoint fv_set_t (t : type) : list id :=
  match t with
    | tU lhs rhs =>
      app (fv_set_t lhs) (fv_set_t rhs)
    | tλ x t1 t2 p1 o =>
      app_all
           [[x];
             (fv_set_t t1);
             (fv_set_t t2);
             (fv_set_p p1);
             (fv_set_o o)]
    | tPair t1 t2 =>
      app (fv_set_t t1)
             (fv_set_t t2)
    | _ => nil
  end

(* free variables in propositions *)
with fv_set_p (p: prop) : list id :=
  match p with
    | Atom d => fv_set_d d
    | p &&& q => app (fv_set_p p) (fv_set_p q)
    | p ||| q => app (fv_set_p p) (fv_set_p q)
    | _ => nil
  end

with fv_set_d (d:datum) : list id :=
  match d with
    | istype o t => 
      app (fv_set_o (Some o)) (fv_set_t t)
  end.

(** Substitution functions: *)
Definition subst_o (o newobj: opt object) (z:id) : opt object :=
  match o with
    | None => None
    | Some (obj pth1 x) =>
      match id_eqdec x z, newobj with
        | left _, None => None
        | left _, Some (obj pth2 y) => Some (obj (pth1 ++ pth2) y)
        | right _, _ => o
      end
  end.


(** _we use true/false instead of +/- for substitution_ *)
Fixpoint subst_p'
         (b:bool)
         (p:prop)
         (opto:opt object)
         (x:id) : prop :=
  match p with
    | Atom d => 
      match (subst_d b d opto x) with
        | None => Truth
        | Some f' => Atom f'
      end
    | P ||| Q => (subst_p' b P opto x) ||| (subst_p' b Q opto x)
    | P &&& Q => (subst_p' b P opto x) &&& (subst_p' b Q opto x)
    | P =--> Q => (subst_p' (negb b) P opto x) =--> (subst_p' b Q opto x)
    | _ => p
  end

with subst_d
       (b:bool)
       (f:datum)
       (opto:opt object)
       (x:id) : opt datum :=     
  match f with
    | istype (obj pth1 z) t =>
      match id_eqdec x z , In_dec id_eqdec z (fv_set_t t) with
        | Yes, _ =>
          match opto with
            | None => None
            | Some (obj pth2 y) =>
              Some (istype (obj (pth1 ++ pth2) y) (subst_t' b t opto x))
          end
        | No, No => Some f
        | No, Yes => None
      end
  end

with subst_t'
       (b:bool)
       (t:type)
       (opto:opt object)
       (x:id) : type :=
  match t with
    | tU lhs rhs => tU (subst_t' b lhs opto x) 
                       (subst_t' b rhs opto x)
    | tλ y t1 t2 p1 opto2 =>

      if id_eqdec x y
      then t
      else tλ y
                (subst_t' b t1 opto x)
                (subst_t' b t2 opto x)
                (subst_p' b p1 opto x)
                (subst_o opto2 opto x)
    | tPair t1 t2 => tPair (subst_t' b t1 opto x)
                           (subst_t' b t2 opto x)
    | _ => t
  end.

Fixpoint subst_f'
         (b:bool)
         (f:formula)
         (opto:opt object)
         (x:id) : formula :=
  match f with
    | Elem d => 
      match (subst_d b d opto x) with
        | None => TT
        | Some f' => Elem f'
      end
    | P || Q => (subst_f' b P opto x) || (subst_f' b Q opto x)
    | P && Q => (subst_f' b P opto x) && (subst_f' b Q opto x)
    | P =-> Q => (subst_f' (negb b) P opto x) =-> (subst_f' b Q opto x)
    | _ => f
  end.


(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Definition subst_p := subst_p' true.
Definition subst_t := subst_t' true.
Definition subst_f := subst_f' true.

Lemma split_nonnil {X:Type} : forall l1 l2 (x:X),
nil <> l1 ++ (x :: l2).
Proof.
  intros. destruct l1; destruct l2; crush.
Defined.


(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 

(** A few helpers to reason about subtyping: *)

Fixpoint is_tU (t:type) : opt (type * type) :=
  match t with
    | tU t1 t2 => Some (t1,t2)
    | _ => None
  end.

Lemma is_tU_eq : forall t t1 t2,
Some (t1,t2) = is_tU t
-> t = tU t1 t2.
Proof.
  intros.
  destruct t; crush.
Defined.
  
Fixpoint is_tλ (t:type) : opt (id * type * type * prop * (opt object)) :=
  match t with
    | tλ x t1 t2 p opto => Some (x,t1,t2,p,opto)
    | _ => None
  end.

Lemma is_tλ_eq : forall t x t1 t2 p opto,
Some (x,t1,t2,p,opto) = is_tλ t
-> t = tλ x t1 t2 p opto.
Proof.
  intros.
  destruct t; crush.
Defined.

Fixpoint is_tPair (t:type) : opt (type * type) :=
  match t with
    | tPair t1 t2 => Some (t1,t2)
    | _ => None
  end.

Lemma is_tPair_eq : forall t t1 t2,
Some (t1,t2) = is_tPair t
-> t = tPair t1 t2.
Proof.
  intros.
  destruct t; crush.
Defined.


Fixpoint rem (f:formula) (l:list formula) : list formula :=
  match l with
    | nil => nil
    | f' :: fs =>
      if form_eqdec f f' 
      then rem f fs
      else f' :: (rem f fs)
  end.


(** Weighting for types/props *)
Fixpoint type_weight (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      2 + (plus (type_weight t1) (type_weight t2))
    | tλ x t1 t2 p _ => 2 + (type_weight t1) 
                        + (type_weight t2)
                        + (prop_weight p)
                                               
    | tPair t1 t2 => 4 + (plus (type_weight t1) (type_weight t2))
    | _ => 1
  end

with prop_weight (p:prop) : nat :=
  match p with
    | Atom (istype o t) => type_weight t
    | And P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Or P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Imp P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Truth => 1
    | Falsehood => 0
    | Unk => 1
  end.
Hint Unfold type_weight prop_weight.

Fixpoint formula_weight (f:formula) : nat :=
  match f with
    | Elem (istype o t) => type_weight t
    | Conj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Disj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Impl P Q => 1 + (formula_weight P) + (formula_weight Q)
    | TT => 1
    | FF => 0
  end.

Hint Unfold formulate' question assume.


Fixpoint env_weight (l:list formula) : nat :=
  match l with
    | nil => 0
    | f :: fs => (formula_weight f) + (env_weight fs)
  end.
Hint Unfold env_weight.

Definition proof_weight (p:(list formula) * formula) : nat :=
plus (env_weight (fst p)) (formula_weight (snd p)).
Hint Unfold proof_weight.
