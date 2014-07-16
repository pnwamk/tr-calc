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

(** Types and propositions: *)
(** Types and propositions: *)
Inductive type : Set :=
| tTop  : type
| tBot  : type
| tNat  : type
| tStr  : type
| tT    : type
| tF    : type
| tCons : type
| tU    : type -> type -> type
| tPair : type -> type -> type
| tλ    : id -> type -> type -> prop -> opt object -> type

with prop : Set :=
| Atom : fact -> prop
| And  : prop -> prop -> prop
| Or   : prop -> prop -> prop
| Imp  : prop -> prop -> prop
| TT   : prop
| FF   : prop
| Unk  : prop

with fact : Set :=
| istype : object -> type -> fact.
Hint Constructors type prop fact.

Fixpoint Not (P:prop) : prop :=
  match P with
    | Atom f => (Imp (Atom f) FF)
    | And P Q => Or (Not P) (Not Q)
    | Or P Q  => And (Not P) (Not Q)
    | Imp P Q => And P (Not Q)
    | FF => TT
    | TT => FF
    | Unk => Unk
  end.

Notation tBool := (tU tT tF).

Infix "::=" := (fun o t => Atom (istype o t)) 
                 (at level 30, right associativity).
Infix "::~" := (fun o t => (Imp (Atom (istype o t)) FF))
                 (at level 30, right associativity).
Notation "P '&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Or P Q) (at level 50, left associativity).
Notation "P '-->' Q" := (Imp P Q) (at level 90).

Inductive formula : Set :=
| Elem      : fact -> formula
| Conj      : formula -> formula -> formula
| Disj      : formula -> formula -> formula
| Impl      : formula -> formula -> formula
| Truth     : formula
| Falsehood : formula.

Fixpoint Negate (F:formula) : formula :=
  match F with
    | Elem f => (Impl (Elem f) Falsehood)
    | Conj P Q => Disj (Negate P) (Negate Q)
    | Disj P Q  => Conj (Negate P) (Negate Q)
    | Impl P Q => Conj P (Negate Q)
    | Falsehood => Truth
    | Truth => Falsehood
  end.

Definition unk_form (b:bool) :=
  match b with
    | true => Truth
    | false => Falsehood
  end.

Fixpoint formulate' (b:bool) (p:prop) : formula :=
  match p with
    | Atom f => (Elem f)
    | And P Q => Conj (formulate' b P) (formulate' b Q)
    | Or P Q  => Disj (formulate' b P) (formulate' b Q)
    | Imp P Q => Disj (formulate' (negb b) P) (formulate' b Q)
    | FF => Falsehood
    | TT => Truth
    | Unk => unk_form b
  end.

Definition formulate := formulate' true.

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
    | TT => 0
    | FF => 0
    | Unk => 0
  end.
Hint Unfold type_weight prop_weight.

Fixpoint formula_weight (f:formula) : nat :=
  match f with
    | Elem (istype o t) => type_weight t
    | Conj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Disj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Impl P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Truth => 0
    | Falsehood => 0
  end.

Hint Unfold formulate formulate'.

Lemma form'_leq : forall p b1 b2,
formula_weight (formulate' b1 p) <= formula_weight (formulate' b2 p).
Proof.
  intros p.
  induction p; crush.
  specialize (IHp1 b1 b2).
  specialize (IHp2 b1 b2).
  crush.
  specialize (IHp1 b1 b2).
  specialize (IHp2 b1 b2).
  crush.
  specialize (IHp1 (negb b1) (negb b2)).
  specialize (IHp2 b1 b2).
  crush.
  destruct b1; simpl; omega.
Qed.

Lemma form_leq_prop : forall p,
prop_weight p <= formula_weight (formulate p).
Proof.
  intros p.
  induction p; crush.
  unfold formulate'.
  fold formulate'.
  fold formulate.
  crush.
  fold formulate.
  crush.
  unfold formulate'.
  fold formulate'.
  unfold formulate in *.
  remember (form'_leq p1 true false).
  crush.
Qed.

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
with prop_eqdec (x y : prop) : {x=y}+{x<>y}
with fact_eqdec (x y : fact) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec fact_eqdec.

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
          (Some (var x)))
    | opIsProc =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tλ x tBot tTop TT None)) 
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
    | opAdd1 =>
      (tλ x 
          tNat tNat
          TT
          None)
    | opIsZero =>
      (tλ x 
          tNat tBool
          TT
          None)
    | opIsStr =>
      (tλ x 
          tTop tBool
          ((var x) ::= tStr)
          None)
    | opStrLen =>
      (tλ x 
          tStr tNat
          TT
          None)
    | opPlus =>
      (tλ x 
          tNat 
          (tλ x 
              tNat tNat
              TT
              None)
          TT
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
    | Atom f => fv_set_f f
    | p && q => app (fv_set_p p) (fv_set_p q)
    | p || q => app (fv_set_p p) (fv_set_p q)
    | _ => nil
  end

with fv_set_f (f:fact) : list id :=
  match f with
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
    | Atom f => 
      match (subst_f b f opto x) with
        | None => TT
        | Some f' => Atom f'
      end
    | P || Q => (subst_p' b P opto x) || (subst_p' b Q opto x)
    | P && Q => (subst_p' b P opto x) && (subst_p' b Q opto x)
    | _ => p
  end

with subst_f
       (b:bool)
       (f:fact)
       (opto:opt object)
       (x:id) : opt fact :=     
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

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Definition subst_p := subst_p' true.
Definition subst_t := subst_t' true.

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


Fixpoint rem (p:prop) (l:list prop) : list prop :=
  match l with
    | nil => nil
    | p' :: ps =>
      if prop_eqdec p p' 
      then rem p ps
      else p' :: (rem p ps)
  end.


