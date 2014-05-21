(* begin hide *)
Require Import LibTactics.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.
Require Import Coq.Program.Wf.

Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.
(* end hide *)

Section LTR.

(** * Basic Definitions for λTR *)

(** Identifiers and objects: *)
Notation opt := option.

Inductive id : Type :=
  Id : nat -> id.

Inductive step : Type := car | cdr.
Hint Constructors step.

Definition path : Type := list step.

Inductive object : Type :=
| obj : path -> id -> object.
Hint Constructors object.


(** Types and propositions: *)
Inductive type : Type :=
| tTop : type
| tBot : type
| tNum : type
| tTrue : type
| tFalse : type
| tUnion : type -> type -> type
| tPair : type -> type -> type
| tFun : id -> type -> prop -> prop -> opt object -> type -> type

with prop : Type :=
| Is    : object -> type -> prop
| IsNot : object -> type -> prop
| And   : prop -> prop -> prop
| Or    : prop -> prop -> prop
| Imp   : prop -> prop -> prop
| TT    : prop
| FF    : prop.
Hint Constructors type prop.

Notation tBool := (tUnion tTrue tFalse).

Infix "::=" := Is (at level 70, right associativity).
Infix "::~" := IsNot (at level 70, right associativity).
Infix "&" := And (at level 80, right associativity).
Infix "v" := Or (at level 85, right associativity).
Infix "-->" := Imp (at level 90, right associativity).

(** Expressions and primitive operations: *)
Inductive op : Type :=
opAdd1 | opIsZero | opIsNum | opIsBool | opIsProc | opIsCons | opCar | opCdr.
Hint Constructors op.

Inductive exp : Type :=
| eVar : id -> exp
| eOp  : op -> exp
| eT   : exp
| eF   : exp
| eNum : nat -> exp
| eIf  : exp -> exp -> exp -> exp
| eAbs : id -> type -> exp -> exp
| eApp : exp -> exp -> exp
| eLet : id -> exp -> exp.
Hint Constructors exp.
 
Notation Car' := (eOp opCar).
Notation Cdr' := (eOp opCdr).
Notation Add1' := (eOp opAdd1).
Notation IsZero' := (eOp opIsZero).
Notation IsNum' := (eOp opIsNum).
Notation IsBool' := (eOp opIsBool).
Notation IsProc' := (eOp opIsProc).
Notation IsCons' := (eOp opIsCons).

(** Decidable equality of defined types thus far: *)

Hint Resolve eq_nat_dec.

Theorem id_eqdec : forall (x y : id),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

Theorem step_eqdec : forall (x y: step),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve step_eqdec.

Hint Resolve list_eq_dec.
Theorem path_eqdec : forall (x y: path),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eqdec.

Theorem obj_eqdec : forall (x y: object),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with prop_eqdec (x y : prop) : {x=y}+{x<>y}.
Proof.
  decide equality.
  decide equality.
  decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec.

(** * Utility Functions 
 Substitution, free variable checking, etc... *)

Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y})
                       (l:list (set X)) : set X :=
match l with
| nil => nil
| x :: xs => set_union dec x (setU dec xs)
end.


(* free variables in objects *)
Definition fv_set_o (opto : opt object) : set id :=
match opto with
| None => []
| Some (obj _ x) => [x]
end.

(* free variables in types *)

Fixpoint fv_set_t (t : type) : set id :=
match t with
| tUnion lhs rhs =>
  set_union id_eqdec (fv_set_t lhs) (fv_set_t rhs)
| tFun x t1 p1 p2 o t2 =>
  setU id_eqdec
       [[x];
        (fv_set_t t1);
        (fv_set_p p1);
        (fv_set_p p2);
        (fv_set_o o);
        (fv_set_t t2)]
| tPair t1 t2 =>
  set_union id_eqdec
            (fv_set_t t1)
            (fv_set_t t2)
| _ => nil
end

(* free variables in propositions *)
with fv_set_p (p: prop) : set id :=
match p with
| o ::= t => set_union id_eqdec (fv_set_o (Some o)) (fv_set_t t)
| o ::~ t => set_union id_eqdec (fv_set_o (Some o)) (fv_set_t t)
| p & q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
| p v q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
| p --> q => set_union id_eqdec (fv_set_p p) (fv_set_p q) 
| _ => nil
end.


Definition subst_o (o newobj: opt object) (x:id) : opt object :=
match o with
| None => None
| Some (obj pth1 z) =>
  match id_eqdec x z, newobj with
  | left _, None => None
  | left _, Some (obj pth2 y) => Some (obj (pth1 ++ pth2) y)
  | right _, _ => o
  end
end.

Definition sign_truth (b:bool) : prop :=
match b with
| true => TT
| false => FF
end.

(* subst+ and - for properties*)
Fixpoint subst_p (b:bool)
                 (p:prop)
                 (opto:opt object)
                 (x:id) : prop :=
match p with
| (obj pth1 z) ::= t =>
  match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
  | left _, _ =>
    match opto with
    | None => (sign_truth b)
    | Some (obj pth2 y) =>
      Is (obj (pth1 ++ pth2) y) (subst_t b t opto x)
    end
  | right _, false => p
  | right _, true => (sign_truth b)
  end
| (obj pth1 z) ::~ t =>
  match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
  | left _, _ =>
    match opto with
    | None => (sign_truth b)
    | Some (obj pth2 y) =>
      Is (obj (pth1 ++ pth2) y) (subst_t b t opto x)
    end
  | right _, false => p
  | right _, true => (sign_truth b)
  end
| P --> Q => (subst_p (negb b) P opto x) --> (subst_p b Q opto x)
| P v Q => (subst_p b P opto x) v (subst_p b Q opto x)
| P & Q => (subst_p b P opto x) & (subst_p b Q opto x)
| _ => p
end

(* type substitution *)
with subst_t (b:bool)
             (t:type)
             (opto:opt object)
             (x:id) : type :=
match t with
| tUnion lhs rhs => tUnion (subst_t b lhs opto x) (subst_t b rhs opto x)
| tFun y t1 p1 p2 opto2 t2 =>
  if id_eqdec x y
  then t
  else tFun y
            (subst_t b t1 opto x)
            (subst_p b p1 opto x)
            (subst_p b p2 opto x)
            (subst_o opto2 opto x)
            (subst_t b t2 opto x)
| tPair t1 t2 => tPair (subst_t b t1 opto x)
                       (subst_t b t2 opto x)
| _ => t
end.

(** * λTR Core Relations 
   Logic, Typing, Subtyping, etc... *)

Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.
Hint Constructors SubObj.



End LTR.
