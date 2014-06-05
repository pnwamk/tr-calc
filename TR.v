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

Notation var := (obj []).

(** Types and propositions: *)
Inductive type : Type :=
| tTop : type
| tBot : type
| tNum : type
| tTrue : type
| tFalse : type
| tUnion : type -> type -> type
| tPair : type -> type -> type
| tAbs : id -> (type * type) -> (prop * prop) -> opt object -> type

with prop : Type :=
| Is    : object -> type -> prop
| IsNot : object -> type -> prop
| And   : prop -> prop -> prop
| Or    : prop -> prop -> prop
| Imp   : prop -> prop -> prop
| TT    : prop
| FF    : prop.
Hint Constructors type prop.

Hint Resolve eq_nat_dec.

Notation tBool := (tUnion tTrue tFalse).

Infix "::=" := Is (at level 30, right associativity).
Infix "::~" := IsNot (at level 30, right associativity).
Notation "P '&&' Q" := (And P Q). 
Notation "P '||' Q" := (Or P Q).
Notation "P '-->' Q" := (Imp P Q) (at level 90).

(** Expressions and primitive operations: *)
Inductive const_op :=
  opAdd1 | opIsZero | opIsNum | opIsBool | opIsProc | opIsCons.
Hint Constructors const_op.

Inductive poly_op :=
 opCar | opCdr.
Hint Constructors poly_op.

Inductive op : Type :=
| c_op : const_op -> op
| p_op : poly_op -> op.
Hint Constructors op.

Inductive exp : Type :=
| eVar : id -> exp
| eOp  : op -> exp
| eTrue   : exp
| eFalse   : exp
| eNum : nat -> exp
| eIf  : exp -> exp -> exp -> exp
| eλ : id -> type -> exp -> exp
| eApp : exp -> exp -> exp
| eLet : id -> exp -> exp -> exp
| eCons : exp -> exp -> exp.
Hint Constructors exp.

Notation Car' := (eOp (p_op opCar)).
Notation Cdr' := (eOp (p_op opCdr)).
Notation Add1' := (eOp (c_op opAdd1)).
Notation IsZero' := (eOp (c_op opIsZero)).
Notation IsNum' := (eOp (c_op opIsNum)).
Notation IsBool' := (eOp (c_op opIsBool)).
Notation IsProc' := (eOp (c_op opIsProc)).
Notation IsCons' := (eOp (c_op opIsCons)).

(** Constant types: *)
Definition const_type (c : const_op) (x:id) : type :=
  match c with
    | opIsNum =>
      (tAbs x 
            (tTop, tBool) 
            (((var x) ::= tNum), ((var x) ::~ tNum)) 
            (Some (var x)))
    | opIsProc =>
      (tAbs x 
            (tTop, tBool) 
            (((var x) ::= (tAbs x (tBot, tTop) (TT, FF) None)), 
             ((var x) ::~ (tAbs x (tBot, tTop) (TT, FF) None)))
            None)
    | opIsBool =>
      (tAbs x 
            (tTop, tBool) 
            (((var x) ::= tBool), ((var x) ::~ tBool)) 
            None)
    | opIsCons =>
      (tAbs x 
            (tTop, tBool) 
            (((var x) ::= (tPair tTop tTop)), ((var x) ::~ (tPair tTop tTop)))
            None)
    | opAdd1 =>
      (tAbs x 
            (tNum, tNum) 
            (TT, FF)
            None)
    | opIsZero =>
      (tAbs x 
            (tNum, tBool) 
            (TT, TT)
            None)
end.

(** Decidable equality of defined types thus far: *)

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
  decide equality.
  decide equality.
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

(** Free variable calculations: *)
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
    | tAbs x (t1, t2) (p1, p2) o =>
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
    | p && q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p || q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p --> q => set_union id_eqdec (fv_set_p p) (fv_set_p q) 
    | _ => nil
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

Definition truth (b:bool) : prop :=
  match b with
    | true => TT
    | false => FF
  end.

(** _we use true/false instead of +/- for substitution_ *)
Fixpoint subst_p' (b:bool)
         (p:prop)
         (opto:opt object)
         (x:id) : prop :=
  match p with
    | (obj pth1 z) ::= t =>
      match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
        | left _, _ =>
          match opto with
            | None => (truth b)
            | Some (obj pth2 y) =>
              Is (obj (pth1 ++ pth2) y) (subst_t' b t opto x)
          end
        | right _, false => p
        | right _, true => (truth b)
      end
    | (obj pth1 z) ::~ t =>
      match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
        | left _, _ =>
          match opto with
            | None => (truth b)
            | Some (obj pth2 y) =>
              IsNot (obj (pth1 ++ pth2) y) (subst_t' b t opto x)
          end
        | right _, false => p
        | right _, true => (truth b)
      end
    | P --> Q => (subst_p' (negb b) P opto x) --> (subst_p' b Q opto x)
    | P || Q => (subst_p' b P opto x) || (subst_p' b Q opto x)
    | P && Q => (subst_p' b P opto x) && (subst_p' b Q opto x)
    | _ => p
  end

with subst_t' (b:bool)
             (t:type)
             (opto:opt object)
             (x:id) : type :=
  match t with
    | tUnion lhs rhs => tUnion (subst_t' b lhs opto x) (subst_t' b rhs opto x)
    | tAbs y (t1, t2) (p1, p2) opto2 =>
      if id_eqdec x y
      then t
      else tAbs y
                ((subst_t' b t1 opto x),
                 (subst_t' b t2 opto x))
                ((subst_p' b p1 opto x),
                 (subst_p' b p2 opto x))
                (subst_o opto2 opto x)
    | tPair t1 t2 => tPair (subst_t' b t1 opto x)
                           (subst_t' b t2 opto x)
    | _ => t
  end.

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Notation subst_p := (subst_p' true).
Notation subst_t := (subst_t' true).

(** A few helpers to reason about subtyping: *)

Inductive isUnion : type -> Prop :=
| isU : forall t1 t2, isUnion (tUnion t1 t2).

Fixpoint typestructuralsize (t:type) : nat :=
  match t with
    | tUnion t1 t2 =>
      S (plus (typestructuralsize t1) (typestructuralsize t2))
    | tAbs x (t1, t2) _ _ => S (plus (typestructuralsize t1) (typestructuralsize t2))
    | tPair t1 t2 => S (plus (typestructuralsize t1) (typestructuralsize t2))
    | _ => 1
  end.

Program Fixpoint common_subtype (type1 type2:type)
        {measure (plus (typestructuralsize type1) (typestructuralsize type2))} : bool :=
  match type1, type2 with
    | tTop , _ => true
    | _, tTop => true
    | tBot, _ => false
    | _, tBot => false
    | tUnion t1 t2, _ => orb (common_subtype t1 type2) 
                             (common_subtype t2 type2)
    | _, tUnion t1 t2 => orb (common_subtype type1 t1) 
                             (common_subtype type1 t2)
    | tNum, tNum => true
    | tNum, _ => false
    | tTrue, tTrue => true
    | tTrue, _ => false
    | tFalse, tFalse => true
    | tFalse, _ => false
    | tAbs _ _ _ _, tAbs _ _ _ _ => true
    | tAbs _ _ _ _, _ => false
    | tPair t1 t2, tPair t3 t4 => andb (common_subtype t1 t3)
                                       (common_subtype t2 t4)
    | tPair _ _, _ => false
  end.
Solve Obligations using crush.

(*
TODO - We must prove all types have a principal type
if we're going to use this for Removed *)

(* NOTE: Our lookup models an environment where every variable in scope
has some type present (even if its only tTop). *)

(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** ** Proves Relation *)
(** "Proves P Q" means proposition "P implies Q" is tautilogical. *)

Inductive Proves : relation prop :=
| P_Refl : (* AKA P_Atom *)
    forall P,
      Proves P P
| P_False :
    forall P,
      Proves FF P
| P_True :
    forall P,
      Proves P TT
| P_AndI :
    forall P Q R,
      Proves P Q 
      -> Proves P R 
      -> Proves P (Q && R)
| P_AndE_lhs :
    forall P Q R,
      Proves P R 
      -> Proves (P && Q) R
| P_AndE_rhs :
    forall P Q R,
      Proves Q R
      -> Proves (P && Q) R
| P_ImpI :
    forall P Q R,
      Proves (P && Q) R
      -> Proves P (Q --> R)
| P_ImpE :
    forall P Q R,
      Proves P Q 
      -> Proves P (Q --> R)
      -> Proves P R
| P_OrI_lhs :
    forall P Q R,
      Proves P Q
      -> Proves P (Q || R)
| P_OrI_rhs :
    forall P Q R,
      Proves P R
      -> Proves P (Q || R)
| P_OrE :
    forall P Q R Y,
      Proves (P && Q) Y
      -> Proves (P && R) Y
      -> Proves (P && (Q || R)) Y
| P_Or :
    forall P Q R,
      Proves P R
      -> Proves Q R
      -> Proves (P || Q) R
| P_Sub :
    forall P τ σ ox,
      Proves P (ox ::= τ)
      -> SubType τ σ
      -> Proves P (ox ::= σ)
| P_SubNot :
    forall P τ σ ox,
      Proves P (ox ::~ σ)
      -> SubType τ σ
      -> Proves P (ox ::~ τ)
| P_Bot : 
    forall P Q ox,
      Proves P (ox ::= tBot) 
      -> Proves P Q
| P_Update_Is :
    forall P τ σ π π' x updated,
      Proves P ((obj π' x) ::= τ) 
      -> Proves P ((obj (π ++ π') x) ::= σ) 
      -> Update τ (true, σ) π updated
      -> Proves P ((obj π' x) ::= updated)
| P_Update_IsNot :
    forall P τ σ π π' x updated,
      Proves P ((obj π' x) ::= τ) 
      -> Proves P ((obj (π ++ π') x) ::~ σ) 
      -> Update τ (false, σ) π updated
      -> Proves P ((obj π' x) ::= updated)

(** ** Update *)

with Update : type -> (bool * type) -> path -> type -> Prop :=
| UP_Car :
    forall τ ν π σ updated,
      Update τ ν π updated 
      -> Update (tPair τ σ) ν (π ++ [car]) (tPair updated σ)
| UP_Cdr :
    forall τ ν π updated σ,
      Update σ ν π updated
      -> Update (tPair τ σ) ν (π ++ [cdr]) (tPair τ updated)
| UP_Is :
    forall τ σ restricted,
      Restrict τ σ restricted 
      -> Update τ (true, σ) [] restricted
| UP_IsNot :
    forall τ σ r,
      Remove τ σ r
      -> Update τ (false, σ) [] r

(** ** Restrict *)

with Restrict : type -> type -> type -> Prop :=
     | RES_NoCommon :
         forall τ σ,
           common_subtype τ σ = false 
           -> Restrict τ σ tBot
     | RES_Lhs :
         forall τ σ,
           common_subtype τ σ = true
           -> Restrict τ σ τ
     | RES_Rhs :
         forall τ σ,
           common_subtype τ σ = true
           -> Restrict τ σ σ
     | RES_U :
         forall τ1 τ2 σ τ1' τ2',
           common_subtype (tUnion τ1 τ2) σ = true
           -> Restrict τ1 σ τ1' 
           -> Restrict τ2 σ τ2' 
           -> Restrict (tUnion τ1 τ2) σ (tUnion τ1' τ2')

(** ** Remove *)

with Remove : type -> type -> type -> Prop :=
     | REM_Bottom_l :
         forall σ,
           Remove tBot σ tBot
     | REM_Bottom_r :
         forall t,
           Remove t tBot t
     | REM_Union_lhs :
         forall t1 t1' t2 σ,
           Remove t1 σ t1'
           -> Remove (tUnion t1 t2) σ (tUnion t1' t2)
     | REM_Union_rhs :
         forall t1 t2 t2' σ,
           Remove t2 σ t2'
           -> Remove (tUnion t1 t2) σ (tUnion t1 t2')
     | REM_Sub :
         forall t σ,
           SubType t σ 
           -> Remove t σ tBot

with SubType : relation type :=
| S_Refl : 
    forall τ, SubType τ τ
| S_Top : 
    forall τ, SubType τ tTop
| S_UnionSuper_l :
    forall τ σ1 σ2,
      SubType τ σ1
      -> SubType τ (tUnion σ1 σ2)
| S_UnionSuper_r :
    forall τ σ1 σ2,
      SubType τ σ2
      -> SubType τ (tUnion σ1 σ2)
| S_UnionSub :
    forall τ1 τ2 σ,
      SubType τ1 σ
      -> SubType τ2 σ
      -> SubType (tUnion τ1 τ2) σ
| S_UnionBot_lhs :
    forall τ σ,
      SubType τ σ
      -> SubType (tUnion tBot τ) σ
| S_UnionBot_rhs :
    forall τ σ,
      SubType τ σ
      -> SubType (tUnion τ tBot) σ
| S_Abs :
    forall x y τ τ' σ σ' tP tP' fP fP' o o',
      SubType (subst_t τ (Some (var y)) x) τ'
      -> SubType σ' (subst_t σ (Some (var y)) x) 
      -> Proves (subst_p tP (Some (var y)) x) tP'
      -> Proves (subst_p fP (Some (var y)) x) fP'
      -> SubObj (subst_o o (Some (var y)) x) o'
      -> SubType (tAbs x (σ, τ) (tP, fP) o)
                 (tAbs y (σ', τ') (tP', fP') o')
| S_Pair :
    forall τ1 σ1 τ2 σ2,
      SubType τ1 τ2
      -> SubType σ1 σ2
      -> SubType (tPair τ1 σ1) (tPair τ2 σ2).


(** ** TypeOf *)

Inductive TypeOf : prop -> exp -> type -> (prop * prop) -> opt object -> Prop :=
| T_Num :
    forall Γ n,
      TypeOf Γ (eNum n) tNum (TT, FF) None
| T_Const :
    forall τ Γ c x,
      τ = (const_type c x)
      -> TypeOf Γ (eOp (c_op c)) τ (TT, FF) None
| T_True :
    forall Γ,
      TypeOf Γ eTrue tTrue (TT, FF) None
| T_False :
    forall Γ,
      TypeOf Γ eFalse tFalse (FF, TT) None
| T_Var :
    forall τ Γ x,
      Proves Γ ((var x) ::= τ)
      -> TypeOf Γ (eVar x) τ (((var x) ::~ tFalse), ((var x) ::= tFalse)) (Some (var x))
| T_Abs :
    forall σ τ o Γ x tP fP e,
      TypeOf (Γ && ((var x) ::= σ)) e τ (tP, fP) o
      -> TypeOf Γ 
                (eλ x σ e) 
                (tAbs x (σ, τ) (tP, fP) o) 
                (TT, FF) 
                None
| T_App :
    forall τ'' σ τ o'' o o' Γ e x tPf fPf of tP fP e' tP' fP' tPf'' fPf'',
      TypeOf Γ e (tAbs x (σ, τ) (tPf, fPf) of) (tP, fP) o
      -> TypeOf Γ e' σ (tP', fP') o'
      -> (subst_t τ o' x) = τ''
      -> (subst_p tPf o' x) = tPf''
      -> (subst_p fPf o' x) = fPf''
      -> (subst_o of o' x) = o''
      -> TypeOf Γ (eApp e e') τ'' (tPf'', fPf'') o''
| T_If :
    forall τ τ' o o1 Γ e1 tP1 fP1 e2 tP2 fP2 e3 tP3 fP3,
      TypeOf Γ e1 τ' (tP1, fP1) o1
      -> TypeOf (Γ && tP1) e2 τ (tP2, fP2) o
      -> TypeOf (Γ && fP1) e3 τ (tP3, fP3) o
      -> TypeOf Γ (eIf e1 e2 e3) τ ((tP2 || tP3), (fP2 || fP3)) o
| T_Cons :
    forall τ1 τ2 o1 o2 Γ e1 tP1 fP1 e2 tP2 fP2,
      TypeOf Γ e1 τ1 (tP1, fP1) o1
      -> TypeOf Γ e2 τ2 (tP2, fP2) o2
      -> TypeOf Γ (eCons e1 e2) (tPair τ1 τ2) (TT, FF) None
| T_Car :
    forall τ1 τ2 o' o Γ e tP0 fP0 tP fP x,
      TypeOf Γ e (tPair τ1 τ2) (tP0, fP0) o
      -> (subst_p ((obj [car] x) ::~ tFalse) o x) = tP
      -> (subst_p ((obj [car] x) ::= tFalse) o x) = fP
      -> (subst_o (Some (obj [car] x)) o x) = o'
      -> TypeOf Γ (eApp Car' e) τ1 (tP, fP) o'
| T_Cdr :
    forall τ1 τ2 o' o Γ e tP0 fP0 tP fP x,
      TypeOf Γ e (tPair τ1 τ2) (tP0, fP0) o
      -> (subst_p ((obj [cdr] x) ::~ tFalse) o x) = tP
      -> (subst_p ((obj [cdr] x) ::= tFalse) o x) = fP
      -> (subst_o (Some (obj [cdr] x)) o x) = o'
      -> TypeOf Γ (eApp Cdr' e) τ2 (tP, fP) o'
| T_Let :
    forall σ' τ σ o1' o0 o1 Γ e0 tP0 fP0 e1 tP1 fP1 x tP1' fP1',
      TypeOf Γ e0 τ (tP0, fP0) o0
      -> TypeOf (Γ && ((var x) ::= τ)
                   && (((var x) ::~ tFalse) --> tP0)
                   && (((var x) ::= tFalse) --> fP0)) 
                e1
                σ
                (tP1, fP1)
                o1
      -> (subst_t σ o0 x) = σ'
      -> (subst_p tP1 o0 x) = tP1'
      -> (subst_p fP1 o0 x) = fP1'
      -> (subst_o o1 o0 x) = o1'
      -> TypeOf Γ (eLet x e0 e1) σ' (tP1', fP1') o1'
| T_Subsume :
    forall τ' τ o' o Γ e tP fP tP' fP',
      TypeOf Γ e τ (tP, fP) o
      -> Proves (Γ && tP) tP'
      -> Proves (Γ && fP) fP'
      -> SubType τ τ'
      -> SubObj o o'
      -> TypeOf Γ e τ' (tP', fP') o'.

(** * Proof Helpers/Lemmas and Automation *)
Lemma then_else_eq : forall (T:Type) (P1 P2:Prop) (test: sumbool P1 P2) (Q:T),
(if test then Q else Q) = Q.
Proof.
  crush.
Qed.
Hint Rewrite then_else_eq.


Lemma if_eq_id : forall (T:Type) x (t1 t2: T),
(if id_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (id_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_id.

Lemma if_eq_obj : forall (T:Type) x (t1 t2: T),
(if obj_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (obj_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_obj.

Lemma neq_id_neq : forall (T:Type) x y (P Q:T),
x <> y ->
((if (id_eqdec x y) then P else Q) = Q).
Proof.
  intros.
  destruct (id_eqdec x y); crush.
Qed.

Lemma neq_obj_neq : forall (T:Type) x y (P Q:T) pth1 pth2,
x <> y ->
((if (obj_eqdec (obj pth1 x) (obj pth2 y)) then P else Q) = Q).
Proof.
  intros.
  destruct (obj_eqdec (obj pth1 x) (obj pth2 y)); crush.
Qed.

Lemma if_eq_type : forall (T:Type) x (t1 t2: T),
(if type_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (type_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_type.

Lemma subst_Some_tNum : forall x y,
(subst_p (var x ::= tNum) (Some (var y)) x)
 = (var y ::= tNum).
Proof.
  intros x y.
  simpl. destruct (id_eqdec x x); crush.
Qed.  
Hint Rewrite subst_Some_tNum.
  
Hint Constructors TypeOf Update.

Ltac tryT :=
  first [(eapply T_Const) |
        (eapply T_Num) |
        (eapply T_True) |
        (eapply T_False) |
        (eapply T_Var) |
        (eapply T_Abs) |
        (eapply T_If) |
        (eapply T_Cons) |
        (eapply T_Car) |
        (eapply T_Cdr) |
        (eapply T_App) |
        (eapply T_Abs) |
        (eapply T_Let) |
        (eapply T_If)  |
        (eapply T_Subsume)].

Ltac tryS :=
  first [(eapply S_Refl) |
        (eapply S_Top) |
        (eapply S_UnionSub) |
        (eapply S_Abs) |
        (eapply S_Pair) |
        (match goal with
         | |- SubType ?t1 (tUnion ?t1 ?t2) =>
           eapply S_UnionSuper_l
         | |- SubType ?t2 (tUnion ?t1 ?t2) =>
           eapply S_UnionSuper_r
         | |- SubType ?t1 (tUnion (tUnion ?t1 ?t2) ?t3) =>
           eapply S_UnionSuper_l; eapply S_UnionSuper_l
         | |- SubType ?t2 (tUnion (tUnion ?t1 ?t2) ?t3) =>
           eapply S_UnionSuper_l; eapply S_UnionSuper_r
         | |- SubType ?t2 (tUnion ?t1 (tUnion ?t2 ?t3)) =>
           eapply S_UnionSuper_r; eapply S_UnionSuper_l
         | |- SubType ?t3 (tUnion ?t1 (tUnion ?t2 ?t3)) =>
           eapply S_UnionSuper_r; eapply S_UnionSuper_r
        end) |
        (eapply S_Refl)].

Ltac tryP :=
  match goal with
  | |- Proves FF _ =>
    solve [eapply P_False]
  | |- Proves _ TT =>
    solve [eapply P_True]
  | |- Proves (?o1 ::= ?τ1) (?o1 ::~ ?τ1)  => 
    eapply P_Update_IsNot
  | |- Proves ?p1 ?p1 => 
    solve [eapply P_Refl]
  | |- Proves ?p1 (?p2 && ?p3) =>
    solve [(eapply P_AndI; tryP)]
  | |- Proves ?p1 (?p2 || ?p3) =>
    solve [first [(eapply P_OrI_lhs; tryP) | (eapply P_OrI_rhs; tryP)]]
  | |- Proves (?p1 && ?p2) ?p3 => 
    solve [first [(eapply P_AndE_lhs; tryP) | (eapply P_AndE_rhs; tryP)]]
  | |- Proves (?p1 || ?p2) ?p3 => 
    solve [eapply P_Or; tryP]
  | |- Proves (?o1 ::= ?τ1) (?o2 ::= ?τ1) =>
    solve [eapply P_Refl]
  | |- Proves (?o1 ::= ?τ1) (?o1 ::= ?τ2) =>
    solve [eapply P_Sub; (tryS; crush); tryP]
  | |- Proves (?o1 ::= (tUnion ?τ1 ?τ2)) (?o1 ::= ?τ2) =>
    solve [eapply P_Sub; (tryS; crush); tryP]
(*  | |- Proves (?o1 ::= (tUnion ?τ1 ?τ2) (?o1 ::~ ?τ1) =>
    solve [eapply P_Sub; (tryS; crush); tryP] *)

  end.
(* tryP currently will just do a recursive logical fact check, it does not
   yet reason about implication or subtyping *)

Ltac trySO :=
  match goal with
    | |- SubObj None ?o => eapply SO_Refl
    | |- SubObj ?o None => eapply SO_Top
  end.



Ltac crushTR :=
  repeat 
    (try simpl; 
       (repeat 
          (((erewrite if_eq_id)
              || (erewrite if_eq_obj)
              || (erewrite if_eq_type)
              || tryT
              || tryS
              || tryP
              || trySO
              || auto
              || eauto
              || crush)))).

Lemma union_not_lhs : forall τ1 τ2 Γ o,
Proves Γ (o ::= (tUnion τ1 τ2))
-> Proves Γ (o ::~ τ1)
-> Proves Γ (o ::= τ2).
Proof with crushTR.
  intros τ1 τ2 Γ [π x] H1 H2.
  eapply P_Sub.
  forwards: (@P_Update_IsNot 
                Γ
                (tUnion τ1 τ2) 
                τ1 [] π x)...
  eapply UP_IsNot.
  eapply REM_Union_lhs.
  eapply REM_Sub... 
  eapply  S_UnionBot_lhs...
Qed.

Lemma union_not_rhs : forall τ1 τ2 Γ o,
Proves Γ (o ::= (tUnion τ1 τ2))
-> Proves Γ (o ::~ τ2)
-> Proves Γ (o ::= τ1).
Proof with crushTR.
  intros τ1 τ2 Γ [π x]  H1 H2.
  eapply P_Sub.
  forwards: (@P_Update_IsNot 
                Γ
                (tUnion τ1 τ2) 
                τ2 [] π x)...
  eapply UP_IsNot.
  eapply REM_Union_rhs.
  eapply REM_Sub... 
  eapply S_UnionBot_rhs...
Qed.

Lemma proves_top : forall x τ,
Proves (x ::=τ) (x ::= tTop).
Proof.
  intros x t.
  eapply P_Sub.
  eapply P_Refl.
  eapply S_Top.
Qed.  
Hint Resolve proves_top.

Lemma remove_TT_lhs : forall P Q,
Proves P Q ->
Proves (TT && P) Q.
Proof.
  intros P Q H.
  eapply P_AndE_rhs; eauto.
Qed.  
Hint Resolve remove_TT_lhs.

(** * Example TypeOf Judgements *)

Example example1:
  forall x,
    TypeOf ((var x) ::= tTop)
           (eIf (eApp IsNum' (eVar x))
                (eApp Add1' (eVar x))
                (eNum 0))
           tNum
           (TT,TT)
           None.
Proof with crushTR.
  intros x...
Grab Existential Variables.
crush. crush.
Qed.

Hint Resolve P_Sub P_True.

Example example2a:
  forall x,
    TypeOf
      ((var x) ::= (tUnion tBool tNum))
      (eIf (eApp IsBool' (eVar x))
           eFalse
           (eApp IsZero' (eVar x)))
      tBool
      (TT,TT)
      None.
Proof with crushTR.
  intros x.
  eapply T_Subsume.
  eapply (T_If tBool)...
  eapply (union_not_lhs tBool tNum)...
  crushTR. crushTR. crushTR. crushTR.
Grab Existential Variables.
crush. crush. crush.
Qed.

Example example2b:
  forall x,
    TypeOf
      TT
      (eλ x (tUnion tBool tNum)
            (eIf (eApp IsBool' (eVar x))
                   eFalse
                   (eApp IsZero' (eVar x))))
      (tAbs x 
            ((tUnion tBool tNum), tBool) 
            (TT, TT) 
            None)
      (TT,TT)
      None.
Proof with crushTR. 
  intros x.
  eapply T_Subsume.
  eapply (T_Abs (tUnion tBool tNum) tBool)...
  eapply (union_not_lhs tBool tNum)...
  crushTR. crushTR. crushTR. crushTR.
Grab Existential Variables.
crush. crush. crush.
Qed.
  
Example example3:
  forall x y,
    x <> y ->
    TypeOf
      ((var y) ::= tTop)
      (eLet x (eApp IsNum' (eVar y))
              (eIf (eVar x)
                     (eVar y)
                     (eNum 0)))
      tNum
      (TT,TT)
      None.
Proof with crushTR. 
  intros x y Hneq.
  eapply T_Subsume.
  eapply T_Let.
  eapply T_App.
  eapply T_Const.
  reflexivity.
  eapply T_Var...
  eauto. eauto. eauto. eauto.
  eapply T_If.
  eapply T_Var...
  eapply P_AndE_lhs. eapply P_AndE_lhs.
  eapply P_AndE_rhs...
  eapply T_Subsume...
  eapply P_ImpE. eapply P_AndE_rhs. eapply P_Refl.
  eapply P_AndE_lhs. eapply P_AndE_lhs.
  eapply P_AndE_rhs... eapply P_Refl.
  eapply SO_Top...
  eapply T_Num...
  eauto. eauto. eauto. eauto.
  crushTR. crushTR. crushTR. crushTR.
Grab Existential Variables.
crush.
Qed.


Definition eAnd' (e1 e2 : exp) : exp :=
(eIf e1 e2 eFalse).

Definition eOr' (e1 e2 : exp) : exp :=
(eIf e1 e1 e2).


Example example4:
  forall x,
    TypeOf (((var x) ::= tTop))
           (eIf (eOr' (eApp IsNum' (eVar x)) 
                      (eApp IsBool' (eVar x)))
                (eApp 
                   (eλ x (tUnion tBool tNum)
                       (eIf (eApp IsBool' (eVar x))
                            eFalse
                            (eApp IsZero' (eVar x))))
                   (eVar x))
                eFalse)
           tBool
           (TT,TT)
           None.
Proof with crushTR.
  intros x.
  eapply (T_Subsume tBool tBool).
  eapply (T_If tBool tBool).
  eapply (T_If tBool tBool).
  eapply T_App.
  eapply T_Const...
  eapply T_Subsume.
  eapply T_Var...
  crushTR. crushTR. crushTR. eapply SO_Top. crushTR.
  crushTR. crushTR. crushTR.
  eapply T_Subsume.
  eapply T_App... eapply P_Refl. eapply P_Refl. 
  crushTR. eapply SO_Top. crushTR.
  eapply T_Subsume.
  eapply T_App.
  eapply (T_Abs (tUnion tBool tNum) tBool)...
  eapply (union_not_lhs tBool tNum)...
  crushTR. 
  eapply P_AndE_rhs. 
  eapply P_Or.
    eapply P_Sub. eapply P_AndE_rhs. eapply P_Refl. crushTR.
    eapply P_Sub. eapply P_Refl. crushTR.

  crushTR. crushTR. crushTR. crushTR.
  eapply P_Refl. eapply P_Refl. crushTR. eapply SO_Top.
  crushTR. crushTR. crushTR. crushTR. crushTR.
Grab Existential Variables.
crush. crush. crush. crush. crush. crush. crush.
Qed.



Example example10:
  forall p,
    TypeOf (((var p) ::= (tPair tTop tTop)))
           (eIf (eApp IsNum' (eApp Car' (eVar p)))
                (eApp Add1' (eApp Car' (eVar p)))
                (eNum 42))
           tNum
           (TT,TT)
           None.
Proof with crushTR.
  intros p...
  eapply P_Refl.
  eapply P_Update_Is.
  eapply P_AndE_lhs. eapply P_Refl.
  eapply P_AndE_rhs. rewrite <- (app_nil_r [car]). 
  eapply P_Refl.
  rewrite <- (app_nil_l [car]).
  eapply UP_Car.
  eapply UP_Is.
  eapply RES_Rhs...
Grab Existential Variables.
crush. crush. crush. crush.
Qed.
  
Example example10':
  forall p,
    TypeOf (((var p) ::= (tPair tTop tTop)))
           (eIf (eApp IsNum' (eApp Cdr' (eVar p)))
                (eApp Add1' (eApp Cdr' (eVar p)))
                (eNum 42))
           tNum
           (TT,TT)
           None.
Proof with crushTR.
  intros p...
  eapply P_Refl.
  eapply P_Update_Is.
  eapply P_AndE_lhs. eapply P_Refl.
  eapply P_AndE_rhs. rewrite <- (app_nil_r [cdr]). 
  eapply P_Refl.
  rewrite <- (app_nil_l [cdr]).
  eapply UP_Cdr.
  eapply UP_Is.
  eapply RES_Rhs...
Grab Existential Variables.
crush. crush. crush. crush.
Qed.

(** * λTR Values & Big Step Semantics *)
(** ** Values *)
Inductive value : Type :=
| vPrim  : op -> value
| vTrue  : value
| vFalse : value
| vNum   : nat -> value
| vλ     : (object -> opt value) -> id -> type -> exp -> value
| vCons  : value -> value -> value.

Inductive IsClosure : value -> Prop :=
| isclos : forall ρ x τ e,
             IsClosure (vλ ρ x τ e).

Definition env := object -> opt value.
Definition extend (ρ:env) (o: object) (v:value) :=
fun x =>
  if (obj_eqdec o x) 
  then Some v
  else (ρ x).

Definition δ (o:op) (v:value) : opt value :=
  match o, v with
    | c_op opAdd1, vNum n => Some (vNum (n + 1))
    | c_op opAdd1, _ => None
    | c_op opIsZero, vNum 0 => Some vTrue
    | c_op opIsZero, vNum (S n) => Some vFalse
    | c_op opIsZero, _ => None
    | c_op opIsNum, vNum _ => Some vTrue
    | c_op opIsNum, _ => Some vFalse
    | c_op opIsBool, vTrue => Some vTrue
    | c_op opIsBool, vFalse => Some vTrue
    | c_op opIsBool, _ => Some vFalse
    | c_op opIsProc, vλ _ _ _ _ => Some vTrue
    | c_op opIsProc, _ => Some vFalse
    | c_op opIsCons, vCons _ _ => Some vTrue
    | c_op opIsCons, _ => Some vFalse
    | p_op opCar, vCons v1 _ => Some v1
    | p_op opCar, _ => None
    | p_op opCdr, vCons _ v2 => Some v2
    | p_op opCdr, _ => None
  end.

(** ** Big-Step Semantics *)
Reserved Notation "ρ |- e ==>* v" (at level 50, left associativity).

Inductive BStep : env -> exp -> value -> Prop :=
| B_Var : 
    forall ρ x v,
      (ρ (var x)) = Some v
      -> ρ |- (eVar x) ==>* v
| B_Op : 
    forall ρ e c e' v v',
      ρ |- e ==>* (vPrim c)
      -> ρ |- e' ==>* v
      -> (δ c v) = Some v'
      -> ρ |- (eApp e e') ==>* v'
| B_True :
    forall ρ,
      ρ |- eTrue ==>* vTrue
| B_False :
    forall ρ,
      ρ |- eFalse ==>* vFalse
| B_Num :
    forall ρ n,
      ρ |- (eNum n) ==>* (vNum n)
| B_Let :
    forall ρ e1 e2 v1 v2 x,
      ρ |- e1 ==>* v1
      -> (extend ρ (var x) v1) |- e2 ==>* v2
      -> ρ |- (eLet x e1 e2) ==>* v2
| B_Abs :
    forall x τ e ρ,
       ρ |- (eλ x τ e) ==>* (vλ ρ x τ e)
| B_Beta :
    forall ef ρ' x τ eb ea va ρ v,
      ρ |- ef ==>* (vλ ρ' x τ eb)
      -> ρ |- ea ==>* va
      -> (extend ρ' (var x) va) |- eb ==>* v
      -> ρ |- (eApp ef ea) ==>* v
| B_Cons :
    forall ρ e1 e2 v1 v2,
      ρ |- e1 ==>* v1
      -> ρ |- e2 ==>* v2
      -> ρ |- (eCons e1 e2) ==>* (vCons v1 v2)
| B_IfTrue :
    forall ρ e1 v1 e2 v e3,
      ρ |- e1 ==>* v1
      -> v1 <> vFalse
      -> ρ |- e2 ==>* v
      -> ρ |- (eIf e1 e2 e3) ==>* v
| B_IfFalse :
    forall ρ e1 e2 v e3,
      ρ |- e1 ==>* vFalse
      -> ρ |- e3 ==>* v
      -> ρ |- (eIf e1 e2 e3) ==>* v

where "ρ |- e ==>* v" := (BStep ρ e v).


Reserved Notation "ρ |= q " (at level 50, left associativity).

(** ** Satisfaction Relation *)
Inductive Satisfies : env -> prop -> Prop :=
| M_Or_lhs :
    forall ρ P Q,
      ρ |= P
      -> ρ |= (P || Q)
| M_Or_rhs :
    forall ρ P Q,
      ρ |= Q
      -> ρ |= (P || Q)
(* | M_Imp ??? *)
| M_And :
    forall ρ P Q,
      ρ |= P
      -> ρ |= Q
      -> ρ |= (P && Q)
| M_Top :
    forall ρ,
      ρ |= TT
| M_Type_Prim : 
    forall c ρ π x y τ,
      (ρ (obj π x)) = Some (vPrim (c_op c))
      -> τ = (const_type c y)
      -> ρ |= ((obj π x) ::= τ)
| M_Type_True :
    forall ρ π x,
      (ρ (obj π x)) = Some vTrue
      -> ρ |= ((obj π x) ::= tTrue)
| M_Type_False :
    forall ρ π x,
      (ρ (obj π x)) = Some vFalse
      -> ρ |= ((obj π x) ::= tFalse)
| M_Type_Num :
    forall ρ π x n,
      (ρ (obj π x)) = Some (vNum n)
      -> ρ |= ((obj π x) ::= tNum)
| M_Type_Closure : 
    forall ρ π x τ σ e o Γ ρ' tP fP tPf fPf of,
      (ρ (obj π x)) = Some (vλ ρ' x σ e)
      -> ρ' |= Γ
      -> TypeOf Γ (eλ x σ e) (tAbs x (σ, τ) (tPf, fPf) of) (tP, fP) o
      -> ρ |= ((obj π x) ::= (tAbs x (σ, τ) (tPf, fPf) of))
| M_Type_Cons :
    forall v1 v2 ρ π x τ1 τ2,
      (ρ (obj π x)) = Some (vCons v1 v2)
      -> ρ |= ((obj (π ++ [car]) x) ::= τ1)
      -> ρ |= ((obj (π ++ [cdr]) x) ::= τ2)
      -> ρ |= ((obj π x) ::= (tPair τ1 τ2))

where "ρ |= q" := (Satisfies ρ q).


End LTR.

        