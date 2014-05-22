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
Infix "&" := And (at level 40, left associativity).
Infix "+" := Or (at level 50, left associativity).
Infix "=->" := Imp (at level 90, right associativity).

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
            None)
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
    | p & q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p + q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p =-> q => set_union id_eqdec (fv_set_p p) (fv_set_p q) 
    | _ => nil
  end.

(** Substitution functions: *)
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
              Is (obj (pth1 ++ pth2) y) (subst_t' b t opto x)
          end
        | right _, false => p
        | right _, true => (truth b)
      end
    | P =-> Q => (subst_p' (negb b) P opto x) =-> (subst_p' b Q opto x)
    | P + Q => (subst_p' b P opto x) + (subst_p' b Q opto x)
    | P & Q => (subst_p' b P opto x) & (subst_p' b Q opto x)
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

Program Fixpoint possible_subtype (pos_sub pos_super:type)
        {measure (plus (typestructuralsize pos_sub) (typestructuralsize pos_super))} : bool :=
  match pos_sub, pos_super with
    | _, tUnion t1 t2 =>
      orb (possible_subtype pos_sub t1)
          (possible_subtype pos_sub t2)
    | tTop , tTop => true
    | tTop , _ => false
    | tBot , tBot => true
    | tBot , _ => false
    | tNum , tNum => true
    | tNum , _ => false
    | tTrue , tTrue => true
    | tTrue , _ => false
    | tFalse , tFalse => true
    | tFalse , _ => false
    | tUnion t1 t2, _ =>
      andb (possible_subtype t1 pos_super)
           (possible_subtype t2 pos_super)
    | tAbs _ (t1,t2) _ _, tAbs _ (t3, t4) _ _ =>
      andb (possible_subtype t1 t3)
           (possible_subtype t2 t4)
    | tAbs _ _ _ _, _ => false
    | tPair t1 t2, tPair t3 t4 =>
      andb (possible_subtype t1 t3)
           (possible_subtype t2 t4)
    | tPair _ _, _ => false
  end.
Solve Obligations using crush.

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
      -> Proves P (Q & R)
| P_AndE_lhs :
    forall P Q R,
      Proves P R 
      -> Proves (P & Q) R
| P_AndE_rhs :
    forall P Q R,
      Proves Q R
      -> Proves (P & Q) R
| P_ImpI :
    forall P Q R,
      Proves (P & Q) R
      -> Proves P (Q =-> R)
| P_ImpE :
    forall P Q R,
      Proves P Q 
      -> Proves P (Q =-> R)
      -> Proves P R
| P_OrI_lhs :
    forall P Q R,
      Proves P Q
      -> Proves P (Q + R)
| P_OrI_rhs :
    forall P Q R,
      Proves P R
      -> Proves P (Q + R)
| P_OrE :
    forall P Q R Y,
      Proves (P & Q) Y
      -> Proves (P & R) Y
      -> Proves (P & (Q + R)) Y
| P_Or :
    forall P Q R,
      Proves P R
      -> Proves Q R
      -> Proves (P + Q) R
| P_Sub :
    forall P τ σ ox,
      Proves P (ox ::= τ)
      -> Subtype τ σ
      -> Proves P (ox ::= σ)
| P_SubNot :
    forall P τ σ ox,
      Proves P (ox ::~ σ)
      -> Subtype τ σ
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
    forall τ ν pth updated σ, (* BOOKMARK *)
      Update σ ν pth updated
      -> Update (tPair τ σ) ν (pth ++ [car]) (tPair updated σ)
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
     | RES_Bottom_l :
         forall σ,
           Restrict tBot σ tBot
     | RES_Bottom_r :
         forall σ,
           Restrict σ tBot tBot
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
     | REM_Union :
         forall t1 t2 t1' t2' σ,
           Remove t1 σ t1' 
           -> Remove t2 σ t2' 
           -> Remove (tUnion t1 t2) σ (tUnion t1' t2')
     | REM_Sub :
         forall t σ,
           Subtype t σ 
           -> Remove t σ tBot

(* TODO *)
(** ** TypeOf *)

with TypeOf : prop -> exp -> type -> (prop * prop) -> opt object -> Prop :=
| T_Num :
    forall τ' Γ tP' fP' o' n,
      Subtype tNum τ'
      -> Proves TT tP'
      -> Proves FF fP'
      -> SubObj None o'
      -> TypeOf Γ (eNum n) τ' (tP', fP') o'
| T_Const :
    forall τ' Γ c x tP' fP' o',
      Proves (Γ & TT) tP'
      -> Proves (Γ & FF) fP'
      -> Subtype (const_type c x) τ'
      -> SubObj None o'
      -> TypeOf Γ (eOp (c_op c)) τ' (tP', fP') o'
| T_True :
    forall τ' Γ tP' fP' o',
      Subtype tTrue τ'
      -> Proves TT tP'
      -> Proves FF fP'
      -> SubObj None o'
      -> TypeOf Γ eTrue τ' (tP', fP') o'
| T_False :
    forall τ' Γ tP' fP' o',
      Subtype tFalse τ'
      -> Proves FF tP'
      -> Proves TT fP'
      -> SubObj None o'
      -> TypeOf Γ eFalse τ' (tP', fP') o'
| T_Var :
    forall τ' τ Γ tP' fP' ox ox' x,
      Proves Γ (ox ::= τ)
      -> Subtype τ τ'
      -> Proves (ox ::~ tFalse) tP'
      -> Proves (ox ::= tFalse) fP'
      -> SubObj (Some ox) ox'
      -> TypeOf Γ (eVar x) τ' (tP', fP') ox'
| T_Abs :
    forall σ' τ' σ τ Γ x e tP fP o tP' fP' o' tP'' fP'' o'',
      TypeOf (Γ & ((var x) ::= σ)) e τ (tP, fP) o
      -> Subtype τ τ'
      -> Subtype σ' σ
      -> SubObj o o'
      -> Proves tP tP'
      -> Proves fP fP'
      -> SubObj None o''
      -> Proves TT tP''
      -> Proves FF fP''
      -> TypeOf Γ 
                (eλ x σ e) 
                (tAbs x (σ', τ') (tP', fP') o') 
                (tP'', fP'') 
                o''
| T_App :
    forall τ'' σ τ σ' Γ e x tPf fPf of tP fP o e' tP' fP' o' tPf'' fPf'' o'',
      TypeOf Γ e (tAbs x (σ, τ) (tPf, fPf) of) (tP, fP) o
      -> TypeOf Γ e' σ' (tP', fP') o'
      -> Subtype σ' σ
      -> Subtype (subst_t τ o' x) τ''
      -> Proves (subst_p tPf o' x) tPf''
      -> Proves (subst_p fPf o' x) fPf''
      -> SubObj (subst_o of o' x) o''
      -> TypeOf Γ (eApp e e') τ'' (tPf'', fPf'') o''
| T_If :
    forall τ' τ1 τ2 τ3 Γ e1 tP1 fP1 o1 e2 tP2 fP2 o e3 tP3 fP3 o' tP' fP',
      TypeOf Γ e1 τ1 (tP1, fP1) o1
      -> TypeOf (Γ & tP1) e2 τ2 (tP2, fP2) o
      -> TypeOf (Γ & fP1) e3 τ3 (tP3, fP3) o
      -> Proves (tP2 + tP3) tP'
      -> Proves (fP2 + fP3) fP'
      -> Subtype (tUnion τ2 τ3) τ'
      -> SubObj o o'
      -> TypeOf Γ (eIf e1 e2 e3) τ' (tP', fP') o'
| T_Cons :
    forall τ' τ1 τ2 Γ e1 tP1 fP1 o1 e2 tP2 fP2 o2 o' fP' tP',
      TypeOf Γ e1 τ1 (tP1, fP1) o1
      -> TypeOf Γ e2 τ2 (tP2, fP2) o2
      -> Subtype (tPair τ1 τ2) τ'
      -> Proves TT tP'
      -> Proves FF fP'
      -> SubObj None o'
      -> TypeOf Γ (eCons e1 e2) τ' (tP', fP') o'
| T_Car :
    forall τ1 τ2 Γ e tP0 fP0 o o' tP fP x,
      TypeOf Γ e (tPair τ1 τ2) (tP0, fP0) o
      -> Proves (subst_p ((obj [car] x) ::~ tFalse) o x) tP
      -> Proves (subst_p ((obj [car] x) ::= tFalse) o x) fP
      -> SubObj (subst_o (Some (obj [car] x)) o x) o'
      -> TypeOf Γ (eApp Car' e) τ1 (tP, fP) o'
| T_Cdr :
    forall τ1 τ2 Γ e tP0 fP0 o o' tP fP x,
      TypeOf Γ e (tPair τ1 τ2) (tP0, fP0) o
      -> Proves (subst_p ((obj [cdr] x) ::~ tFalse) o x) tP
      -> Proves (subst_p ((obj [cdr] x) ::= tFalse) o x) fP
      -> SubObj (subst_o (Some (obj [cdr] x)) o x) o'
      -> TypeOf Γ (eApp Cdr' e) τ2 (tP, fP) o'
| T_Let :
    forall σ' τ σ Γ e0 tP0 fP0 o0 e1 tP1 fP1 o1 x tP1' fP1' o1',
      TypeOf Γ e0 τ (tP0, fP0) o0
      -> TypeOf (Γ & ((var x) ::= τ)
                   & (((var x) ::~ tFalse) =-> tP0)
                   & (((var x) ::= tFalse) =-> fP0)) 
                e1
                σ
                (tP1, fP1)
                o1
      -> Subtype (subst_t σ o0 x) σ'
      -> Proves (subst_p tP1 o0 x) tP1'
      -> Proves (subst_p fP1 o0 x) fP1'
      -> SubObj (subst_o o1 o0 x) o1'
      -> TypeOf Γ (eLet x e0 e1) σ' (tP1', fP1') o1'

(** ** Subtype *)

with Subtype : relation type :=
| S_Refl : 
    forall τ, Subtype τ τ
| S_Top : 
    forall τ, Subtype τ tTop
| S_UnionSuper :
    forall τ σ1 σ2,
      (Subtype τ σ1 \/ Subtype τ σ2)
      -> Subtype τ (tUnion σ1 σ2)
| S_UnionSub :
    forall τ1 τ2 σ,
      Subtype τ1 σ
      -> Subtype τ2 σ
      -> Subtype (tUnion τ1 τ2) σ
| S_Abs :
    forall x x' τ τ' σ σ' tP tP' fP fP' o o',
      Subtype (subst_t τ (Some (var x')) x) τ'
      -> Subtype σ' (subst_t σ (Some (var x')) x) 
      -> Proves (subst_p tP (Some (var x')) x) tP'
      -> Proves (subst_p fP (Some (var x')) x) fP'
      -> SubObj (subst_o o (Some (var x')) x) o'
      -> Subtype (tAbs x (σ, τ) (tP, fP) o)
                 (tAbs x' (σ', τ') (tP', fP') o')
| S_Pair :
    forall τ1 σ1 τ2 σ2,
      Subtype τ1 τ2
      -> Subtype σ1 σ2
      -> Subtype (tPair τ1 σ1) (tPair τ2 σ2).


(** Proof Helpers/Lemmas *)
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
  


(** *Automation for Examples *)

Hint Constructors TypeOf Update.
Hint Resolve P_Refl S_Refl SO_Refl .





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
Proof with crush. 
  intros x.
  eapply T_If...
  eapply T_App...
  eapply T_Const...
  eapply T_Var...
  eapply T_App...
  eapply T_Const... 
  eapply T_Var...
  eapply P_AndE_rhs...
  crush.
  eapply P_Or...
  eapply P_Or...
  eapply P_False.
  eapply P_False.
  crush.
  eapply S_UnionSub...
Grab Existential Variables.
crush. crush.
Qed.

(*
Thoughts during & after the long, long proof:

Subtype tTop _  => try S_Refl
Proves (var x ::= tTop) (?120251 ::= ?120250) => must use P_Refl
   since top can only prove top
    - what does this imply for cases w/o Top? How can they behave?

Proves (var x ::~ tFalse) ?120218 => these cases will always be
  P_Refl since if *All* we know is it is not type X, we don't
  know anything more (unless it's ~ tTop?? meh)

Proves TT ?? must be P_Refl

Can we prove P & TT = P?

A functional equivalence for prop would be nice:
Axiom: forall P Q, (forall Z, Proves P Z <-> Proves Q Z) -> P = Q
OR! We could just make a rule in the auto rules that say
if you see P & TT, apply P_AndE; left, and the flip for right

Function for "Path to False" would be sweet. i.e., if we had
the prop P & Q & FF & R proves Z, give me the path of
tactics to get to the FF. OR just prove for some function
"contains" that if contains lhs FF then it proves the rhs.

ALWAYS!!! Try SO_Refl before SO_None!!!

When Proving Proves P ?124353 or similar, be careful about losing information
- perhaps P_Refl is *always* the best so *all* of the info is propogated,
instead of trying to reason about what to keep and what to ignore

Example of try always else
ALWAYS try SO_REFL, if that fails, then try SO_None or whatever

perhaps for Proves, ALWAYS TRY P_Refl, then if that fails start
drilling down into how to prove each thing

The rules for Proves are still somewhat tied to the idea of an "environment"
of properties instead of just 1 big property... this could be improved.

*)


End LTR.
