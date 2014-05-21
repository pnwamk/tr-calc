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
| tFun : id -> (type * type) -> (prop * prop) -> opt object -> type

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
| eAbs : id -> type -> exp -> exp
| eApp : exp -> exp -> exp
| eLet : id -> exp -> exp.
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
      (tFun x 
            (tTop, tBool) 
            (((var x) ::= tNum), ((var x) ::~ tNum)) 
            None)
    | opIsProc =>
      (tFun x 
            (tTop, tBool) 
            (((var x) ::= (tFun x (tBot, tTop) (TT, FF) None)), 
             ((var x) ::~ (tFun x (tBot, tTop) (TT, FF) None)))
            None)
    | opIsBool =>
      (tFun x 
            (tTop, tBool) 
            (((var x) ::= tBool), ((var x) ::~ tBool)) 
            None)
    | opIsCons =>
      (tFun x 
            (tTop, tBool) 
            (((var x) ::= (tPair tTop tTop)), ((var x) ::~ (tPair tTop tTop)))
            None)
    | opAdd1 =>
      (tFun x 
            (tNum, tNum) 
            (TT, FF)
            None)
    | opIsZero =>
      (tFun x 
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
    | tFun x (t1, t2) (p1, p2) o =>
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
Fixpoint subst_p (b:bool)
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
              Is (obj (pth1 ++ pth2) y) (subst_t b t opto x)
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
              Is (obj (pth1 ++ pth2) y) (subst_t b t opto x)
          end
        | right _, false => p
        | right _, true => (truth b)
      end
    | P =-> Q => (subst_p (negb b) P opto x) =-> (subst_p b Q opto x)
    | P + Q => (subst_p b P opto x) + (subst_p b Q opto x)
    | P & Q => (subst_p b P opto x) & (subst_p b Q opto x)
    | _ => p
  end

with subst_t (b:bool)
             (t:type)
             (opto:opt object)
             (x:id) : type :=
  match t with
    | tUnion lhs rhs => tUnion (subst_t b lhs opto x) (subst_t b rhs opto x)
    | tFun y (t1, t2) (p1, p2) opto2 =>
      if id_eqdec x y
      then t
      else tFun y
                ((subst_t b t1 opto x),
                 (subst_t b t2 opto x))
                ((subst_p b p1 opto x),
                 (subst_p b p2 opto x))
                (subst_o opto2 opto x)
    | tPair t1 t2 => tPair (subst_t b t1 opto x)
                           (subst_t b t2 opto x)
    | _ => t
  end.

(** A few helpers to reason about subtyping: *)

Inductive isUnion : type -> Prop :=
| isU : forall t1 t2, isUnion (tUnion t1 t2).

Fixpoint typestructuralsize (t:type) : nat :=
  match t with
    | tUnion t1 t2 =>
      S (plus (typestructuralsize t1) (typestructuralsize t2))
    | tFun x (t1, t2) _ _ => S (plus (typestructuralsize t1) (typestructuralsize t2))
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
    | tFun _ _ _ _, tFun _ _ _ _ => true
    | tFun _ _ _ _, _ => false
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
    | tFun _ (t1,t2) _ _, tFun _ (t3, t4) _ _ =>
      andb (possible_subtype t1 t3)
           (possible_subtype t2 t4)
    | tFun _ _ _ _, _ => false
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
Hint Constructors SubObj.

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
| P_AndE :
    forall P Q R,
      (Proves P R \/ Proves Q R) 
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
| P_OrI :
    forall P Q R,
      (Proves P Q \/ Proves P R) 
      -> Proves P (Q + R)
| P_OrE :
    forall P Q R Y,
      Proves (P & Q) Y
      -> Proves (P & R) Y
      -> Proves (P & (Q + R)) Y
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
    forall Γ t' tP' fP' o' n,
      Subtype tNum t'
      -> Proves TT tP'
      -> Proves FF fP'
      -> SubObj None o'
      -> TypeOf Γ (eNum n) t' (tP', fP') o'
| T_Const :
    forall Γ c x τ' tP' fP' o',
      Proves (Γ & TT) tP'
      -> Proves (Γ & FF) fP'
      -> Subtype (const_type c x) τ'
      -> SubObj None o'
      -> TypeOf Γ (eOp (c_op c)) τ' (tP', fP') o'
| T_True :
    forall Γ t' tP' fP' o',
      Subtype tTrue t'
      -> Proves TT tP'
      -> Proves FF fP'
      -> SubObj None o'
      -> TypeOf Γ eTrue t' (tP', fP') o'
| T_False :
    forall Γ t' tP' fP' o',
      Subtype tFalse t'
      -> Proves FF tP'
      -> Proves TT fP'
      -> SubObj None o'
      -> TypeOf Γ eFalse t' (tP', fP') o'

(* TODO *)
(** ** Subtype *)

with Subtype : relation type :=
| S_Refl : forall x, Subtype x x.

(* TypeOf Rules 
with TypeOf : env -> exp -> type -> env -> env -> obj -> Prop :=
     | T_isnum :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tTop
                       (envFact true tNum (var x) envEmpty)
                       (envFact false tNum (var x) envEmpty)
                       objnil
                       tBool)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E isnum' t' tE' fE' o'
     | T_isproc :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tTop
                       (envFact true (tλ x tBot tt ff objnil tTop) (var x) envEmpty)
                       (envFact false (tλ x tBot tt ff objnil tTop) (var x) envEmpty)
                       objnil
                       tBool)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E isproc' t' tE' fE' o'
     | T_isbool :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tTop
                       (envFact true tBool (var x) envEmpty)
                       (envFact false tBool (var x) envEmpty)
                       objnil
                       tBool)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E isbool' t' tE' fE' o'
     | T_iscons :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tTop
                       (envFact true (tPair tTop tTop) (var x) envEmpty)
                       (envFact false (tPair tTop tTop) (var x) envEmpty)
                       objnil
                       tBool)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E iscons' t' tE' fE' o'
     | T_add1 :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tNum
                       tt
                       ff
                       objnil
                       tNum)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E add1' t' tE' fE' o'

     | T_iszero :
         forall t' E x tE' fE' o',
           Subtype (tλ x
                       tTop
                       tt
                       tt
                       objnil
                       tBool)
                   t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E iszero' t' tE' fE' o'

     | T_Num :
         forall t' E tE' fE' o' n,
           Subtype tNum t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E (expNum n) t' tE' fE' o'
     | T_True :
         forall t' E tE' fE' o',
           Subtype tTrue t' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E expT t' tE' fE' o'
     | T_False :
         forall t' E tE' fE' o',
           Subtype tFalse t' ->
           Proves ff tE' ->
           Proves tt fE' ->
           SubObj objnil o' ->
           TypeOf E expF t' tE' fE' o'
     | T_Var :
         forall t' t E x tE' fE' o',
           Proves E (envFact true t (var x) envEmpty) ->
           Subtype t t' ->
           Proves (envFact false tFalse (var x) envEmpty) tE' ->
           Proves (envFact true tFalse (var x) envEmpty) fE' ->
           SubObj (var x) o' ->
           TypeOf E
                  (expVar x)
                  t'
                  tE'
                  fE'
                  (var x)
     | T_Abs :
         forall σ' t' σ t E x e tE fE o tE' fE' o',
           TypeOf (envFact true σ (var x) E) e t tE fE o ->
           Subtype t t' ->
           Subtype σ' σ ->
           SubObj o o' ->
           Proves tE tE' ->
           Proves fE fE' ->
           TypeOf E
                  (expλ x σ e)
                  (tλ x σ' tE fE o t')
                  tE'
                  fE'
                  o'
     | T_App :
         forall t'' σ t σ' E e x tEλ fEλ oλ tE fE o e' tE' fE' o' tEλ'' fEλ'' o'',
           TypeOf E e (tλ x σ tEλ fEλ oλ t) tE fE o ->
           TypeOf E e' σ' tE' fE' o' ->
           Subtype σ' σ ->
           Subtype (subst_t t o' x) t'' ->
           Proves (subst_env tEλ o' x) tEλ'' ->
           Proves (subst_env fEλ o' x) fEλ'' ->
           SubObj (subst_o oλ o' x) o'' ->
           TypeOf E (expApp e e') t'' tEλ'' fEλ'' o''
                  
     | T_If :
         forall t' t1 t2 t3 E e1 tE1 fE1 o1 e2 tE2 fE2 o e3 tE3 fE3 o',
           TypeOf E e1 t1 tE1 fE1 o1 ->
           TypeOf (env_app E tE1) e2 t2 tE2 fE2 o ->
           TypeOf (env_app E fE1) e3 t3 tE3 fE3 o ->
           Subtype (tUnion t2 t3) t' ->
           (* Subtype t2 t' ->
Subtype t3 t' -> *)
           SubObj o o' ->
           TypeOf E (expIf e1 e2 e3) t' (envOr tE2 tE3) (envOr fE2 fE3) o
     | T_Cons :
         forall t1' t2' t1 t2 E e1 tE1 fE1 o1 e2 tE2 fE2 o2 o' fE' tE',
           TypeOf E e1 t1 tE1 fE1 o1 ->
           TypeOf E e2 t2 tE2 fE2 o2 ->
           Subtype t1 t1' ->
           Subtype t2 t2' ->
           Proves tt tE' ->
           Proves ff fE' ->
           SubObj objnil o' ->
           TypeOf E (expCons e1 e2) (tPair t1' t2') tE' fE' o'
     | T_Car :
         forall t1 t2 E e tE0 fE0 o o' tE fE x,
           TypeOf E e (tPair t1 t2) tE0 fE0 o ->
           tE = (subst_env (envFact false tFalse (objπ [car] x) envEmpty) o x) ->
           fE = (subst_env (envFact true tFalse (objπ [car] x) envEmpty) o x) ->
           o' = subst_o (objπ [car] x) o x ->
           TypeOf E (expApp car' e) t1 tE fE o'
     | T_Cdr :
         forall t2 t1 E e tE0 fE0 o o' tE fE x,
           TypeOf E e (tPair t1 t2) tE0 fE0 o ->
           tE = (subst_env (envFact false tFalse (objπ [cdr] x) envEmpty) o x) ->
           fE = (subst_env (envFact true tFalse (objπ [cdr] x) envEmpty) o x) ->
           o' = subst_o (objπ [cdr] x) o x ->
           TypeOf E (expApp cdr' e) t2 tE fE o'
     | T_Let :
         forall σ' t σ E e0 tE0 fE0 o0 e1 tE1 fE1 o1 x tE1' fE1' o1',
           TypeOf E e0 t tE0 fE0 o0 ->
           TypeOf (env_app (envFact true t (var x) envEmpty)
                           (env_app (envOr (envFact true tFalse (var x) envEmpty)
                                           tE0)
                                    (envOr (envFact false tFalse (var x) envEmpty)
                                           fE0)))
                  e1
                  σ
                  tE1
                  fE1
                  o1 ->
           Subtype (subst_t σ o0 x) σ'->
           Proves (subst_env tE1 o0 x) tE1' ->
           Proves (subst_env fE1 o0 x) fE1' ->
           SubObj (subst_o o1 o0 x) o1' ->
           TypeOf E (expLet x e0 e1) σ' tE1' fE1' o1'

(* subtyping *)
with Subtype : relation type :=
     | S_Refl : forall x, Subtype x x
     | S_Top : forall x, Subtype x tTop
     | S_UnionSuper_l :
         forall t t1 t2,
           Subtype t t1 ->
           Subtype t (tUnion t1 t2)
     | S_UnionSuper_r :
         forall t t1 t2,
           Subtype t t2 ->
           Subtype t (tUnion t1 t2)
     | S_UnionSub :
         forall t t1 t2,
           Subtype t1 t ->
           Subtype t2 t ->
           Subtype (tUnion t1 t2) t
     | S_Fun :
         forall x t t' σ σ' tE tE' fE fE' o o',
           Subtype t t' ->
           Subtype σ' σ ->
           Proves tE tE' ->
           Proves fE fE' ->
           SubObj o o' ->
           Subtype (tλ x σ tE fE o t)
                   (tλ x σ' tE' fE' o' t')
     | S_Pair :
         forall t1 t2 t1' t2',
           Subtype t1 t1' ->
           Subtype t2 t2' ->
           Subtype (tPair t1 t2) (tPair t1' t2').
*)




  End LTR.
