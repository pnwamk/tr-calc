
Require Import LibTactics.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.
Require Import Coq.Program.Wf.

Import ListNotations.
Open Scope list_scope.


Section LTR.

Inductive id : Type :=
  Id : nat -> id.

Hint Resolve eq_nat_dec.

Theorem id_eqdec : forall (x y : id),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

(* Path Elements (accessors) *)
Inductive acc : Type := car | cdr.

Theorem acc_eqdec : forall (x y: acc),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve acc_eqdec.

Definition path := list acc.

Hint Resolve list_eq_dec.
Theorem path_eqdec : forall (x y: path),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eqdec.


(* Objects *)
Inductive obj : Type :=
| objnil : obj
| objπ : path -> id -> obj.

Theorem obj_eqdec : forall (x y: obj),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

(* Types *)
Inductive type : Type :=
| tTop : type (* Top *)
| tNum : type (* Numbers *)
| tTrue : type (* True *)
| tFalse : type (* False *)
| tBottom : type
| tUnion : type -> type -> type (* union *)
| tλ : id -> 
       type -> 
       env -> 
       env -> 
       obj -> 
       type -> type (* function *)
| tPair :  type -> type -> type (* cons pair *)
with env : Type :=
| envEmpty : env
| envFalse : env -> env
| envFact  : bool -> type -> obj -> env -> env
| envOr    : env -> env -> env.
Hint Constructors type env.

Notation tBool := (tUnion tTrue tFalse).

Hint Resolve bool_dec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with env_eqdec (x y : env) : {x=y}+{x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.
Hint Resolve type_eqdec env_eqdec.

Fixpoint env_app (Γ1 Γ2: env) : env :=
match Γ1 with
| envEmpty => Γ2
| envFalse rest => envFalse (env_app rest Γ2)
| envFact b t o rest => envFact b t o (env_app rest Γ2)
| envOr lhs rhs => envOr (env_app lhs Γ2) (env_app rhs Γ2)
end.


Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y})
                       (l:list (set X)) : set X :=
match l with
| nil => nil
| x :: xs => set_union dec x (setU dec xs)
end.


(* free variables in objects *)
Definition fv_set_o (o : obj) : set id :=
match o with
| objnil => nil
| objπ _ x => [x]
end.

(* free variables in types *)

Fixpoint fv_set_t (t : type) : set id :=
match t with
| tUnion t1 t2 =>
  set_union id_eqdec (fv_set_t t1) (fv_set_t t2)
| tλ x t1 p1 p2 o t2 =>
  setU id_eqdec
       [[x];
        (fv_set_t t1);
        (fv_set_env p1);
        (fv_set_env p2);
        (fv_set_o o);
        (fv_set_t t2)]
| tPair t1 t2 =>
  set_union id_eqdec
            (fv_set_t t1)
            (fv_set_t t2)
| _ => nil
end

(* free variables in the proposition environment*)
with fv_set_env (E : env) : set id :=
match E with
| envEmpty => nil
| envFalse rest => fv_set_env rest
| envFact b t o rest => setU id_eqdec 
                             [(fv_set_t t);
                              (fv_set_o o);
                              (fv_set_env rest)]
| envOr lhs rhs => set_union id_eqdec (fv_set_env lhs) (fv_set_env rhs)
end.

Definition subst_o (o1 o2:obj) (x:id) : obj :=
match o1 with
| objnil => objnil
| objπ pth1 z =>
  match id_eqdec x z, o2 with
  | left _, objnil => objnil
  | left _, objπ pth2 y => objπ (pth1 ++ pth2) y
  | right _, _ => o1
  end
end.

(* subst+ and - for properties*)
Fixpoint subst_env (E:env)
                   (o:obj)
                   (x:id) : env :=
match E with
| envEmpty => envEmpty
| envFalse rest => envFalse (subst_env rest o x)
| envFact fb ft (objπ pth1 z) rest =>
  match id_eqdec x z, set_mem id_eqdec z (fv_set_t ft) with
  | left _, _ =>
    match o with
    | objnil => subst_env rest o x (* tt - ignore *)
    | objπ pth2 y =>
      envFact fb (subst_t ft o x) (objπ (pth1 ++ pth2) y) (subst_env rest o x)
    end
  | right _, false => envFact fb ft (objπ pth1 z) (subst_env rest o x)
  | right _, true => subst_env rest o x (* tt - ignore *)
  end
| envFact fb ft objnil rest => envFact fb ft objnil (subst_env rest o x)
| envOr lhs rhs => envOr (subst_env lhs o x) (subst_env rhs o x)
end

(* type substitution *)
with subst_t (t:type)
             (o:obj)
             (x:id) : type :=
match t with
| tUnion t1 t2 => tUnion (subst_t t1 o x) (subst_t t2 o x)
| tλ y t1 p1 p2 o2 t2 =>
  if id_eqdec x y
  then t
  else tλ y
          (subst_t t1 o x)
          (subst_env p1 o x)
          (subst_env p2 o x)
          (subst_o o2 o x)
          (subst_t t2 o x)
| tPair t1 t2 => tPair (subst_t t1 o x)
                       (subst_t t2 o x)
| _ => t
end.

(* Constant Operations *)
Inductive c_op : Type :=
| op_add1 : c_op
| op_iszero : c_op
| op_isnum : c_op
| op_isbool : c_op
| op_isproc : c_op
| op_iscons : c_op.

Theorem c_op_eqdec : forall (x y : c_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve c_op_eqdec.

(* Polymorphic Operations *)
Inductive p_op : Type :=
| op_car : p_op
| op_cdr : p_op.

Theorem p_op_eqdec : forall (x y : p_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve p_op_eqdec.

(* Primitive Operations *)
Inductive primop : Type :=
| prim_c : c_op -> primop
| prim_p : p_op -> primop.

Theorem primop_eqdec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eqdec.

(* Expressions *)
Inductive exp : Type :=
| expVar : id -> exp
| expApp : exp -> exp -> exp
| expλ : id -> type -> exp -> exp
| expIf : exp -> exp -> exp -> exp
| expPrimop : primop -> exp
| expT : exp
| expF : exp
| expNum : nat -> exp
| expCons : exp -> exp -> exp
| expLet : id -> exp -> exp -> exp.

Notation car' := (expPrimop (prim_p op_car)).
Notation cdr' := (expPrimop (prim_p op_cdr)).
Notation add1' := (expPrimop (prim_c op_add1)).
Notation iszero' := (expPrimop (prim_c op_iszero)).
Notation isnum' := (expPrimop (prim_c op_isnum)).
Notation isbool' := (expPrimop (prim_c op_isbool)).
Notation isproc' := (expPrimop (prim_c op_isproc)).
Notation iscons' := (expPrimop (prim_c op_iscons)).

Theorem exp_eqdec : forall (x y : exp),
{x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition exp_eq (x y : exp) : bool :=
if exp_eqdec x y then true else false.

Inductive SubObj : relation obj :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj objnil x.
Hint Constructors SubObj.

Inductive isUnion : type -> Prop :=
| isU : forall t1 t2, isUnion (tUnion t1 t2).


Fixpoint typestructuralsize (t:type) : nat :=
match t with
| tTop => 1
| tBottom => 1
| tNum => 1
| tTrue => 1
| tFalse => 1
| tUnion t1 t2 => 
  1 + (typestructuralsize t1) + (typestructuralsize t2)
| tλ x t1 e1 e2 o t2 => 1 + (typestructuralsize t1) + (typestructuralsize t2)
| tPair t1 t2 => 1 + (typestructuralsize t1) + (typestructuralsize t2)
end.

Program Fixpoint common_subtype (type1 type2:type) 
        {measure ((typestructuralsize type1) + (typestructuralsize type2))} : bool := 
match type1, type2 with
| tTop , _ => true
| _, tTop => true
| tBottom, _ => false
| _, tBottom => false
| tUnion t1 t2, tUnion t3 t4 =>
  orb (common_subtype t1 t3)
      (orb (common_subtype t1 t4)
           (orb (common_subtype t2 t3)
                (common_subtype t2 t4)))           
| tUnion t1 t2, _ => orb (common_subtype t1 type2) (common_subtype t2 type2)
| _, tUnion t1 t2 => orb (common_subtype type1 t1) (common_subtype type1 t2)
| tNum,  tNum => true
| tNum, _ => false
| tTrue,  tTrue => true
| tTrue, _ => false 
| tFalse,  tFalse => true
| tFalse, _ => false 
| tλ _ _ _ _ _ _, tλ _ _ _ _ _ _  => true
| tλ _ _ _ _ _ _, _ => false
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
        {measure ((typestructuralsize pos_sub) + (typestructuralsize pos_super))} : bool :=
match pos_sub, pos_super with
| tTop , tTop => true
| tTop , tUnion t1 t2 => 
  orb (possible_subtype tTop t1)
      (possible_subtype tTop t2)
| tTop , _ => false
| tBottom , tBottom => true
| tBottom , tUnion t1 t2 => 
  orb (possible_subtype tBottom t1)
      (possible_subtype tBottom t2)
| tBottom , _ => false
| tNum , tNum => true
| tNum , tUnion t1 t2 => 
  orb (possible_subtype tNum t1)
      (possible_subtype tNum t2)
| tNum , _ => false
| tTrue , tTrue => true
| tTrue , tUnion t1 t2 => 
  orb (possible_subtype tTrue t1)
      (possible_subtype tTrue t2)
| tTrue , _ => false
| tFalse , tFalse => true
| tFalse , tUnion t1 t2 => 
  orb (possible_subtype tFalse t1)
      (possible_subtype tFalse t2)
| tFalse , _ => false
| tUnion t1 t2, _ => 
  andb (possible_subtype t1 pos_super)
       (possible_subtype t2 pos_super)
| tλ _ t1 _ _ _ t2, tλ _ t3 _ _ _ t4 =>
  andb (possible_subtype t1 t3)
       (possible_subtype t2 t4)
| tλ _ _ _ _ _ _, tUnion t1 t2 =>
  orb (possible_subtype pos_sub t1)
      (possible_subtype pos_sub t2)
| tλ _ _ _ _ _ _, _ => false
| tPair t1 t2, tPair t3 t4 => 
  andb (possible_subtype t1 t3)
       (possible_subtype t2 t4)
| tPair _ _, tUnion t1 t2 =>
  orb (possible_subtype pos_sub t1)
      (possible_subtype pos_sub t2)
| tPair _ _, _ => false
end.
Solve Obligations using crush.

Definition typelookup := option (obj -> type).
Definition emptylookup : typelookup := Some (fun o => tTop).

Definition falselookup : typelookup := None.

Definition extend_lookup (o:obj) (t:type) (tl:typelookup) : typelookup :=
if type_eqdec t tBottom then None else
match tl with
| None => None
| Some tl => Some (fun o' => if obj_eqdec o o' then t else tl o')
end.

Definition tt := envEmpty.
Definition ff := envFalse envEmpty.

Notation "(var x )" := (objπ [] x).

Inductive lookupset : Type :=
| tls_atom : typelookup -> lookupset
| tls_cons : typelookup -> lookupset -> lookupset.

Fixpoint tls_app (l1 l2:lookupset) : lookupset :=
match l1 with
| tls_atom tl => (tls_cons tl l2)
| tls_cons tl tls => (tls_cons tl (tls_app tls l2))
end.           

Inductive UpdatedEnv : env -> lookupset -> Prop :=
| UE_Empty :
    UpdatedEnv envEmpty (tls_atom emptylookup)
| UE_False :
    forall E,
      UpdatedEnv (envFalse E) (tls_atom falselookup)
| UE_Fact :
    forall E tlset b t o tlset',
    UpdatedEnv E tlset ->
    UpdatedLookupSet b t o tlset tlset' ->
    UpdatedEnv (envFact b t o E) tlset' 
| UE_Or :
    forall E1 E2 tlset1 tlset2, 
    UpdatedEnv E1 tlset1 ->
    UpdatedEnv E2 tlset2 ->
    UpdatedEnv (envOr E1 E2) (tls_app tlset1 tlset2) 

with UpdatedLookupSet : bool -> type -> obj -> lookupset -> lookupset -> Prop :=
| ULS_Atom :
    forall b t o tl tl',
      UpdatedLookup b t o tl tl' ->
      UpdatedLookupSet b t o (tls_atom tl) (tls_atom tl')                    
| ULS_Cons :
    forall b t o tl tl' tls tls',
      UpdatedLookupSet b t o tls tls' ->
      UpdatedLookup b t o tl tl' ->
      UpdatedLookupSet b t o (tls_cons tl tls) (tls_cons tl' tls')

with UpdatedLookup : bool -> type -> obj -> typelookup -> typelookup -> Prop :=
| UL_Some :
    forall b t t' pth pth' pth'' x tl updated,
      pth'' = (pth ++ pth') ->
      tl (objπ pth' x) = t' ->
      UpdatedType t' (b, t) pth updated ->
      UpdatedLookup b t (objπ pth'' x) (Some tl) (extend_lookup (objπ pth' x) updated (Some tl))
| UL_None :
    forall b t o,
    UpdatedLookup b t o None None

with UpdatedType : type -> (bool * type) -> path -> type -> Prop :=
| UT_Car :
    forall t v pth σ updated,
      UpdatedType t v pth updated ->
      UpdatedType (tPair t σ) v (pth ++ [car]) (tPair updated σ)
| UT_Cdr :
    forall t v pth σ updated,
      UpdatedType σ v pth updated ->
      UpdatedType (tPair t σ) v (pth ++ [cdr]) (tPair t updated)
| UT_T :
    forall t σ restricted,
      Restricted t σ restricted ->
      UpdatedType t (true, σ) nil restricted
| UT_NT :
    forall t σ removed,
      Removed t σ removed ->
      UpdatedType t (false, σ) nil removed


with Restricted : type -> type -> type -> Prop :=
| RES_Bottom :
    forall t σ,
      common_subtype t σ = false ->
      Restricted t σ tBottom
| RES_Bottom_l :
    forall σ,
      Restricted tBottom σ tBottom
| RES_Bottom_r :
    forall σ,
      Restricted σ tBottom tBottom
| RES_U :
    forall t1 t2 σ t1' t2',
      common_subtype (tUnion t1 t2) σ = true ->
      Restricted t1 σ t1' ->
      Restricted t2 σ t2' ->
      Restricted (tUnion t1 t2) σ (tUnion t1' t2')
| RES_Sub :
    forall t σ,
      (~isUnion t) ->
      Subtype t σ ->
      Restricted t σ t
| RES_NonSub :
    forall t σ,
      possible_subtype t σ = false -> 
      common_subtype t σ = true ->
      (~isUnion t) ->
      NonSubtype t σ ->
      Restricted t σ σ

with Removed : type -> type -> type -> Prop :=
| REM_Bottom_l :
    forall σ,
      Removed tBottom σ tBottom
| REM_Bottom_r :
    forall t,
      Removed t tBottom t
| REM_Union :
    forall t1 t2 t1' t2' σ,
      Removed t1 σ t1' ->
      Removed t2 σ t2' ->
      Removed (tUnion t1 t2) σ (tUnion t1' t2')
| REM_Sub :
    forall t σ,
      Subtype t σ ->
      Removed t σ tBottom
| REM_NonSub :
    forall t σ,
      NonSubtype t σ -> 
      (~isUnion t) ->
      Removed t σ t

(* Typing Rules *)
with Typing : env -> exp -> type -> env -> env -> obj -> Prop :=
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
    Typing E isnum' t' tE' fE' o'
| T_isproc :
  forall t' E x tE' fE' o',
    Subtype (tλ x
               tTop
               (envFact true (tλ x tBottom tt ff objnil tTop) (var x) envEmpty)
               (envFact false (tλ x tBottom tt ff objnil tTop) (var x) envEmpty)
               objnil
               tBool)
            t' ->
    Proves tt tE' ->
    Proves ff fE' ->
    SubObj objnil o' ->
    Typing E isproc' t' tE' fE' o'
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
    Typing E isbool' t' tE' fE' o'
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
    Typing E iscons' t' tE' fE' o'
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
    Typing E add1' t' tE' fE' o'

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
    Typing E iszero' t' tE' fE' o'

| T_Num :
  forall t' E tE' fE' o' n,
      Subtype tNum t' ->
      Proves tt tE' ->
      Proves ff fE' ->
      SubObj objnil o' ->
      Typing E (expNum n) t' tE' fE' o'
| T_True :
  forall t' E tE' fE' o',
      Subtype tTrue t' ->
      Proves tt tE' ->
      Proves ff fE' ->
      SubObj objnil o' ->
      Typing E expT t' tE' fE' o'
| T_False :
  forall t' E tE' fE' o',
      Subtype tFalse t' ->
      Proves ff tE' ->
      Proves tt fE' ->
      SubObj objnil o' ->
      Typing E expF t' tE' fE' o'
| T_Var :
    forall t' t E x tE' fE' o',
      Proves E (envFact true t (var x) envEmpty) ->
      Subtype t t' ->
      Proves (envFact false tFalse (var x) envEmpty) tE' ->
      Proves (envFact true tFalse (var x) envEmpty) fE' ->
      SubObj (var x) o' ->
      Typing E
             (expVar x)
             t'
             tE'
             fE'
             (var x)
| T_Abs :
   forall σ' t' σ t E x e tE fE o tE' fE' o',
     Typing (envFact true σ (var x) E) e t tE fE o ->
     Subtype t t' ->
     Subtype σ' σ ->
     SubObj o o' ->
     Proves tE tE' ->
     Proves fE fE' ->
     Typing E
            (expλ x σ e)
            (tλ x σ' tE fE o t')
            tE'
            fE'
            o'
| T_App :
   forall t'' σ t σ' E e x tEλ fEλ oλ tE fE o e' tE' fE' o' tEλ'' fEλ'' o'',
     Typing E e (tλ x σ tEλ fEλ oλ t) tE fE o ->
     Typing E e' σ' tE' fE' o' ->
     Subtype σ' σ ->
     Subtype (subst_t t o' x) t'' ->
     Proves (subst_env tEλ o' x) tEλ'' ->
     Proves (subst_env fEλ o' x) fEλ'' ->
     SubObj (subst_o oλ o' x) o'' ->
     Typing E (expApp e e') t'' tEλ'' fEλ'' o''
 
| T_If :
   forall t' t1 t2 t3 E e1 tE1 fE1 o1 e2 tE2 fE2 o e3 tE3 fE3 o',
     Typing E e1 t1 tE1 fE1 o1 ->
     Typing (env_app E tE1) e2 t2 tE2 fE2 o ->
     Typing (env_app E fE1) e3 t3 tE3 fE3 o ->
     Subtype (tUnion t2 t3) t' ->
(*     Subtype t2 t' ->
     Subtype t3 t' -> *)
     SubObj o o' ->
     Typing E (expIf e1 e2 e3) t' (envOr tE2 tE3) (envOr fE2 fE3) o
| T_Cons :
   forall t1' t2' t1 t2 E e1 tE1 fE1 o1 e2 tE2 fE2 o2 o' fE' tE',
     Typing E e1 t1 tE1 fE1 o1 ->
     Typing E e2 t2 tE2 fE2 o2 ->
     Subtype t1 t1' ->
     Subtype t2 t2' ->
     Proves tt tE' ->
     Proves ff fE' ->
     SubObj objnil o' ->
     Typing E (expCons e1 e2) (tPair t1' t2') tE' fE' o'
| T_Car :
   forall t1 t2 E e tE0 fE0 o o' tE fE x,
     Typing E e (tPair t1 t2) tE0 fE0 o ->
     tE = (subst_env (envFact false tFalse (objπ [car] x) envEmpty) o x) ->
     fE = (subst_env (envFact true tFalse (objπ [car] x) envEmpty) o x) ->
     o' = subst_o (objπ [car] x) o x ->
     Typing E (expApp car' e) t1 tE fE o'
| T_Cdr :
   forall t2 t1 E e tE0 fE0 o o' tE fE x,
     Typing E e (tPair t1 t2) tE0 fE0 o ->
     tE = (subst_env (envFact false tFalse (objπ [cdr] x) envEmpty) o x) ->
     fE = (subst_env (envFact true tFalse (objπ [cdr] x) envEmpty) o x) ->
     o' = subst_o (objπ [cdr] x) o x ->
     Typing E (expApp cdr' e) t2 tE fE o'
| T_Let :
   forall σ' t σ E e0 tE0 fE0 o0 e1 tE1 fE1 o1 x tE1' fE1' o1',
     Typing E e0 t tE0 fE0 o0 ->
     Typing (env_app (envFact true t (var x) envEmpty)
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
     Proves (subst_env tE1 o0 x) tE1'  ->
     Proves (subst_env fE1 o0 x) fE1'  ->
     SubObj (subst_o o1 o0 x) o1' ->
     Typing E (expLet x e0 e1) σ' tE1' fE1' o1'

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
      Subtype (tPair t1 t2) (tPair t1' t2')


(* subtype negation *)
with NonSubtype : type -> type -> Prop :=
| NS_Trivial : forall t1 t2,
          possible_subtype t1 t2 = false ->
          NonSubtype t1 t2
| NS_UnionSuper :
    forall t1 t2 t3,
      NonSubtype t1 t2 ->
      NonSubtype t1 t3 ->
      NonSubtype t1 (tUnion t2 t3)
| NS_UnionSub_l :
    forall t1 t2 t3,
      NonSubtype t1 t3 ->
      NonSubtype (tUnion t1 t2) t3 
| NS_UnionSub_r :
    forall t1 t2 t3,
      NonSubtype t2 t3 ->
      NonSubtype (tUnion t1 t2) t3 
| NS_Abs_arg :
    forall σ σ' x tE fE o t tE' fE' o' t',
      NonSubtype σ' σ ->
      NonSubtype (tλ x σ tE fE o t) (tλ x σ' tE' fE' o' t')
| NS_Abs_result :
    forall σ σ' x tE fE o t tE' fE' o' t',
      NonSubtype t t' ->
      NonSubtype (tλ x σ tE fE o t) (tλ x σ' tE' fE' o' t')
| NS_Abs_obj :
    forall σ σ' x tE fE o t tE' fE' o' t',
      ~SubObj o o' ->
      NonSubtype (tλ x σ tE fE o t) (tλ x σ' tE' fE' o' t')
| NS_Abs_tEnv :
    forall σ σ' x tE fE o t tE' fE' o' t',
      CannotProve tE tE' ->
      NonSubtype (tλ x σ tE fE o t) (tλ x σ' tE' fE' o' t')
| NS_Abs_fEnv :
    forall σ σ' x tE fE o t tE' fE' o' t',
      CannotProve fE fE' ->
      NonSubtype (tλ x σ tE fE o t) (tλ x σ' tE' fE' o' t')      

(* Proves: One environment (lhs) has the typing information
   to prove the conclusion in the other environment (the rhs). *)
with Proves : relation env  :=
| P_Refl :
    forall E,
      Proves E E
| P_False :
    forall E1 E2,
      Proves (envFalse E1) E2
| P_Fact_lhs :
    forall E1 E2 b t o,
      Proves E1 E2 ->
      Proves (envFact b t o E1) E2
| P_Fact_rhs :
    forall E1 E2 b t o tls,
      Proves E1 E2 ->
      UpdatedEnv E1 tls ->
      ProvesTyping tls b t o ->
      Proves E1 (envFact b t o E2)
| P_Or_rhs_l :
    forall E E1 E2,
      Proves E E1 ->
      Proves E (envOr E1 E2)
| P_Or_rhs_r :
    forall E E1 E2,
      Proves E E2 ->
      Proves E (envOr E1 E2)
| P_Or_lhs :
    forall E1 E2 E3,
      Proves E1 E3 ->
      Proves E2 E3 ->
      Proves (envOr E1 E2) E3

(* CannotProve: The lhs environment cannot prove
   the judgements in the rhs environment. *)
with CannotProve : relation env  :=
| CP_Fact :
    forall E1 E2 b t o tls,
      Proves E1 E2 ->
      UpdatedEnv E1 tls ->
      ProvesTyping tls (negb b) t o ->
      CannotProve E1 (envFact b t o E2)
| CP_Or :
    forall E E1 E2,
      CannotProve E E1 ->
      CannotProve E E2 ->
      CannotProve E (envOr E1 E2)

(* A set of 'updated' typing conclusions does or does not
   support a given typing of an object (_all_ must support 
   for true *)
with ProvesTyping : lookupset -> bool -> type -> obj -> Prop :=
| PT_Atom :
    forall t t' tl (o:obj),
      (tl o) = t' ->
      Subtype t' t ->
      ProvesTyping (tls_atom (Some tl)) true t o
| PT_Sub_Cons :
    forall tl tls t' t (o:obj),
      (tl o) = t' ->
      Subtype t' t ->
      ProvesTyping tls true t o ->
      ProvesTyping (tls_cons (Some tl) tls) true t o
| PT_FAtom :
    forall tl t o t',
      (tl o) = t' ->
      NonSubtype t' t ->
      ProvesTyping (tls_atom (Some tl)) false t o
| PT_FCons_prev :
    forall tl tls t o,
      ProvesTyping tls false t o ->
      ProvesTyping (tls_cons tl tls) false t o
| PT_FCons_new :
    forall tl tls t' t o,
      (tl o) = t' ->
      NonSubtype t' t ->
      ProvesTyping (tls_cons (Some tl) tls) false t o
| PT_False_Cons :
    forall tls b t o,
      ProvesTyping tls b t o ->
      ProvesTyping (tls_cons None tls) b t o
| PT_False_Atom :
    forall b t o,
      ProvesTyping (tls_atom None) b t o.

Ltac tryUE :=
  first [(eapply UE_Empty) | 
         (eapply UE_Fact) |
         (eapply UE_Or) |
         (eapply UE_False)].

Ltac tryULS :=
  first [(eapply ULS_Atom) |
         (eapply ULS_Cons)].

Ltac tryUL :=
  first [(eapply UL_Some) |
         (eapply UL_None)].

Ltac tryUT :=
  first [(eapply UT_T) |
         (eapply UT_NT) |
         (eapply UT_Car) |
         (eapply UT_Cdr) ].

Ltac tryRES :=
  first [(eapply RES_Bottom_l) |
         (eapply RES_Bottom_r) |
         (eapply RES_U) |
         ((eapply RES_Bottom); compute;
          match goal with
          | |- common_subtype ?t ?σ = false => compute; first [reflexivity | fail 1]
          | |- false = false => compute; reflexivity
          | |- true = false => fail 1
          | |- _ => eauto
          end) |
         ((eapply RES_NonSub); compute;
          match goal with
          | |- possible_subtype ?t ?σ = false => compute; first [reflexivity | fail 1];
            match goal with
            | |- common_subtype ?t ?σ = true => compute; first [reflexivity | fail 2]
            | |- common_subtype ?t ?σ = false => fail 1
            | |- false = true => fail 1
            | |- true = false => fail 1
            | |- _ => eauto
            end
          | |- common_subtype ?t ?σ = true => compute; first [reflexivity | fail 1]
          | |- possible_subtype ?t ?σ = true => fail 1
          | |- common_subtype ?t ?σ = false => fail 1
          | |- false = true => fail 1
          | |- true = false => fail 1
          | |- _ => eauto
          end) |
         (eapply RES_Sub)].

Ltac tryT :=
  first [(eapply T_isnum) |
        (eapply T_isproc) |
        (eapply T_isbool) |
        (eapply T_iscons) |
        (eapply T_add1) |
        (eapply T_iszero) |
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
        (eapply T_If)].
(* Removed Subsume since it always works *)  


Ltac tryS :=
  first [(eapply S_Refl) |
        (eapply S_Top) |
        (eapply S_UnionSub) |
        (eapply S_Fun) |
        (eapply S_Pair) |
        (match goal with
         | |- Subtype ?t1 (tUnion ?t1 ?t2) =>
           eapply S_UnionSuper_l
         | |- Subtype ?t2 (tUnion ?t1 ?t2) =>
           eapply S_UnionSuper_r
         | |- Subtype ?t1 (tUnion (tUnion ?t1 ?t2) ?t3) =>
           eapply S_UnionSuper_l; eapply S_UnionSuper_l
         | |- Subtype ?t2 (tUnion (tUnion ?t1 ?t2) ?t3) =>
           eapply S_UnionSuper_l; eapply S_UnionSuper_r
         | |- Subtype ?t2 (tUnion ?t1 (tUnion ?t2 ?t3)) =>
           eapply S_UnionSuper_r; eapply S_UnionSuper_l
         | |- Subtype ?t3 (tUnion ?t1 (tUnion ?t2 ?t3)) =>
           eapply S_UnionSuper_r; eapply S_UnionSuper_r
        end) |
        (eapply S_Refl)].

Ltac tryNS :=
  first [(eapply NS_Trivial) |
        (eapply NS_UnionSuper) |
        (eapply NS_UnionSub_l) |
        (eapply NS_UnionSub_r) |
        (eapply NS_Abs_arg) |
        (eapply NS_Abs_result) |
        (eapply NS_Abs_obj) |
        (eapply NS_Abs_tEnv) |
        (eapply NS_Abs_fEnv)].


Ltac tryREM :=
  first [(eapply REM_Bottom_l) |
         (eapply REM_Bottom_r) |
         (eapply REM_Union) |
         (match goal with
            | |- Removed ?t1 ?t2 ?tr =>
              assert (Subtype t1 t2) by solve [ tryS; crush ];
            match goal with
              | |- Subtype t1 t2 => fail 1
              | _ => eapply REM_Sub
            end
            | |- Removed ?t1 ?t2 ?tr =>
              assert (NonSubtype t1 t2) by solve [ tryNS; crush ];
            match goal with
              | |- NonSubtype t1 t2 => fail 1
              | _ => eapply REM_NonSub
            end
          end)].


Ltac tryP :=
  first [(eapply P_Refl) |
        (eapply P_False) |
        (eapply P_Fact_rhs) |
        (eapply P_Or_rhs_l) |
        (eapply P_Or_rhs_r) |
        (eapply P_Or_lhs) |
        (eapply P_Fact_lhs)].

Ltac tryCP :=
  first [(eapply CP_Fact) |
        (eapply CP_Or)].

Ltac tryPT :=
  first [(eapply PT_Atom) |
        (eapply PT_FAtom) |
        (eapply PT_Sub_Cons) |
        (eapply PT_False_Atom) |
        (eapply PT_False_Cons) |
        (eapply PT_FCons_new) |
        (eapply PT_FCons_prev)].

Lemma then_else_eq : forall (T:Type) (P1 P2:Prop) (test: sumbool P1 P2) (Q:T),
(if test then Q else Q) = Q.
Proof.
  crush.
Qed.
Hint Rewrite then_else_eq.

Lemma if_id_eqdec_refl : forall (T:Type) x (t1 t2: T),
(if id_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (id_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_id_eqdec_refl.

Lemma if_obj_eqdec_refl : forall (T:Type) x (t1 t2: T),
(if obj_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (obj_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_obj_eqdec_refl.

Lemma neq_id_neq : forall (T:Type) x y (P Q:T),
x <> y ->
((if (id_eqdec x y) then P else Q) = Q).
Proof.
  intros.
  destruct (id_eqdec x y); crush.
Qed.

Lemma neq_obj_neq : forall (T:Type) x y (P Q:T) pth1 pth2,
x <> y ->
((if (obj_eqdec (objπ pth1 x) (objπ pth2 y)) then P else Q) = Q).
Proof.
  intros.
  destruct (obj_eqdec (objπ pth1 x) (objπ pth2 y)); crush.
Qed.

Lemma if_type_eqdec_refl : forall (T:Type) x (t1 t2: T),
(if type_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (type_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_type_eqdec_refl.

Ltac crushTR :=
repeat (try (erewrite 
               then_else_eq 
               || erewrite if_id_eqdec_refl 
               || erewrite if_obj_eqdec_refl 
               || erewrite if_type_eqdec_refl
               || erewrite neq_obj_neq
               || erewrite neq_id_neq
               || tryUE || tryULS || tryUL || tryUT 
               || tryRES || tryREM 
               || tryT || tryS || tryNS || tryP || tryCP 
               || tryPT || eauto || crush)).
(*
Hint Constructors UpdatedEnv UpdatedLookupSet UpdatedLookup UpdatedType 
Restricted Removed Typing Subtype NonSubtype Proves CannotProve.
Hint Resolve PT_Atom PT_Sub_Cons PT_FAtom PT_FCons_prev PT_FCons_new.
*)

Theorem P_Empty : forall E,
Proves E envEmpty.
Proof with crushTR. 
  intros E.
  induction E...
Qed.
Hint Resolve P_Empty.

Inductive SimpleTypeOf : exp -> type -> Prop :=
| simpletype : forall e t tE fE o,
               Typing envEmpty e t tE fE o ->
               SimpleTypeOf e t.
Hint Constructors SimpleTypeOf.

Inductive FunctionTypeOf : exp -> type -> type -> Prop :=
| functiontype : forall e x t1 tEλ fEλ oλ t2 tE fE o,
               Typing envEmpty e (tλ x t1 tEλ fEλ oλ t2) tE fE o ->
               FunctionTypeOf e t1 t2.
Hint Constructors FunctionTypeOf.

Lemma subst_emptyeqid_tNum : forall b x y,
(subst_env (envFact b tNum (var y) envEmpty) (var x) y) =
envFact b tNum (var x) envEmpty.
Proof.
  intros b x y.
  simpl. destruct (id_eqdec y y).
  reflexivity. tryfalse.
Qed.
Hint Rewrite subst_emptyeqid_tNum.

Lemma app_envEmpty_l : forall E,
env_app envEmpty E = E.
Proof.
  intros E.
  simpl. reflexivity.
Qed.
Hint Rewrite app_envEmpty_l.

Lemma app_envEmpty_r : forall E,
env_app E envEmpty = E.
Proof.
  intros E.
  induction E.
  simpl. reflexivity.
  simpl. rewrite IHE. reflexivity.
  simpl. rewrite IHE. reflexivity.
  simpl. rewrite IHE1. rewrite IHE2. reflexivity.
Qed.
Hint Rewrite app_envEmpty_r.


Lemma empty_proves_top : forall x E,
Proves envEmpty E ->
Proves envEmpty (envFact true tTop (var x) E).
Proof with crushTR.
  intros x E HE.
  eapply P_Fact_rhs...
Qed.
Hint Resolve empty_proves_top.


Lemma top_not_union :
~ isUnion tTop.
Proof.
  intros contra; inversion contra.
Qed. 
Lemma num_not_union :
~ isUnion tNum.
Proof. intros contra; inversion contra. Qed. 
Lemma true_not_union :
~ isUnion tTrue.
Proof. intros contra; inversion contra. Qed. 
Lemma false_not_union :
~ isUnion tFalse.
Proof. intros contra; inversion contra. Qed. 
Lemma λ_not_union : forall x t tE fE o t',
~ isUnion (tλ x t tE fE o t').
Proof. intros x t tE fE o t' contra; inversion contra. Qed. 
Lemma pair_not_union : forall t1 t2,
~ isUnion (tPair t1 t2).
Proof. intros t1 t2 contra; inversion contra. Qed.
Hint Resolve top_not_union num_not_union true_not_union
false_not_union λ_not_union pair_not_union.




(*
- Add if eqdec's to crushTR
- ProvesTypings to crushTR
- Add outer match statement into CrushTR
- add to outer match statement checks for simplifications (eqdecs, simpls of env_apps, etc)
 *)

Lemma PT_empty_any : forall o,
ProvesTyping (tls_atom emptylookup) true tTop o.
Proof with crushTR.
  intros o...
Qed.  
Hint Resolve PT_empty_any.


(* Typing If statement where the if predicate/test passes
   it's conclusion to the then branch *)
Example example1:
  forall x,
    SimpleTypeOf (expIf (expApp isnum' (expVar x)) 
                        (expApp add1' (expVar x)) 
                        (expNum 0))
                 tNum.
Proof with crushTR.
  intros x; eapply simpletype...
Grab Existential Variables.
apply objnil. crush. apply objnil.
crush. apply objnil. apply objnil.
Qed.


Example example2':
  forall x,
    SimpleTypeOf
      (expIf (expApp isbool' (expVar x)) 
                   expF 
                   (expApp iszero' (expVar x)))
      tBool.
Proof with crushTR.
  intros x; eapply simpletype...
Grab Existential Variables.
apply objnil. crush. apply objnil.
crush. apply objnil. apply objnil.
Qed.

(* Typing a function of type ((U Bool Num) -> Bool)  *)
Example example2:
  forall x,
    FunctionTypeOf 
      (expλ x (tUnion tBool tNum) 
            (expIf (expApp isbool' (expVar x)) 
                   expF 
                   (expApp iszero' (expVar x))))
      (tUnion tBool tNum)
      tBool.
Proof with crushTR.
  intros x; eapply functiontype...
Grab Existential Variables.
apply objnil. crush. apply objnil.
crush. apply objnil. apply objnil.
apply objnil.
Qed.


(* Propositions from let-assignment are present in the let-body *)
Example example3:
  forall x y,
    x <> y ->
    SimpleTypeOf
      (expLet x (expApp isnum' (expVar y)) 
              (expIf (expVar x) 
                     (expVar y) 
                     (expNum 0)))
      tNum.
Proof with crushTR.
  intros x y Hneq; eapply simpletype...
Check T_Let.
  eapply (T_Let tNum tBool tNum).
Check T_App.
  eapply (T_App tBool tTop tBool tTop)...
Check T_If.
  eapply (T_If tNum tBool tNum tNum).
  tryT.
  tryP.
  tryP.
  tryP.
  tryP.
  tryP.
  tryP.
  tryP.
  crush. simpl. crush. 
  tryUE. 
  tryUE.
  tryUE.
  tryUE.
  tryUE.
  tryUE.
  tryULS.
  tryUL. crush. crush.
  tryUT.
  tryREM.
  tryNS. compute. reflexivity.
  crush. simpl. crush.
  tryUE.
  tryUE.
  tryULS.
  tryUL. crush. crush.
  tryUT.
  tryREM.
  tryNS. crush. crush.
  simpl.
  tryULS. 
  tryULS.
  tryUL.
  crush. crushTR.
  tryUT.
  tryRES.
  tryNS. compute; reflexivity.
  tryUL. crush. crushTR.
  tryUT.
  tryRES.
  tryNS. compute; reflexivity.
  simpl. crushTR. simpl.
  tryULS.
  tryULS.
  tryULS.
  tryULS.
  tryUL. crush.
  crushTR.
  tryUT.
  tryRES.
  tryNS. compute; reflexivity.
  tryUL. crush. crushTR.
  tryUT.
  tryRES.
  tryNS. compute; reflexivity.
  tryUL. crush. crush.
  tryUT. crush.
  tryRES. crush.
  tryS. tryS.
  crushTR.
  tryPT. crushTR.
  crushTR.
  tryPT.
  destruct (obj_eqdec (varx) (varx)).
  crush.
  crushTR.
  crushTR.
  tryPT. destruct (obj_eqdec (varx) (varx)).
  reflexivity. (* Right here, subgoal 2 is now Subtype tBool tFalse! *)
  tryfalse.

Grab Existential Variables.
crush.
Qed.

(* Using or predicate to identify if x is of type (U Num Bool),
   and if so calling f (the function from example 2) which takes
   (U Num Bool) 
 (Note also: the Union order is flipped, so it must use subtyping 
  to typecheck. )
 *)

Definition f' (x:id) := (expλ x (tUnion tBool tNum) 
            (expIf (expApp isbool' (expVar x)) 
                   expF 
                   (expApp iszero' (expVar x)))).

Example example4prep:
  forall x,
    SimpleTypeOf
      (expIf (expApp isnum' (expVar x)) 
             expT 
             (expApp isbool' (expVar x)))
      tBool.
Proof with crushTR.
  intros x; eapply simpletype...
  eapply T_Subsume...
Grab Existential Variables.
crush. crush.
Qed.

Example example4:
  forall x,
  SimpleTypeOf
  (expIf (expIf (expApp isnum' (expVar x)) expT (expApp isbool' (expVar x)))
         (expApp (f' x) (expVar x))
         expF)
  tBool.
Proof with crushTR.
  intros x.
  eapply simpletype.
  eapply T_If.
  eapply T_If. (* BOOKMARK *)
  crushTR.
  crushTR.
  crushTR.
  crushTR.
  crushTR.
  crushTR.
  crushTR.
  eapply T_App.
  tryT.
  eapply T_Const_isbool.
  tryT.
  tryT.
  crushTR.


  intros x; eapply simpletype...
  eapply T_Subsume...
Grab Existential Variables.
crush.
Qed.

(* usage of an and (nested ifs) to illustrate the conjunction of
   the predicates from the and being true *)
Example example7:
  forall x y,
    SimpleTypeOf
      (expIf (and' (expApp isnum' (expVar x)) (expApp isbool' (expVar y)))
             (and' (expApp iszero' (expVar x)) (expVar y))
             expF)
      tBool.

(* usage of function to identify (U Bool Num) type *)
Example example8:
  forall x,
    SimpleTypeOf 
      (expIf (expApp (expλ x tTop (* strbool? *)
                           (or' (expApp isbool' (expVar x)) 
                                (expApp isnum'  (expVar x))))
                     (expVar x))
             (expVar x)
             expT)
      (tUnion tBool tNum).


(* Results of tests on structure-accessors (car)
   for typing *)
Example example10:
  forall p,
    SimpleTypeOf
    (expIf (expApp isnum' (expApp car' p))
           (expApp add1'  (expApp car' p))
           42)
    tNum.

(* Results of tests on structure-accessors (car & cdr)
   for typing *)
Example example11:
  forall p,
    SimpleTypeOf
    (expIf (and' (expApp isnum' (expApp car' p)) (expApp isnum' (expApp cdr' p)))
           p
           (expCons (expNum 19) (expNum 84)))
    (tPair tNum tNum).


(* Reasons about the else branch of an if whose predicate is a conjuction
   and must use this to typecheck (in the else branch, if x is a bool then
   y must be a bool since it cannot be a num being that 
   (and (bool? x) (number? y)) produced #f ) *)
Example example13:
  forall x y,
    FunctionTypeOf
      (expλ y (tUnion tNum tBool) (* strbool? *)
            (expIf (and' (expApp isbool' (expVar x)) 
                         (expApp isnum'  (expVar y)))
                   (and' (expVar x) (expApp 'iszero (expVar y)))
                   (expIf (expApp isbool' (expVar x))
                          (and' (expVar x) (expVar y))
                          expF)))
      (tUnion tNum tBool) 
      (tBool).


(*
TODO -- Other theorems?

1. forall (e:exp), TypeOf e t ->
                   TypeOf e t' ->
                   (Subtype t t' \/ Subtype t' t)

2. forall (e:exp),


*)

(*
TODO - right now, there is no way to reason about the following:
If we know Proves E1 E2,
we *should* be able to say forall E1' s.t. E1' is an extension of E1,
Proves E1' E2
But we currently cannot (or it has not been proven at least and the
Proves relation doesn't indicate any obvious ways to do that)
*)

End LTR.
