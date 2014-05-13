

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

Definition id_eq (x y : id) : bool :=
if id_eqdec x y then true else false.

(* Path Elements (accessors) *)
Inductive acc : Type := car | cdr.

Theorem acc_eqdec : forall (x y: acc),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve acc_eqdec.

Definition acc_eq (x y : acc) : bool :=
if acc_eqdec x y then true else false.

Definition path := list acc.

Hint Resolve list_eq_dec.
Theorem path_eqdec : forall (x y: path),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eqdec.

Definition path_eq (x y : path) : bool :=
if path_eqdec x y then true else false.

(* Objects *)
Inductive obj : Type :=
| objnil : obj
| objπ : path -> id -> obj.

Theorem obj_eqdec : forall (x y: obj),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

Definition obj_eq (x y : obj) : bool :=
if obj_eqdec x y then true else false.

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
  match id_eq x z, o2 with
  | true, objnil => objnil
  | true, objπ pth2 y => objπ (pth1 ++ pth2) y
  | false, _ => o1
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
  match id_eq x z, set_mem id_eqdec z (fv_set_t ft) with
  | true, _ =>
    match o with
    | objnil => subst_env rest o x (* tt - ignore *)
    | objπ pth2 y =>
      envFact fb (subst_t ft o x) (objπ (pth1 ++ pth2) y) (subst_env rest o x)
    end
  | false, false => envFact fb ft (objπ pth1 z) (subst_env rest o x)
  | false, true => subst_env rest o x (* tt - ignore *)
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
  if id_eq x y
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

Definition c_op_eq (x y : c_op) : bool :=
if c_op_eqdec x y then true else false.

(* Polymorphic Operations *)
Inductive p_op : Type :=
| op_car : p_op
| op_cdr : p_op.

Theorem p_op_eqdec : forall (x y : p_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve p_op_eqdec.

Definition p_op_eq (x y : p_op) : bool :=
if p_op_eqdec x y then true else false.

(* Primitive Operations *)
Inductive primop : Type :=
| prim_c : c_op -> primop
| prim_p : p_op -> primop.

Theorem primop_eqdec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eqdec.

Definition primop_eq (x y : primop) : bool :=
if primop_eqdec x y then true else false.

(* Expressions *)
Inductive exp : Type :=
| expVar : id -> exp
| expApp : exp -> exp -> exp
| expAbs : id -> type -> exp -> exp
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
| SO_Top : forall x, SubObj x objnil.
Hint Constructors SubObj.

Theorem sub_obj : forall x y,
{SubObj x y} + {~ SubObj x y}.
Proof.
  intros x y.
  destruct (obj_eqdec x y) as [Heq | Hneq].
  left; crush.
  destruct y. auto.
  right; intro contra.
  inversion contra; crush.
Defined.

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
| tλ x t1 e1 e2 o t2 => 1
| tPair t1 t2 => 1 + (typestructuralsize t1) + (typestructuralsize t2)
end.

Program Fixpoint common_subtype (type1 type2:type) 
        {measure ((typestructuralsize type1) + (typestructuralsize type2))} : bool := 
match type1, type2 with
| tTop , _ => true
| _, tTop => true
| tBottom, _ => false
| _, tBottom => false
| tNum,  tNum => true
| tNum, _ => false
| tTrue,  tTrue => true
| tTrue, _ => false 
| tFalse,  tFalse => true
| tFalse, _ => false 
| tUnion t1 t2, tUnion t3 t4 =>
  orb (common_subtype t1 t3)
      (orb (common_subtype t1 t4)
           (orb (common_subtype t2 t3)
                (common_subtype t2 t4)))           
| tUnion t1 t2, _ => orb (common_subtype t1 type2) (common_subtype t2 type2)
| _, tUnion t1 t2 => orb (common_subtype t1 type1) (common_subtype t2 type1)
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

Definition typelookup := obj -> option type.
Definition emptylookup : typelookup := fun o => None.

Definition falselookup : typelookup := (fun o : obj => Some tBottom).

Definition extend_lookup (o:obj) (t:type) (tl:typelookup) : typelookup :=
(fun o' => if obj_eq o o'
           then Some t
           else tl o').

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
| UpEnv_Empty :
    UpdatedEnv envEmpty (tls_atom emptylookup)
| UpEnv_False :
    forall E,
      UpdatedEnv (envFalse E) (tls_atom falselookup)
| UpEnv_Fact :
    forall E tlset b t o tlset',
    UpdatedEnv E tlset ->
    UpdatedLookupSet b t o tlset tlset' ->
    UpdatedEnv (envFact b t o E) tlset' 
| UpEnv_Or :
    forall E1 E2 tlset1 tlset2, 
    UpdatedEnv E1 tlset1 ->
    UpdatedEnv E2 tlset2 ->
    UpdatedEnv (envOr E1 E2) (tls_app tlset1 tlset2) 

with UpdatedLookupSet : bool -> type -> obj -> lookupset -> lookupset -> Prop :=
| UpLUS_Atom :
    forall b t o tl tl',
      UpdatedLookup b t o tl tl' ->
      UpdatedLookupSet b t o (tls_atom tl) (tls_atom tl')                    
| UpLUS_cons :
    forall b t o tl tl' tls tls',
      UpdatedLookupSet b t o tls tls' ->
      UpdatedLookup b t o tl tl' ->
      UpdatedLookupSet b t o (tls_cons tl tls) (tls_cons tl' tls')                    

with UpdatedLookup : bool -> type -> obj -> typelookup -> typelookup -> Prop :=
| UpLU :
    forall b t t' pth pth' x tl updated,
      tl (objπ pth' x) = Some t' ->
      UpdatedType t' (b, t) pth updated ->
      UpdatedLookup b t (objπ (pth ++ pth') x) tl (extend_lookup (objπ pth' x) updated tl)

with UpdatedType : type -> (bool * type) -> path -> type -> Prop :=
| UpT_Car :
    forall t v pth σ updated,
      UpdatedType t v pth updated ->
      UpdatedType (tPair t σ) v (pth ++ [car]) (tPair updated σ)
| UpT_Cdr :
    forall t v pth σ updated,
      UpdatedType σ v pth updated ->
      UpdatedType (tPair t σ) v (pth ++ [cdr]) (tPair t updated)
| UpT_T :
    forall t σ restricted,
      Restricted t σ restricted ->
      UpdatedType t (true, σ) nil restricted
| UpT_NT :
    forall t σ removed,
      Removed t σ removed ->
      UpdatedType t (false, σ) nil removed


(* TODO: update restricted/removed w/ new Union def *)
with Restricted : type -> type -> type -> Prop :=
| RES_Bottom :
    forall t σ,
      common_subtype t σ = false ->
      Restricted t σ tBottom
| RES_Bottom_Left :
    forall σ,
      Restricted tBottom σ tBottom
| RES_Bottom_Right :
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
      common_subtype t σ = true ->      
      (~isUnion t) ->
      NonSubtype t σ ->
      Restricted t σ σ

with Removed : type -> type -> type -> Prop :=
| REM_Bot :
    forall t σ,
      Subtype t σ ->
      Removed t σ tBottom
| REM_Bottom_Left :
    forall σ,
      Removed tBottom σ tBottom
| REM_Bottom_Right :
    forall t,
      Removed t tBottom t
| REM_Union :
    forall t1 t2 t1' t2' σ,
      Removed t1 σ t1' ->
      Removed t2 σ t2' ->
      Removed (tUnion t1 t2) σ (tUnion t1' t2')
| REM_nop :
    forall t σ,
      NonSubtype t σ -> 
      (~isUnion t) ->
      Removed t σ t

(* Typing Rules *)
with TypeOf : env -> exp -> type -> env -> env -> obj -> Prop :=
| Τ_Num :
    forall E n,
      TypeOf E (expNum n) tNum tt ff objnil
| T_Const_isnum :
  forall E x,
    TypeOf E 
           isnum' 
           (tλ x
               tTop
               (envFact true tNum (var x) envEmpty)
               (envFact false tNum (var x) envEmpty)
               objnil
               tBool)
           tt
           ff
           objnil
| T_Const_isproc :
  forall E x,
    TypeOf E 
           isproc' 
           (tλ x
               tTop
               (envFact true (tλ x tBottom tt ff objnil tTop) (var x) envEmpty)
               (envFact false (tλ x tBottom tt ff objnil tTop) (var x) envEmpty)
               objnil
               tBool)
           tt
           ff
           objnil
| T_Const_isbool :
  forall E x,
    TypeOf E 
           isbool' 
           (tλ x
               tTop
               (envFact true tBool (var x) envEmpty)
               (envFact false tBool (var x) envEmpty)
               objnil
               tBool)
           tt
           ff
           objnil
| T_Const_iscons :
  forall E x,
    TypeOf E 
           iscons' 
           (tλ x
               tTop
               (envFact true (tPair tTop tTop) (var x) envEmpty)
               (envFact false (tPair tTop tTop) (var x) envEmpty)
               objnil
               tBool)
           tt
           ff
           objnil
| T_Const_add1 :
  forall E x,
    TypeOf E 
           add1' 
           (tλ x
               tTop
               tt
               tt
               objnil
               tNum)
           tt
           ff
           objnil
| T_Const_iszero :
  forall E x,
    TypeOf E 
           iszero' 
           (tλ x
               tTop
               tt
               tt
               objnil
               tNum)
           tt
           ff
           objnil
| T_True :
    forall E,
      TypeOf E expT tTrue tt ff objnil
| T_False :
    forall E,
      TypeOf E expF tFalse ff tt objnil
| T_Var :
    forall E x t,
      Proves E (envFact true t (var x) envEmpty) ->
      TypeOf E
             (expVar x)
             t
             (envFact false tFalse (var x) envEmpty)
             (envFact true tFalse (var x) envEmpty)
             (var x)
| T_Abs :
   forall E σ x e t tE fE o,
     TypeOf (envFact true σ (var x) E) e t tE fE o ->
     TypeOf E
            (expAbs x σ e)
            (tλ x σ tE fE o t)
            tt
            ff
            objnil
| T_App :
   forall E e x σ tEλ fEλ oλ t tE fE o e' tE' fE' o',
     TypeOf E e (tλ x σ tEλ fEλ oλ t) tE fE o ->
     TypeOf E e' σ tE' fE' o' ->
     TypeOf E (expApp e e') (* BOOKMARK *)
            (subst_t t o' x)
            (subst_env tEλ o' x)
            (subst_env fEλ o' x)
            (subst_o oλ o' x)
| T_If :
   forall E e1 t1 tE1 fE1 o1 e2 t tE2 fE2 o e3 tE3 fE3,
     TypeOf E e1 t1 tE1 fE1 o1 ->
     TypeOf (env_app E tE1) e2 t tE2 fE2 o ->
     TypeOf (env_app E fE1) e3 t tE3 fE3 o ->
     TypeOf E (expIf e1 e2 e3) t (envOr tE2 tE3) (envOr fE2 fE3) o
| T_Subsume :
   forall E e t tE fE o tE' fE' t' o',
     TypeOf E e t tE fE o ->
     Proves (env_app E tE) tE' ->
     Proves (env_app E fE) fE' ->
     Subtype t t' ->
     SubObj o o' ->
     TypeOf E e t' tE' fE' o'
| T_Cons :
   forall E e1 t1 tE1 fE1 o1 e2 t2 tE2 fE2 o2,
     TypeOf E e1 t1 tE1 fE1 o1 ->
     TypeOf E e2 t2 tE2 fE2 o2 ->
     TypeOf E (expCons e1 e2) (tPair t1 t2) tt ff objnil
| T_Car :
   forall E e t1 t2 tE0 fE0 o o' tE fE x,
     TypeOf E e (tPair t1 t2) tE0 fE0 o ->
     tE = (subst_env (envFact false tFalse (objπ [car] x) envEmpty) o x) ->
     fE = (subst_env (envFact true tFalse (objπ [car] x) envEmpty) o x) ->
     o' = subst_o (objπ [car] x) o x ->
     TypeOf E (expApp car' e) t1 tE fE o'
| T_Cdr :
   forall E e t1 t2 tE0 fE0 o o' tE fE x,
     TypeOf E e (tPair t1 t2) tE0 fE0 o ->
     tE = (subst_env (envFact false tFalse (objπ [cdr] x) envEmpty) o x) ->
     fE = (subst_env (envFact true tFalse (objπ [cdr] x) envEmpty) o x) ->
     o' = subst_o (objπ [cdr] x) o x ->
     TypeOf E (expApp cdr' e) t2 tE fE o'
| T_Let :
   forall E e0 t tE0 fE0 o0 e1 σ tE1 fE1 o1 x,
     TypeOf E e0 t tE0 fE0 o0 ->
     TypeOf (env_app (envFact true t (var x) envEmpty)
                     (env_app (envOr (envFact true tFalse (var x) envEmpty) 
                                     tE0)
                              (envOr (envFact true tFalse (var x) envEmpty) 
                                     tE0)))
            e1 
            σ 
            tE1 
            fE1 
            o1 ->
     TypeOf E
            (expLet x e0 e1)
            (subst_t σ o0 x)
            (subst_env tE1 o0 x)
            (subst_env fE1 o0 x)
            (subst_o o1 o0 x)

(* subtyping *)
with Subtype : type -> type -> Prop :=
| ST_temp : forall t1 t2, Subtype t1 t2

(* subtype negation *)
with NonSubtype : type -> type -> Prop :=
| NST_temp : forall t1 t2, NonSubtype t1 t2

(* subtype negation *)
with Proves : env -> env -> Prop :=
| P_all : forall E1 E2, Proves E1 E2

with ProvesTyping : lookupset -> bool -> type -> obj -> Prop :=
| PT_Atom :
    forall (tl:typelookup) t o t',
      (tl o) = Some t' ->
      Subtype t t' ->
      ProvesTyping (tls_atom tl) true t o
| PT_Cons :
    forall tl tls t' t o,
      (tl o) = Some t' ->
      Subtype t t' ->
      ProvesTyping tls true t o ->
      ProvesTyping (tls_cons tl tls) true t o
| PF_Atom :
    forall tl t o t',
      (tl o) = Some t' ->
      NonSubtype t t' ->
      ProvesTyping (tls_atom tl) false t o
| PF_Cons_prev :
    forall tl tls t o,
      ProvesTyping tls false t o ->
      ProvesTyping (tls_cons tl tls) false t o
| PF_Cons_new :
    forall tl tls t' t o,
      (tl o) = Some t' ->
      NonSubtype t t' ->
      ProvesTyping (tls_cons tl tls) false t o.



(* forall τ1 ψ1 ψ1' o1 σ1 ψ2 ψ2' o2,
~(exists v, (and (TypeOf [] v τ1 ψ1 ψ1' o1)
(TypeOf [] v σ1 ψ2 ψ2' o2))) ->
This is a non positive usage of TypeOf.... *)

Inductive Proves : env -> bool -> type -> obj -> Prop
| P_Atom :
    forall f E,
      Proves (envfact f E) f
| P_False :
    forall f E,
      Proves (Γfalse E) f
| P_Cons :
    forall f f' E,
      Proves E f' ->
      Proves (Γfact f E) f'
| P_Or :
    forall E1 E2 f,
      Proves E1 f ->
      Proves E2 f ->
      Proves (Γor E1 E2) f
| P_Sub :
    forall t σ E pth x,
      Subtype t σ ->
      Proves E (fτ true t (objπ pth x)) ->
      Proves E (fτ true σ (objπ pth x))
| P_SubNeg :
    forall E t σ pth x,
      Subtype t σ ->
      Proves E (fτ false σ (objπ pth x)) ->
      Proves E (fτ false t (objπ pth x))
| P_Update :
    forall E t1 pth1 x b σ pth2 t2,
      Proves E (fτ true t1 (objπ pth1 x)) ->
      Proves E (fτ b σ (objπ (pth2 ++ pth1) x)) ->
      Update t1 (b, σ) pth2 t2 ->
      Proves E (fτ b t2 (objπ pth1 x))

with NotProves : env -> fact -> Prop
| NP_Nil :
    forall f E,
      NotProves envNil f
| NP_Cons :
    forall f E x t',
      contains_false E = false ->
      NotProves E f ->
      fact_symbol f = Some x -> (* TODO: Proving a fact with a null object...? *)
      (* And for all things proven about x in E, neither they nore their updated type are super-types
         of the type in this query, then it is not proven hear either *)


with ProvesAll : env -> env -> Prop :=
| PAll_empty :
    forall E,
      ProvesΓ E envNil
| PAll_Cons :
    forall E1 E2 f,
      Proves E1 f ->
      ProvesAll E1 E2 ->
      ProvesAll E1 (Γfact f E2)
| PΓ_Or_l :
    forall E E1 E2,
      ProvesAll E E1 ->
      ProvesAll E (Γor E1 E2)
| PΓ_Or_r :
    forall E E1 E2,
      ProvesΓ E E2 ->
      ProvesΓ E (Γor E1 E2)

with NotProvesAll : env -> env -> Prop :=

with Subtype : type -> type -> Prop :=

with NotSubtype : type -> type -> Prop :=

with Update :

with Restrict

with Remove :

with TypeOf : 


(*  TODO: Build this into the typing relation
Definition c_op_type (c : c_op) : type :=
match c with
| op_isnum =>
  (tλ X
         tTrue
         (envFact (fact true tNum (objπ [] X)) envEmpty)
         (envFact (fact false tNum (objπ [] X)) envEmpty)
         objnil
         τB)
| op_isproc =>
  (tλ X
         τT
         (envFact (fact true (τλ X τ_ ψtt ψff objnil τT) (objπ [] X)) envEmpty)
         (envFact (fact false (τλ X τ_ ψtt ψff objnil τT) (objπ [] X)) envEmpty)
         objnil
         τB)
| op_isbool =>
  (tλ X
         τT
         (envFact (fact true τB (objπ [] X)) envEmpty)
         (envFact (fact false τB (objπ [] X)) envEmpty)
         objnil
         τB)
| op_iscons =>
  (tλ X
         τT
         (envFact (fτ true (τcons τT τT) (objπ [] X)) envEmpty)
         (envFact (fτ false (τcons τT τT) (objπ [] X)) envEmpty)
         objnil
         τB)
| op_add1 =>
  (tλ X
      τN
      envEmpty
      envEmpty
      objnil
      τN)
| op_iszero =>
  (tλ X
      τN
      envEmpty
      envEmpty
      objnil
      τB)
end.
*)

End LTR.