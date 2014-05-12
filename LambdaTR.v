

Require Import LibTactics.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.

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
| tUnion : list type -> type (* union *)
| tλ : id -> 
       type -> 
       (set (set fact)) -> 
       (set (set fact)) -> 
       obj -> 
       type -> type (* function *)
| tPair :  type -> type -> type (* cons pair *)

with fact : Type :=
| tfact : bool -> type -> obj -> fact.
Hint Constructors type fact.

Notation tB := (tUnion tTrue tFalse).
Notation t_ := (tUnion nil).

Hint Resolve bool_dec.

Notation env := (set (set fact)).
Definition nilenv := [ (@nil fact) ].

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with fact_eqdec (x y : fact) : {x=y}+{x<>y}.
Proof.
  decide equality.
  decide equality.
Defined.
Hint Resolve type_eqdec fact_eqdec.

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

Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y})
                       (l:list (set X)) : set X :=
match l with
| nil => nil
| x :: xs => set_union dec x (setU dec xs)
end.

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


Inductive SubstitutedProp : obj -> id -> obj -> obj -> Prop :=
| SubProp :
    forall p x o' psubtd,
    SubstitutedProp p x o' psubtd.



Definition fact_symbol (f:fact) : option id :=
match f with
| tfact b t (objπ pth x) => Some x
| _ => None
end.

Inductive isUnion : type -> Prop :=
| isU : forall ts, isUnion (tUnion ts).

Definition typelookup := obj -> option type.
Definition emptylookup : typelookup := fun o => None.
Definition extend_lookup (o:obj) (t:type) (tl:typelookup) : typelookup :=
(fun o' => if obj_eq o o'
           then Some t
           else tl o').

Definition tt := nilenv.
Definition ff := (@nil (list fact)).

Definition join_envs (e1 e2: env) : env := e1. (* TODO *)
Definition or_envs (e1 e2: env) : env := e1. (* TODO *)


Inductive UpdatedEnv : env -> set typelookup -> Prop :=
| UpEnv_Nil :
    UpdatedEnv nil nil
| UpEnv_Cons :
    forall E senv tlset tl,
      UpdatedEnv E tlset ->
      UpdatedSubEnv senv tl ->
      UpdatedEnv (senv :: E) (tl :: tlset)

with UpdatedSubEnv : set fact -> typelookup -> Prop :=
| UpSEnv_Nil :
    UpdatedSubEnv nil emptylookup
| UpSEnv_Cons :
    forall sE tl x t b t' pth pth' updated,
    UpdatedSubEnv sE tl ->
    tl (objπ pth' x) = Some t' ->
    UpdatedType t' (b, t) pth updated ->
    UpdatedSubEnv ((tfact b t (objπ (pth ++ pth') x)) :: sE) 
                  (extend_lookup (objπ pth' x) updated tl)

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

with ProvesFalse : env -> Prop :=
| FalseProven : 
    forall E, ProvesFalse E


with NoSharedValues : type -> type -> Prop :=
| NSV_NumTrue :
    NoSharedValues tNum tTrue
| NSV_NumFalse : 
    NoSharedValues tNum tFalse
| NSV_NumBottom :
    NoSharedValues tNum t_
| NSV_Numλ :
    forall x t1 p1s p2s o t2,
    NoSharedValues tNum (tλ x t1 p1s p2s o t2)
| NSV_NumPair : 
    forall t1 t2,
      NoSharedValues tNum (tPair t1 t2)
| NSV_TrueNum :
    NoSharedValues tTrue tNum
| NSV_TrueFalse : 
    NoSharedValues tTrue tFalse
| NSV_TrueBottom :
    NoSharedValues tTrue t_
| NSV_Trueλ :
    forall x t1 p1s p2s o t2,
    NoSharedValues tTrue (tλ x t1 p1s p2s o t2)
| NSV_TruePair : 
    forall t1 t2,
      NoSharedValues tTrue (tPair t1 t2)
| NSV_FalseNum :
    NoSharedValues tFalse tNum
| NSV_FalseTrue : 
    NoSharedValues tFalse tTrue
| NSV_FalseBottom :
    NoSharedValues tFalse t_
| NSV_Falseλ :
    forall x t1 p1s p2s o t2,
    NoSharedValues tFalse (tλ x t1 p1s p2s o t2)
| NSV_FalsePair : 
    forall t1 t2,
      NoSharedValues tFalse (tPair t1 t2)
| NSV_λNum :
    forall x t1 p1s p2s o t2,
    NoSharedValues (tλ x t1 p1s p2s o t2) tNum
| NSV_λTrue :
    forall x t1 p1s p2s o t2,
    NoSharedValues (tλ x t1 p1s p2s o t2) tTrue
| NSV_λFalse : 
    forall x t1 p1s p2s o t2,
    NoSharedValues (tλ x t1 p1s p2s o t2) tFalse
| NSV_λBottom :
    forall x t1 p1s p2s o t2,
    NoSharedValues (tλ x t1 p1s p2s o t2) t_
| NSV_λPair : 
    forall x t1 p1s p2s o t2 t3 t4,
    NoSharedValues (tλ x t1 p1s p2s o t2) (tPair t3 t4)
| NSV_PairNum :
    forall t1 t2,
    NoSharedValues (tPair t1 t2) tNum
| NSV_PairTrue :
    forall t1 t2,
    NoSharedValues (tPair t1 t2) tTrue
| NSV_PairFalse : 
    forall t1 t2,
    NoSharedValues (tPair t1 t2) tFalse
| NSV_PairBottom :
    forall t1 t2,
    NoSharedValues (tPair t1 t2) t_
| NSV_Pairλ :
    forall x t1 p1s p2s o t2 t3 t4,
    NoSharedValues (tPair t3 t4) (tλ x t1 p1s p2s o t2)
| NSV_BottomAll :
    forall t,
      NoSharedValues t_ t
| NSV_UnionAll :
    forall σ t ts,
    NoSharedValues (tUnion ts) σ ->
    NoSharedValues σ t ->
    NoSharedValues (tUnion (t :: ts)) σ
| NSV_AllUnion :
    forall σ t ts,
    NoSharedValues σ (tUnion ts) ->
    NoSharedValues σ t ->
    NoSharedValues σ (tUnion (t :: ts))

with Restricted : type -> type -> type -> Prop :=
| RES_Bottom :
    forall t σ,
      NoSharedValues t σ ->
      Restricted t σ t_
| RES_U_nil :
    forall σ,
      Restricted t_ σ t_
| RES_U_cons :
    forall t ts σ restricted rs p1t p1f p2t p2f o1 o2,
      (exists e, TypeOf nilenv e (tUnion (t :: ts)) p1t p1f o1 /\
                 TypeOf nilenv e σ p2t p2f o2) ->
      Restricted (tUnion ts) σ (tUnion rs) ->
      Restricted t σ restricted ->
      Restricted (tUnion (t :: ts)) σ (tUnion (restricted :: rs))
| RES_Sub :
    forall t σ o1 p1t p1f p2t p2f o2,
      (~isUnion t) ->
      Subtype t σ ->
      Restricted t σ t
| RES_NonSub :
    forall t σ p1t p1f p2t p2f o1 o2,
      (exists e, TypeOf nilenv e t p1t p1f o1 /\
                 TypeOf nilenv e σ p2t p2f o2) ->
      (~isUnion t) ->
      NonSubtype t σ ->
      Restricted t σ σ

(* bookmark - finished Restricted, moving on to Removed *)
with Removed : type -> type -> type -> Prop :=
| REM_Bot :
    forall t σ,
      Subtype t σ ->
      Removed t σ t_
| REM_U_nil :
    forall σ,
      Removed t_ σ t_
| REM_U_cons :
    forall t ts σ r rs,
      Removed (tUnion ts) σ (tUnion rs) ->
      Removed t σ r ->
      Removed (tUnion (t :: ts)) σ (tUnion (r :: rs))
| REM_nop :
    forall t σ,
      NonSubtype t σ -> 
      (~isUnion t) ->
      Removed t σ t

(* Typing Rules *)
with TypeOf :
  env -> exp -> type -> env -> env -> obj -> Prop :=
| Τ_Num :
    forall E n,
      TypeOf E (expNum n) tNum tt ff objnil
| T_Const :
    forall E c,
      TypeOf E
             (e_primop (prim_c c))
             (c_op_type c)
             tt
             ff
             objnil
| T_True :
    forall E,
      TypeOf E expTrue tTrue tt ff objnil
| T_False :
    forall E,
      TypeOf E expFalse tFalse ff tt objnil
| T_Var :
    forall E x t,
      Proves E (fact true t (objπ [] x)) ->
      TypeOf E
             (expVar x)
             t
             [[(fact false tFalse (objπ [] x))]]
             [[(fact true tFalse (objπ [] x))]]
             (obj_p [] x)
(* BOOKMARK *)
| T_Abs :
   forall E s x e t pT pF o,
     TypeOf ((ψτ true s [] x) :: E) e t pT pF o ->
     TypeOf E
            (e_abs x s e)
            (τλ x s pT pF o t)
            ψT
            ψF
            obj_nil
| T_App :
   forall E e x s pTf pFf t pT pF of o e' pT' pF' o',
     TypeOf E e (τλ x s pTf pFf of t) pT pF o ->
     TypeOf E e' s pT' pF' o' ->
     TypeOf E (e_app e e')
            (subst_t pos t o' x)
            (subst_p pos pTf o' x)
            (subst_p pos pFf o' x)
            (subst_o of o' x)
| T_If :
   forall E e1 t1 pT1 pF1 o1 e2 t pT2 pF2 o e3 pT3 pF3,
     TypeOf E e1 t1 pT1 pF1 o1 ->
     TypeOf (pT1 :: E) e2 t pT2 pF2 o ->
     TypeOf (pF1 :: E) e3 t pT3 pF3 o ->
     TypeOf E (e_if e1 e2 e3) t (ψor pT2 pT3) (ψor pF2 pF3) o
| T_Subsume :
   forall E e t pT pF o pT' pF' t' o',
     TypeOf E e t pT pF o ->
     Proves (pT :: E) pT' ->
     Proves (pF :: E) pF' ->
     SubType t t' ->
     SubObj o o' ->
     TypeOf E e t' pT' pF' o'
| T_Cons :
   forall E e1 t1 p1 p1' o1 e2 t2 p2 p2' o2,
     TypeOf E e1 t1 p1 p1' o1 ->
     TypeOf E e2 t2 p2 p2' o2 ->
     TypeOf E (e_cons e1 e2) (τcons t1 t2) ψT ψF obj_nil
| T_Car :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [car] x) o x) ->
     p' = (subst_p pos (ψτ true τf [car] x) o x) ->
     o' = subst_o (obj_p [car] x) o x ->
     TypeOf E (e_app car' e) t1 p p' o'
| T_Cdr :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [cdr] x) o x) ->
     p' = (subst_p pos (ψτ true τf [cdr] x) o x) ->
     o' = subst_o (obj_p [cdr] x) o x ->
     TypeOf E (e_app cdr' e) t2 p p' o'
| T_Let :
   forall E e0 t p0 p0' o0 e1 t' p1 p1' o1 x,
   TypeOf E e0 t p0 p0' o0 ->
   TypeOf ((ψτ true t [] x) ::
           (ψimp (ψτ false τf [] x) p0) ::
           (ψimp (ψτ true τf [] x) p0') ::
           E)
          e1
          t'
          p1
          p1'
          o1 ->
   TypeOf E
          (e_let x e0 e1)
          (subst_t pos t' o0 x)
          (subst_p pos p1 o0 x)
          (subst_p pos p1' o0 x)
          (subst_o o1 o0 x)

(* subtyping *)
with Subtype : type -> type -> Prop :=
| ST_temp : forall t1 t2, Subtype t1 t2

(* subtype negation *)
with NonSubtype : type -> type -> Prop :=
| NST_temp : forall t1 t2, NonSubtype t1 t2.





(* Typing Rules *)
with TypeOf :
  Γ -> e -> τ -> ψ -> ψ -> obj -> Prop :=
| Τ_Num :
    forall E n,
      TypeOf E (e_num n) τN ψT ψF obj_nil
| T_Const :
    forall E c,
      TypeOf E
             (e_primop (prim_c c))
             (c_op_type c)
             ψT
             ψF
             obj_nil
| T_True :
    forall E,
      TypeOf E e_true τt ψT ψF obj_nil
| T_False :
    forall E,
      TypeOf E e_false τf ψF ψT obj_nil
| T_Var :
    forall E x t,
      In (ψτ true t [] x) E ->
      TypeOf E
             (e_var x)
             t
             (ψτ false τf [] x)
             (ψτ true τf [] x)
             (obj_p [] x)
| T_Abs :
   forall E s x e t pT pF o,
     TypeOf ((ψτ true s [] x) :: E) e t pT pF o ->
     TypeOf E
            (e_abs x s e)
            (τλ x s pT pF o t)
            ψT
            ψF
            obj_nil
| T_App :
   forall E e x s pTf pFf t pT pF of o e' pT' pF' o',
     TypeOf E e (τλ x s pTf pFf of t) pT pF o ->
     TypeOf E e' s pT' pF' o' ->
     TypeOf E (e_app e e')
            (subst_t pos t o' x)
            (subst_p pos pTf o' x)
            (subst_p pos pFf o' x)
            (subst_o of o' x)
| T_If :
   forall E e1 t1 pT1 pF1 o1 e2 t pT2 pF2 o e3 pT3 pF3,
     TypeOf E e1 t1 pT1 pF1 o1 ->
     TypeOf (pT1 :: E) e2 t pT2 pF2 o ->
     TypeOf (pF1 :: E) e3 t pT3 pF3 o ->
     TypeOf E (e_if e1 e2 e3) t (ψor pT2 pT3) (ψor pF2 pF3) o
| T_Subsume :
   forall E e t pT pF o pT' pF' t' o',
     TypeOf E e t pT pF o ->
     Proves (pT :: E) pT' ->
     Proves (pF :: E) pF' ->
     SubType t t' ->
     SubObj o o' ->
     TypeOf E e t' pT' pF' o'
| T_Cons :
   forall E e1 t1 p1 p1' o1 e2 t2 p2 p2' o2,
     TypeOf E e1 t1 p1 p1' o1 ->
     TypeOf E e2 t2 p2 p2' o2 ->
     TypeOf E (e_cons e1 e2) (τcons t1 t2) ψT ψF obj_nil
| T_Car :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [car] x) o x) ->
     p' = (subst_p pos (ψτ true τf [car] x) o x) ->
     o' = subst_o (obj_p [car] x) o x ->
     TypeOf E (e_app car' e) t1 p p' o'
| T_Cdr :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [cdr] x) o x) ->
     p' = (subst_p pos (ψτ true τf [cdr] x) o x) ->
     o' = subst_o (obj_p [cdr] x) o x ->
     TypeOf E (e_app cdr' e) t2 p p' o'
| T_Let :
   forall E e0 t p0 p0' o0 e1 t' p1 p1' o1 x,
   TypeOf E e0 t p0 p0' o0 ->
   TypeOf ((ψτ true t [] x) ::
           (ψimp (ψτ false τf [] x) p0) ::
           (ψimp (ψτ true τf [] x) p0') ::
           E)
          e1
          t'
          p1
          p1'
          o1 ->
   TypeOf E
          (e_let x e0 e1)
          (subst_t pos t' o0 x)
          (subst_p pos p1 o0 x)
          (subst_p pos p1' o0 x)
          (subst_o o1 o0 x).
(* forall τ1 ψ1 ψ1' o1 σ1 ψ2 ψ2' o2,
~(exists v, (and (TypeOf [] v τ1 ψ1 ψ1' o1)
(TypeOf [] v σ1 ψ2 ψ2' o2))) ->
This is a non positive usage of TypeOf.... *)

Inductive Proves : env -> fact -> Prop
| P_Atom :
    forall f E,
      Proves (Γfact f E) f
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