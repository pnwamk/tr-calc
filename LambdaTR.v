

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
| tλ : id -> type -> env -> env -> obj -> type -> type (* function *)
| tPair :  type -> type -> type (* cons pair *)

with env : Type :=
| envNil   : env
| envFalse : env -> env
| envFact  : evidence -> env -> env
| envOr    : env -> env -> env

with evidence : Type :=
| fact : bool -> type -> obj -> evidence.
Hint Constructors type env evidence.

Hint Resolve bool_dec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with env_eqdec (x y : env) : {x=y}+{x<>y}
with evidence_eqdec (x y : evidence) : {x=y}+{x<>y}.
Proof.
  decide equality.
  decide equality.
  decide equality.
Defined.
Hint Resolve type_eqdec env_eqdec evidence_eqdec.

Fixpoint env_app (Γ1 Γ2: env) : env :=
match Γ1 with
| envNil => Γ2
| envFalse rest => envFalse (env_app rest Γ2)
| envFact f rest => envFact f (env_app rest Γ2)
| envOr lhs rhs => envOr (env_app lhs Γ2) (env_app rhs Γ2)
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
| tUnion l =>
  fold_left (fun ids next =>
               set_union id_eqdec
                         ids
                         (fv_set_t next))
            l
            nil
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

with fv_set_f (f:evidence) : set id :=
match f with
| fact b t o => set_union id_eqdec (fv_set_t t) (fv_set_o o)
end

(* free variables in the proposition environment*)
with fv_set_env (E : env) : set id :=
match E with
| envNil => nil
| envFalse rest => fv_set_env rest
| envFact f rest => set_union id_eqdec  (fv_set_f f) (fv_set_env rest)
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
| envNil => envNil
| envFalse rest => envFalse (subst_env rest o x)
| envFact (fact fb ft (objπ pth1 z)) rest => 
  match id_eq x z, set_mem id_eqdec z (fv_set_t ft) with
  | true, _ =>
    match o with
    | objnil => subst_env rest o x (* tt  - ignore *)
    | objπ pth2 y  => 
      envFact (fact fb (subst_t ft o x) (objπ (pth1 ++ pth2) y)) (subst_env rest o x)
    end
  | false, false => envFact (fact fb ft (objπ pth1 z)) (subst_env rest o x)
  | false, true => subst_env rest o x (* tt  - ignore *)
  end 
| envFact (fact fb ft objnil) rest => envFact (fact fb ft objnil) (subst_env rest o x)
| envOr lhs rhs => envOr (subst_env lhs o x) (subst_env rhs o x)
end

(* type substitution *)
with subst_t (t:type)
             (o:obj)
             (x:id) : type :=
match t with
| tUnion l => tUnion (map (fun t' => subst_t t' o x) l)
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

Definition fact_symbol (f:evidence) : option id :=
match f with
| fact b t (objπ pth x) => Some x
| _ => None
end.

Fixpoint contains_false (E:env) : bool := false. (* TODO *)


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