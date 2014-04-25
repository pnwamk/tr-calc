
(* Formalization of the core calculi found in
   "Logical Types for Untyped Languages" 

   -Andrew Kent *)


Require Import LibTactics.
Require Import List.
Require Import Arith.
Import ListNotations.

Open Scope list_scope.


Section LTR.

Inductive id : Type :=
  Id : nat -> id.

Hint Resolve eq_nat_dec.

Theorem id_eq_dec : forall (x y : id),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eq_dec.

Definition X : id := (Id 0).

(* Path Elements *)
Inductive pe : Type :=
| car : pe
| cdr : pe.

Theorem pe_eq_dec : forall (x y: pe),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve pe_eq_dec.

Definition path := list pe.

Hint Resolve list_eq_dec.
Theorem path_eq_dec : forall (x y: path),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eq_dec.

(* Objects *)
Inductive object : Type :=
| obj_nil : object
| obj_path : path -> id -> object. 

Theorem obj_eq_dec : forall (x y: object),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eq_dec. 
Definition obj_var (v:id) : object := (obj_path nil v).

(* Types *)
Inductive type : Type :=
| t_top : type
| t_num    : type
| t_true   : type
| t_false  : type 
| t_union : list type -> type
| t_fun   : id -> type -> prop -> prop -> object -> type -> type
| t_cons  : type -> type -> type 

(* Propositions *)
with prop : Type :=
| TYPE     : type -> id -> prop
| NOT      : type -> id -> prop
| IMPL     : prop -> prop -> prop
| OR       : prop -> prop -> prop
| AND      : prop -> prop -> prop
| FALSE    : prop
| TRUE     : prop
| PATH_TYPE  : type -> path -> id -> prop
| PATH_NOT : type -> path -> id -> prop.

(* Common Type Abbreviations *)
Definition t_bool := (t_union (t_true :: t_false :: nil)).
Definition t_bottom := (t_union nil).

Fixpoint type_eq_dec (x y : type) : {x = y} + {x <> y}
with prop_eq_dec (x y : prop) : {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.
Hint Resolve type_eq_dec.
Hint Resolve prop_eq_dec.

(* Constant Operations *)
Inductive constop : Type :=
| op_add1   : constop
| op_iszero : constop
| op_isnum  : constop
| op_isbool : constop
| op_isproc : constop
| op_iscons : constop.

Theorem constop_eq_dec : forall (x y : constop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve constop_eq_dec.

(* Polymorphic Operations *)
Inductive polyop : Type :=
| op_car    : polyop
| op_cdr    : polyop.

Theorem polyop_eq_dec : forall (x y : polyop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve polyop_eq_dec.

(* Primitive Operations *)
Inductive primop : Type := 
| prim_c : constop -> primop
| prim_p : polyop -> primop.

Theorem primop_eq_dec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eq_dec.

(* Expressions *)
Inductive expr : Type :=
| e_var    : id -> expr
| e_app    : expr -> expr -> expr
| e_abs    : id -> type -> expr -> expr
| e_if     : expr -> expr -> expr -> expr
| e_primop : primop -> expr
| e_true   : expr
| e_false  : expr
| e_num    : nat -> expr
| e_cons   : expr -> expr -> expr.

Theorem expr_eq_dec : forall (x y : expr),
{x = y} + {x <> y}.
Proof. decide equality. Defined.

(* TODO: Do we need Integers to represent numbers? Reals? *)

(* Environments *)
Definition env := list prop.

(* In figure 10 ( pg 8 http://www.ccs.northeastern.edu/racket/pubs/icfp10-thf.pdf ) there are arrows without any propositions or objects accompanying them. Is this merely a type function arrow excluding tt|ff and the null object for brevity? *)

Definition constop_type (c : constop) : type :=
match c with
| op_isnum => 
  (t_fun X 
         t_top 
         (TYPE t_num X) 
         (NOT t_num X) 
         obj_nil 
         t_bool)
| op_isproc =>
  (t_fun X 
         t_top 
         (TYPE (t_fun X t_bottom TRUE FALSE obj_nil t_top) X) 
         (NOT (t_fun X t_bottom TRUE FALSE obj_nil t_top) X) 
         obj_nil 
         t_bool)
| op_isbool =>
  (t_fun X
         t_top
         (TYPE t_bool X)
         (NOT t_bool X)
         obj_nil
         t_bool)
| op_iscons =>
  (t_fun X
         t_top
         (TYPE (t_cons t_top t_top) X)
         (NOT (t_cons t_top t_top) X)
         obj_nil
         t_bool)
| op_add1 =>
  (t_fun X
         t_num
         TRUE
         FALSE
         obj_nil
         t_num)
| op_iszero =>
  (t_fun X
         t_num
         TRUE
         FALSE
         obj_nil
         t_bool)
end.

(* Substitution *)
Definition subst_o (o sub : object) (x : id) : object :=
match o with
| obj_nil => obj_nil
| obj_path p z =>
  if id_eq_dec x z
  then match sub with
       | obj_nil => obj_nil
       | obj_path p' y =>
         obj_path (p ++ p') y (* TODO verify correct *)
       end
  else o
end.

(* TODO - I'm unsure what the + and - mean in Figure 8 (pg 8) with
   regard to substitution. I thought the + and - where merely
   arbitrary characters used to differentiate symbols (e.g. as a
   convenient/intuitive subscript).  What does it mean next to a
   substitution annotation?

   ALSO TODO - What is the v? Above it's defined as a "metavariable
   ... rang[ing] over tau and not-tau (without variables)". 

   What does that mean? It is either TYPE or NOT (in this context)?
   But then what about the "without variables" comment?*)

(* BOOKMARK - currently working through the substitution
   definition on page 8, Figure 8 *)
Definition subst_p (p:prop) (sub:object) (x:id) : prop :=
match p with
| TYPE t z =>
| NOT t z =>
| IMPL P Q =>
| OR P Q => OR (subst_p P sub x) (subst_p Q sub x)
| AND P Q => AND (subst_p P sub x) (subst_p Q sub x)
| FALSE => FALSE
| TRUE => TRUE
| PATH_TYPE t p z =>
| PATH_NOT t p z =>
end.



(* Typing Rules *)
Inductive TypeOf : 
  env -> expr -> type -> prop -> prop -> object -> Prop :=
| T_Num : 
    forall E n, 
      TypeOf E (e_num n) t_num TRUE FALSE obj_nil
| T_Const : 
    forall E c,
      TypeOf E (e_primop (prim_c c)) (constop_type c) TRUE FALSE obj_nil
| T_True :
    forall E,
      TypeOf E e_true t_true TRUE FALSE obj_nil
| T_False :
    forall E,
      TypeOf E e_false t_false FALSE TRUE obj_nil
| T_Var :
    forall E x t,
      In (TYPE t x) E ->
      TypeOf E (e_var x) t (NOT t_false x) (TYPE t_false x) (obj_var x)
| T_Abs :
   forall E s x e t pT pF o,
     TypeOf (cons (TYPE s x) E) e t pT pF o ->
     TypeOf E (e_abs x s e) (t_fun x s pT pF o t) TRUE FALSE obj_nil
| T_App :
   forall E e x s pTf pFf t pT pF of o e' pT' pF' o',
     TypeOf E e (t_fun x s pTf pFf of ). 
  (* BOOKMARK - Left work here to go work out substitution details. *)
              

End LTR.