
Require Import LibTactics.
Require Import List.

Open Scope list_scope.


Section LTR.

Inductive id : Type :=
  Id : nat -> id.

(* Objects *)
Inductive object : Type :=
| o_nil : object
| o_var  : id -> object. 

(* Types *)
Inductive type : Type :=
| t_super : type
| t_num   : type
| t_true  : type
| t_false : type
| t_union : list type -> type
| t_fun   : id -> type -> prop -> prop -> object -> type -> type

(* Propositions *)
with prop : Type :=
| p_type  : type -> id -> prop
| p_neg   : type -> id -> prop
| p_impl  : prop -> prop -> prop
| p_disj  : prop -> prop -> prop
| p_conj  : prop -> prop -> prop
| p_false : prop
| p_true  : prop.

(* Primitive Operations *)
Inductive primop : Type :=
| add1   : primop
| iszero : primop
| isnum  : primop
| isbool : primop
| isproc : primop.

(* Expressions *)
Inductive expr : Type :=
| e_var     : id -> expr
| e_app    : expr -> expr -> expr
| e_abs    : id -> type -> expr -> expr
| e_if     : expr -> expr -> expr -> expr
| e_primop : primop -> expr
| e_true   : expr
| e_false  : expr
| e_num    : nat -> expr.

(* Common Type Abbreviations *)
Definition t_bool := (t_union (t_true :: t_false :: nil)).
Definition t_bottom := (t_union nil).

(* TODO: Do we need Integers to represent numbers? Reals? *)

(* Environments *)
Definition Env := list prop.

End LTR.