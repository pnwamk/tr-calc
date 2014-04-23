
Require Import LibTactics.
Require Import List.

Open Scope list_scope.


Section LTR.

Inductive type : Type :=
| t_super : type
| t_num   : type
| t_true  : type
| t_false : type
| t_union : list type -> type
| t_fun   : type -> type -> type. 
(* TODO:  How/where do the latent propositions and objects of a function type fit?? *)

Definition t_bool := (t_union (t_true :: t_false :: nil)).
Definition t_bottom := (t_union nil).

Inductive primop : Type :=
| add1   : primop
| iszero : primop
| isnum  : primop
| isbool : primop
| isproc : primop.

Inductive id : Type :=
  Id : nat -> id.

Inductive expr : Type :=
| e_num    : nat -> expr
| e_false  : expr
| e_true   : expr
| e_primop : primop -> expr
| e_if     : expr -> expr -> expr -> expr
| e_lam    : id -> type -> expr -> expr
| e_app    : expr -> expr -> expr
| e_id     : id -> expr.

(* TODO: Do we need Integers to represent numbers? Reals? *)

End LTR.