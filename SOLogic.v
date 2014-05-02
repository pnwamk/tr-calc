

(*
Second order logic

TODO:
1. Make this a module/section/whatever.

*)

Set Implicit Arguments.

Require Import Relations.
Require Import List.


Variable id : Type.
Hypothesis id_eqdec : forall x y : id, 
                       {x=y}+{x<>y}.
Variable X : Type.
Hypothesis X_eqdec : forall x y : X, 
                       {x=y}+{x<>y}.

Variable Merge : X -> X -> X.

Variable Sub : relation X.
Hypothesis Sub_dec : forall (x y : X), 
                     {Sub x y} + {~Sub x y}.

Inductive P : Type :=
| Valid   : X -> id -> P
| Invalid : X -> id -> P
| Implies : P -> P -> P
| Or      : P -> P -> P
| And     : P -> P -> P
| Absurd  : P
| Trivial : P.

Definition Env := list P.

Inductive Proves : Env -> P -> Prop :=
| L_Atom : 
    forall E p, 
      In p E -> Proves E p
| L_True :
    forall E, 
      Proves E Trivial
| L_False :
    forall E p, 
      Proves E Absurd ->
      Proves E p
| L_AndI :
    forall E p q, 
      Proves E p ->
      Proves E q ->
      Proves E (And p q)
| L_AndE_l :
    forall E p q r,
      Proves (p :: E) r ->
      Proves ((And p q) :: E) r
| L_AndE_r :
    forall E p q r,
      Proves (q :: E) r ->
      Proves ((And p q) :: E) r
| L_ImpI :
    forall E p q,
      Proves (p :: E) q ->
      Proves E (Implies p q)
| L_ImpE :
    forall E p q,
      Proves E p ->
      Proves E (Implies p q) ->
      Proves E q
| L_OrI_l :
    forall E p q,
      Proves E p ->
      Proves E (Or p q)
| L_OrI_r :
    forall E p q,
      Proves E q ->
      Proves E (Or p q)
| L_OrE :
    forall E p q r,
      Proves (p :: E) r ->
      Proves (q :: E) r ->
      Proves ((Or p q) :: E) r
| L_Sub :
    forall E X Y x,
      Proves E (Valid X x) ->
      Sub X Y ->
      Proves E (Valid X x)
| L_SubNot :
    forall E X Y x,
      Proves E (Invalid Y x) ->
      Sub X Y ->
      Proves E (Invalid X x)
| L_Update :
    forall E X Y x,
      Proves E (Valid X x) ->
      Proves E (Valid Y x) ->
      Proves E (Valid (Merge X Y) x)
| L_UpdateNot :
    forall E X Y x,
      Proves E (Valid X x) ->
      Proves E (Invalid Y x) ->
      Proves E (Valid (Merge X Y) x).

Theorem Proves_dec : forall E p,
{Proves E p} + {~Proves E p}.
(* TODO! *)