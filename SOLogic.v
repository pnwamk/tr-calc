

(*
Second order logic

TODO:
1. Make this a module/section/whatever.

*)

Set Implicit Arguments.

Require Import LibTactics.
Require Import Relations.
Require Import List.
Require Import ListSet.
Require Import Program.Wf.
Require Import LibTactics.

Open Scope list_scope.

Variable id : Type.
Hypothesis id_eqdec : forall x y : id, 
                       {x=y}+{x<>y}.
Hint Resolve id_eqdec.

Variable X : Type.
Hypothesis X_eqdec : forall x y : X, 
                       {x=y}+{x<>y}.
Hint Resolve X_eqdec.

Record fact : Type := mkFact {
  var : id;
  prop : X
}.

Theorem fact_eqdec : forall x y : fact,
{x=y}+{x<>y}.
Proof.
  decide equality.
Defined.
Hint Resolve fact_eqdec.

(*
Variable Merge : X -> X -> X.

Variable Sub : relation X.
Hypothesis Sub_dec : forall (x y : X), 
                     {Sub x y} + {~Sub x y}.
<<<<<<< HEAD
*)
Inductive P : Type :=
| Valid   : fact -> P
| Invalid : fact -> P
| Implies : P -> P -> P
| Or      : P -> P -> P
| And     : P -> P -> P
| Absurd  : P
| Trivial : P.

Theorem P_eqdec : forall p1 p2 : P,
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality.
Defined.
Hint Resolve P_eqdec.

Record Env : Type := mkEnv {
  ff_proven : bool;
  TFacts : list P;
  FFacts : list P;
  Implications : list P;
  Implied : list P;
  Disjunctions : list P
}.

Definition nil_Env := mkEnv false nil nil nil nil nil.

Definition set_false (E:Env) : Env :=
mkEnv true 
      (TFacts E) 
      (FFacts E) 
      (Implications E)
      (Implied E)
      (Disjunctions E).

Definition add2TFacts (p:P) (E:Env) : Env :=
mkEnv (ff_proven E)
      (set_add P_eqdec p (TFacts E))
      (FFacts E) 
      (Implications E)
      (Implied E)
      (Disjunctions E).

Definition add2FFacts (p:P) (E:Env) : Env :=
mkEnv (ff_proven E)
      (TFacts E) 
      (set_add P_eqdec p (FFacts E))
      (Implications E)
      (Implied E)
      (Disjunctions E).

Definition add2Impls (p:P) (E:Env) : Env :=
mkEnv (ff_proven E)
      (TFacts E) 
      (FFacts E) 
      (set_add P_eqdec p (Implications E))
      (Implied E)
      (Disjunctions E).

Definition add2Implied (p:P) (E:Env) : Env :=
mkEnv (ff_proven E)
      (TFacts E) 
      (FFacts E) 
      (Implications E)
      (set_add P_eqdec p (Implied E))
      (Disjunctions E).

Definition add2Disjs (p:P) (E:Env) : Env :=
mkEnv (ff_proven E)
      (TFacts E) 
      (FFacts E) 
      (Implications E)
      (Implied E)
      (set_add P_eqdec p (Disjunctions E)).

Definition inb {X:Type} (Xeqdec : forall x y : X, {x=y}+{x<>y}) (x:X) (l:list X) := if in_dec Xeqdec x l then true else false.

Fixpoint inEnv (prop:P) (E:Env) : bool :=
match prop with
| Valid f => inb P_eqdec prop (TFacts E)
| Invalid f => inb P_eqdec prop (FFacts E)
| Implies p q => (orb (inb P_eqdec prop (Implications E)) 
                      (inb P_eqdec prop (Implied E)))
| Or p q => inb P_eqdec prop (Disjunctions E)
| And p q => andb (inEnv p E) (inEnv q E)
| Absurd => (ff_proven E)
| Trivial => false
end.

Definition removeImpls (E:Env) : Env :=
mkEnv (ff_proven E)
      (TFacts E) 
      (FFacts E) 
      nil
      (Implied E)
      (Disjunctions E).

Fixpoint Psize (p:P) : nat :=
match p with
| Valid f => 1
| Invalid f => 1
| Implies p q => 1 + Psize p + Psize q
| Or p q => 1 + Psize p + Psize q
| And p q => 1 + Psize p + Psize q
| Absurd => 0
| Trivial => 0
end.

Definition Plistsize (props:list P) : nat :=
fold_left (fun acc p => acc + Psize p) props 0.

Definition Envsize (E:Env) : nat :=
Plistsize (TFacts E) +
Plistsize (FFacts E) +
Plistsize (Implications E) +
Plistsize (Implied E) +
Plistsize (Disjunctions E).

Program Fixpoint add2Env (props: list P) 
                         (E:Env) 
                         {measure (Plistsize props +
                                   Envsize E)} : Env :=
match props, (ff_proven E) with
| nil     , _    => E
| _       , true => E 
| prop :: ps , _    => add2Env ps 
  match prop with
  | Valid f => 
    (add2Env (Implications E)
             (add2TFacts prop 
                         (removeImpls E)))
  | Invalid f =>
    (add2Env (Implications E)
             (add2FFacts prop 
                         (removeImpls E)))
  | Implies p q =>
    if (inEnv p E)
    then (add2Env (q :: nil) (add2Implied prop E))
    else (add2Impls prop E)
  | Or p q =>
    add2Disjs prop E
  | And p q =>
    add2Env (p :: q :: nil) E
  | Absurd => set_false E
  | Trivial => E
  end
end.
Next Obligation.
Proof.
  unfold Envsize. destruct E. simpl.
  (* Bookmark *)


Inductive Proves : list P -> P -> Prop :=
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
(*
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
      Proves E (Valid (Merge X Y) x) *).
Hint Constructors Proves.

Theorem Proves_nil_dec : forall p,
{Proves nil p} + {~Proves nil p}.
Proof.
  induction p.
  right. intros contra.
  inversion contra; subst. tryfalse.
(*
Interesting. We had:

Proves nil (Valid x i)

as a hypothesis we believed was a contradiction. So we do case analysis on
the Proves relation and get:

contra : Proves nil (Valid x i)
  p : P
  H : Proves nil p
  H0 : Proves nil (Implies p (Valid x i))

Well that seems stupid - so if p is proved by nil and
p implies (Valid x i)... but wait, if p *is* (Valid x i)
then the implication is valid, and we're stuck trying to
disprove "Proves nil p" - which puts us back to square 1.

Formal example of the implication loop:
Let Γ be the empty environment and ψ1 be some proposition.
does Γ |- ψ1 ?

(1) By L-ImpE, if ψ2 -> ψ1 and Γ |- ψ2 then Γ |- ψ1.
(2) By L-Atom Γ, ψ1 |- ψ1
(3) By L-ImpI and (2) then Γ |- ψ1 -> ψ1
Excellent! Now by (1) we can see we just need to see prove 
Γ |- ψ1! And so there are an infinite number of ways to prove
anything since the rules for implication (and possibly others)
allow for looping which does not affect the actual truth state
of the universe.

You could have also just done this without picking ψ2 = ψ1
and you could be lost in an infinite loop of searching
for implicators, first trying to prove ψ1, then by the logic
above ψ2, then ψ3, etc . . .



TODO:

Where from here?

Perhaps:
1. change valid/invalid to Prop w/ bool t or f
2. adjust props
3. write algorithm that turns Γ into CNF:
http://en.wikipedia.org/wiki/Conjunctive_normal_form#Converting_from_first-order_logic
4. Simplify (and/ors w/ bools should be simple)


*)
Abort.
  
