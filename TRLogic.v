
Require Import LibTactics.
Require Import Bool.
Require Import List.

Open Scope list_scope.

Section Logic.

Variable fact : Type.
Hypothesis fact_eqdec : forall x y : fact,
{x=y}+{x<>y}.
Variable negate_fact : fact -> fact.

Hint Resolve bool_dec.

Inductive ψ : Type :=
| ψfact : fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ.

Theorem ψ_eqdec : forall (p1 p2 : ψ),
{p1 = p2}+{p1<>p2}.
Proof.
  decide equality.
Defined.
Hint Resolve ψ_eqdec.

Inductive θ : Type :=
| θfact : fact -> θ
| θor   : θ -> θ -> θ
| θand  : θ -> θ -> θ
| θff   : θ
| θtt   : θ.

Fixpoint ψtoθ (prop:ψ) : θ :=
match prop with
| ψfact f   => θfact f
| ψimpl p q => θor (notψtoθ p) (ψtoθ q)
| ψor   p q => θor (ψtoθ p) (ψtoθ q)
| ψand  p q => θand (ψtoθ p) (ψtoθ q)
| ψff       => θff
| ψtt       => θtt
end

with notψtoθ (prop:ψ) : θ :=
match prop with
| ψfact f   => θfact (negate_fact f)
| ψimpl p q => θand (ψtoθ p) (notψtoθ q)
| ψor   p q => θand (notψtoθ p) (notψtoθ q)
| ψand  p q => θor (notψtoθ p) (notψtoθ q)
| ψff       => θtt
| ψtt       => θff
end.

Definition ψstoθs (ps:list ψ) : list θ :=
map ψtoθ ps.

Inductive Γ : Type :=
| Γempty : Γ
| Γfalse : Γ -> Γ
| Γfact  : fact -> Γ -> Γ
| Γor    : Γ -> Γ -> Γ.

Fixpoint Γapp (Γ1 Γ2:Γ) : Γ :=
match Γ1 with
| Γempty => Γ2
| Γfalse rest => Γfalse (Γapp rest Γ2)
| Γfact f rest => Γfact f (Γapp rest Γ2)
| Γor lhs rhs => Γor (Γapp lhs Γ2) (Γapp rhs Γ2)
end.

Fixpoint θtoΓ (prop:θ) : Γ :=
match prop with
| θfact f  => Γfact f Γempty
| θor p q  => Γor (θtoΓ p) (θtoΓ q)
| θand p q => Γapp (θtoΓ p) (θtoΓ q)
| θff      => Γfalse Γempty
| θtt      => Γempty
end.

Fixpoint buildΓ' (props:list θ) : Γ :=
match props with
| nil => Γempty
| p :: ps => Γapp (θtoΓ p) (buildΓ' ps)
end.

Definition buildΓ (ps:list ψ) := buildΓ' (ψstoθs ps).

Inductive Proves : Γ -> fact -> Prop :=
| P_Atom :
    forall f E,
      Proves (Γfact f E) f
| P_False :
    forall f E,
      Proves (Γfalse E) f
| P_Rest : 
    forall f f' E,
      Proves E f' ->
      Proves (Γfact f E) f'
| P_Or :
    forall E1 E2 f,
      Proves E1 f ->
      Proves E2 f ->
      Proves (Γor E1 E2) f.
Hint Constructors Proves.

Theorem Proves_dec : forall E f,
{Proves E f} + {~Proves E f}.
Proof.
  induction E.
  intros f. right.
  intros contra; inversion contra.

  intros f. left. apply P_False.

  intros f'.
  destruct (fact_eqdec f f'); subst.
  left. apply P_Atom.
  destruct (IHE f') as [Htrue | Hfalse].
  left. apply P_Rest. assumption.
  right. intros contra. inversion contra; subst. tryfalse. 
  tryfalse. 

  intros f.
  destruct (IHE1 f); destruct (IHE2 f).
  left. apply P_Or; auto.
  right. intros contra; inversion contra; subst. tryfalse.
  right. intros contra; inversion contra; subst. tryfalse.
  right. intros contra; inversion contra; subst. tryfalse.
Qed.

(* 
Proves Note!

Although negation is included in this logic in some sense - deriving
contradictions via the negation of facts is not.

This behavior can be specifically included in expandΓ if desired.

*)

(* Option used so None can represent a false environment (i.e. ff is proven) *)
Variable expandΓ : list fact -> option (list fact).
Definition fact_in (f : fact) (fs : option (list fact)) : bool := 
match fs with
| None => true
| Some facts =>
  if in_dec fact_eqdec f facts then true else false
end.

Fixpoint expProves' (f:fact) (facts:list fact) (E:Γ) : bool :=
match E with
| Γempty => fact_in f (expandΓ facts)
| Γfalse rest => true
| Γfact f rest => expProves' f (f :: facts) rest
| Γor lhs rhs => andb (expProves' f facts lhs) (expProves' f facts rhs)
end.

Definition expProves (f:fact) (E:Γ) : bool :=
expProves' f nil E.

End Logic.