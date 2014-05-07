

Set Implicit Arguments.

Require Import LibTactics.
Require Import Bool.
Require Import List.

Open Scope list_scope.

Variable id : Type.
Hypothesis id_eqdec : forall x y : id,
                       {x=y}+{x<>y}.
Hint Resolve id_eqdec.

Variable X : Type.
Hypothesis X_eqdec : forall x y : X,
                       {x=y}+{x<>y}.
Hint Resolve X_eqdec.
Hint Resolve bool_dec.

Record fact : Type := mkfact {
  fbool : bool;
  fobj : id;
  ftype : X
}.

Definition fact_neg (f:fact) : fact :=
mkfact (negb (fbool f)) (fobj f) (ftype f).

Theorem fact_eqdec : forall x y : fact,
{x=y}+{x<>y}.
Proof.
  decide equality.
Defined.
Hint Resolve fact_eqdec.

Inductive ψ : Type :=
| ψfact : fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ.

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
| ψfact f   => θfact (fact_neg f)
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