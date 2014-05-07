

Set Implicit Arguments.

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

Inductive Γ : Type :=
| Γempty : Γ
| Γfalse : Γ -> Γ
| Γfact  : fact -> Γ -> Γ
| Γor    : Γ -> Γ -> Γ.
