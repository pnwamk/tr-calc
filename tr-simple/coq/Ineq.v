
Require Import CpdtTactics.
Require Import ZArith.

Local Open Scope Z_scope.

Theorem leq_equiv : forall x y : Z,
(~ x <= y) <-> (1 + y <= x).
Proof.
  split; omega.
Qed.

SearchPattern (_ * _ = _ * _).
SearchAbout Zmult.

(* l1 <= a1*x /\  a2*x <= l2 *)
Theorem elim_imp : forall l1 l2 a1 a2 x,
(a1 > 0) ->
(a2 > 0) ->
(((l1 <= a1*x) /\  (a2*x <= l2)) 
-> 
(a2*l1 <= a1*l2)).
Proof.
  intros.
  destruct H1.
  apply Z.le_trans with (m:=(a1*a2*x)). 
  rewrite Zmult_assoc_reverse.
  rewrite (Z.mul_comm a1 (a2 * x)).
  rewrite Zmult_assoc_reverse.
  rewrite (Z.mul_comm x a1).
  rewrite (Z.mul_comm a2 l1).
  rewrite (Z.mul_comm a2 (a1 * x)).
  apply Zmult_gt_0_le_compat_r; auto.
  rewrite Zmult_assoc_reverse.
  rewrite (Z.mul_comm a1 (a2 * x)).
  rewrite (Z.mul_comm a1 l2).
  apply Zmult_gt_0_le_compat_r; auto.
Qed.  