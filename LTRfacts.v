(*
The MIT License (MIT)

Copyright (c) 2014 Andrew M. Kent

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*)

Require Import CpdtTactics.
Require Export LTRbase.
Require Export LTRutil.
Require Export LTRrel.
Import ListNotations.

Ltac howboutno :=
try(solve[right; intros contra; inversion contra; crush]).


(** Weighting for types/props *)
Fixpoint type_weight (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      2 + (plus (type_weight t1) (type_weight t2))
    | tλ x t1 t2 p _ => 2 + (type_weight t1) 
                        + (type_weight t2)
                        + (prop_weight p)
                                               
    | tPair t1 t2 => 4 + (plus (type_weight t1) (type_weight t2))
    | _ => 1
  end

with prop_weight (p:prop) : nat :=
  match p with
    | Atom (istype o t) => type_weight t
    | And P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Or P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Imp P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Truth => 0
    | Falsehood => 0
    | Unk => 0
  end.
Hint Unfold type_weight prop_weight.

Fixpoint formula_weight (f:formula) : nat :=
  match f with
    | Elem (istype o t) => type_weight t
    | Conj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Disj P Q => 1 + (formula_weight P) + (formula_weight Q)
    | Impl P Q => 1 + (formula_weight P) + (formula_weight Q)
    | TT => 0
    | FF => 0
  end.

Hint Unfold formulate' question assume.


Lemma form'_leq : forall p b1 b2,
formula_weight (formulate' b1 p) <= formula_weight (formulate' b2 p).
Proof.
  intros p.
  induction p; crush.
  specialize (IHp1 b1 b2).
  specialize (IHp2 b1 b2).
  crush.
  specialize (IHp1 b1 b2).
  specialize (IHp2 b1 b2).
  crush.
  specialize (IHp1 (negb b1) (negb b2)).
  specialize (IHp2 b1 b2).
  crush.
  destruct b1; simpl; omega.
Qed.

Lemma assume_leq_prop : forall p,
prop_weight p <= formula_weight (assume p).
Proof.
  intros p.
  unfold assume.
  induction p; crush.
  unfold formulate'.
  fold formulate'.
  remember (form'_leq p1 false true).
  crush.
Qed.

Lemma question_leq_prop : forall p,
prop_weight p <= formula_weight (question p).
Proof.
  intros p.
  unfold question.
  induction p; crush.
  unfold formulate'.
  fold formulate'.
  remember (form'_leq p1 true false).
  crush.
Qed.

Fixpoint env_weight (l:list formula) : nat :=
  match l with
    | nil => 0
    | f :: fs => (formula_weight f) + (env_weight fs)
  end.
Hint Unfold env_weight.

Definition proof_weight (p:(list formula) * formula) : nat :=
plus (env_weight (fst p)) (formula_weight (snd p)).
Hint Unfold proof_weight.


Lemma SO_dec : forall opto1 opto2,
{SubObj opto1 opto2} + {~SubObj opto1 opto2}.
Proof.
  intros.
  destruct opto2; destruct opto1; 
  try (solve[right; intros contra; inversion contra; crush]).
  destruct (obj_eqdec o o0). subst. left. apply SO_Refl.
  right; intros contra; inversion contra; crush.
  left; apply SO_Top. left; apply SO_Top.
Defined.

Lemma SO_trans : forall o1 o2 o3,
SubObj o1 o2
-> SubObj o2 o3
-> SubObj o1 o3.
Proof.
  intros.
  inversion H; inversion H0; crush.
Qed.

Lemma split_And_weight_lhs : forall L P1 P2,
proof_weight (L, P1) < proof_weight (L, P1 && P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Defined.

Lemma split_And_weight_rhs : forall L P1 P2,
proof_weight (L, P2) < proof_weight (L, P1 && P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Defined.

Lemma split_Or_weight_lhs : forall L P1 P2,
proof_weight (L, P1) < proof_weight (L, P1 || P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Defined.

Lemma split_Or_weight_rhs : forall L P1 P2,
proof_weight (L, P2) < proof_weight (L, P1 || P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Defined.
Hint Resolve split_And_weight_lhs split_And_weight_rhs 
             split_Or_weight_lhs split_Or_weight_rhs.

Definition typing (p:prop) : bool :=
match p with
  | (Atom (istype o t)) => true
  | _ => false
end.

Fixpoint types_in (o:object) (L:list formula) : list type :=
  match L with
    | nil => nil
    | (Elem (istype o' t)) :: ps => 
      if (obj_eqdec o o')
      then t :: types_in o ps
      else types_in o ps
    | _ :: ps => types_in o ps
  end.

Lemma types_in_In : forall o t L,
In t (types_in o L)
-> In (o ::= t) L.
Proof.
  intros o t L. generalize dependent o.
  generalize dependent t.
  induction L as [| p ps]; auto.
  intros t o HIn.
  simpl in HIn. destruct p;
    try (solve[right; auto]).
  destruct d as [o' t'].
  destruct (obj_eqdec o o'); subst.
  destruct HIn. subst. left; auto.
  right; auto. right; auto.
Defined.

Lemma types_in_nonnil : forall L o t,
In (Elem (istype o t)) L
-> types_in o L <> [].
Proof.
  intros L; induction L; crush.
  destruct (obj_eqdec o o). crush. crush.
  destruct a; crush; try (solve[eapply IHL; eassumption]).
  destruct d.
  destruct (obj_eqdec o o0). crush.
  apply (IHL o t); auto. 
Defined.      
   
Fixpoint type_pair_weight (tp : (type * type)) : nat :=
(type_weight (fst tp)) + (type_weight (snd tp)).

Lemma CST_dec : forall tp,
{CommonSubtype tp} + {~CommonSubtype tp}.
Proof.
  intros tp.
  induction tp as ((t1, t2),IH) 
                      using
                      (well_founded_induction
                         (well_founded_ltof _ type_pair_weight)).
  destruct (type_eqdec t1 t2).
  crush.
  remember (is_tU t1) as Ht1U.
  destruct Ht1U as [[ta tb] |]. apply is_tU_eq in HeqHt1U. subst.
  assert ({CommonSubtype (ta, t2)} + {~ CommonSubtype (ta, t2)}) as Hll.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  assert ({CommonSubtype (tb, t2)} + {~ CommonSubtype (tb, t2)}) as Hlr.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  destruct Hll. left; apply CST_lhsUnion_lhs; crush. 
  destruct Hlr. left; apply CST_lhsUnion_rhs; crush. 
  remember (is_tU t2) as Ht2U.
  destruct Ht2U as [[tc td] |]. apply is_tU_eq in HeqHt2U. subst.
  assert ({CommonSubtype ((tU ta tb), tc)} + {~ CommonSubtype ((tU ta tb), tc)}) as Hrl.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  assert ({CommonSubtype ((tU ta tb), td)} + {~ CommonSubtype ((tU ta tb), td)}) as Hrr.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  destruct Hrl. left; apply CST_rhsUnion_lhs; crush. 
  destruct Hrr. left; apply CST_rhsUnion_rhs; crush. 
  right; intros contra; inversion contra; crush.
  right; intros contra; inversion contra; crush.
  remember (is_tU t2) as Ht2U.
  destruct Ht2U as [[tc td] |]. apply is_tU_eq in HeqHt2U. subst.
  assert ({CommonSubtype (t1, tc)} + {~ CommonSubtype (t1, tc)}) as Hrl.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  assert ({CommonSubtype (t1, td)} + {~ CommonSubtype (t1, td)}) as Hrr.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  destruct Hrl. left. apply CST_rhsUnion_lhs. auto.
  destruct Hrr. left. apply CST_rhsUnion_rhs. auto.
  right; intros contra; inversion contra; crush.
  destruct t1; destruct t2; 
    try (solve[right; intros contra; inversion contra; crush |
               left; crush]).
  assert ({CommonSubtype (t1_1, t2_1)} + {~ CommonSubtype (t1_1, t2_1)}) as Hlhs.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  assert ({CommonSubtype (t1_2, t2_2)} + {~ CommonSubtype (t1_2, t2_2)}) as Hrhs.
  apply IH. unfold type_pair_weight. unfold ltof. crush.
  destruct Hlhs; destruct Hrhs; crush;
    try (solve[right; intros contra; inversion contra; crush]).
Defined.

Definition flip_pair {X:Type} (p:X*X) : X*X := ((snd p), (fst p)).
Hint Unfold flip_pair.

Ltac auto_tp_weight :=
  unfold type_pair_weight; unfold ltof; crush.

Lemma flip_eq {X:Type} : forall t1 t2 : X ,
(t1, t2) = flip_pair (t2,t1).
Proof.
  crush.
Defined.  

Lemma CST_symmetric : forall tp,
CommonSubtype tp
-> CommonSubtype (flip_pair tp).
Proof.
  intros tp H.
  induction tp as ((t1, t2),IH) 
                    using
                    (well_founded_induction
                       (well_founded_ltof _ type_pair_weight)).
  remember (is_tU t1) as Ht1U.
  destruct Ht1U as [[ta tb] |]. apply is_tU_eq in HeqHt1U. subst.
  inversion H; crush. 
  compute. apply CST_Top_lhs. 
  compute. apply CST_rhsUnion_lhs. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  compute. apply CST_rhsUnion_rhs. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  compute. apply CST_lhsUnion_lhs.
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  compute. apply CST_lhsUnion_rhs.
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  remember (is_tU t2) as Ht2U.
  destruct Ht2U as [[ta tb] |]. apply is_tU_eq in HeqHt2U. subst.
  inversion H; crush. 
  compute. apply CST_Top_rhs. 
  compute. apply CST_lhsUnion_lhs. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  compute. apply CST_lhsUnion_rhs. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
  destruct t1; destruct t2; 
  try(solve[compute; auto |
            inversion H; crush |
            right; intros contra; inversion contra; crush]).
  inversion H; subst; crush.
  apply CST_Pair. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
Defined.

Fixpoint contains_type_conflict (o:object) (t:type) (L:list formula) : opt type :=
  match L with
    | nil => None
    | (Elem (istype o' t')) :: L' =>
      if (obj_eqdec o o')
      then if CST_dec (t, t')
           then contains_type_conflict o t L'
           else Some t'
      else contains_type_conflict o t L'
    | _ :: L' => contains_type_conflict o t L'
  end.

Lemma contains_no_conflict_lhs_In : forall L o t1 t2,
In (o ::= t2) L
-> contains_type_conflict o t1 L = None
-> CommonSubtype (t1, t2).
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros o t1 t2 HIn HNone.
  destruct HIn. subst.
  unfold contains_type_conflict in HNone.
  destruct (obj_eqdec o o); try (solve[crush]).
  destruct (CST_dec (t1, t2)).
  crush. crush.
  apply (IHL' o); auto.
  simpl in HNone.
  destruct p; try (solve[crush]).
  destruct f as [o' t'].
  destruct (obj_eqdec o o'); try (solve[crush]).
  destruct (CST_dec (t1, t')); crush.
Defined.  

Lemma contains_conflict_None : forall L o t1 t2,
In (o ::= t1) L
-> contains_type_conflict o t2 L = None
-> CommonSubtype (t1, t1).
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros o t1 t2 HIn HNone.
  destruct HIn. subst.
  unfold contains_type_conflict in HNone.
  destruct (obj_eqdec o o); try (solve[crush]).
  destruct (CST_dec (t2, t1)).
  crush. crush.
Defined.  

Lemma contains_conflict_Some : forall L o t1 t2,
contains_type_conflict o t1 L = Some t2
-> ~ CommonSubtype (t1,t2).
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros o t1 t2 HSome.
  unfold contains_type_conflict in HSome.
  destruct p. destruct f as [o' t']. 
  destruct (obj_eqdec o o').
  destruct (CST_dec (t1, t')). subst.
  fold contains_type_conflict in HSome.
  apply (IHL' o'). auto.
  inversion HSome; crush.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. auto.
Defined.

Lemma contains_conflict_Some_In : forall L o t1 t2,
contains_type_conflict o t1 L = Some t2
-> In (o ::= t2) L.
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros o t1 t2 HSome.
  unfold contains_type_conflict in HSome.
  destruct p. destruct f as [o' t']. 
  destruct (obj_eqdec o o').
  destruct (CST_dec (t1, t')). subst.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  inversion HSome; crush.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
  fold contains_type_conflict in HSome.
  apply IHL' in HSome. right; auto.
Defined.


Fixpoint contains_contradiction (L:list prop) : opt (object * type * type) := 
  match L with
    | nil => None
    | (Atom (istype o t)) :: L' =>
      match contains_type_conflict o t L' with
        | None => contains_contradiction L'
        | Some t' => Some (o, t, t')
      end
    | _ :: L' => contains_contradiction L'
  end.

Lemma contains_contradiction_None : forall L,
contains_contradiction L = None 
-> (forall o t1 t2, 
      In (o ::= t1) L 
      -> In (o ::= t2) L
      -> CommonSubtype (t1, t2)).
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros HNone o t1 t2 Ht1In Ht2In.
  destruct p as [[o' t']|P1 P2|P1 P2|P1 P2| | | ].
  destruct Ht1In as [H1eq | ].
  rewrite H1eq in *.
  destruct Ht2In as [H2eq | ].
  inversion H2eq. crush.
  inversion H1eq; subst.
  unfold contains_contradiction in HNone.
  remember (contains_type_conflict o t1 L') as Hhd.
  destruct Hhd. crush.
  apply (contains_no_conflict_lhs_In L' o). auto. auto.
  destruct Ht2In as [H2eq | ].
  inversion H2eq. subst. 
  assert ((t1, t2) = (flip_pair (t2,t1))) as Hflip; crush.
  apply CST_symmetric.
  apply (contains_no_conflict_lhs_In L' o). auto. 
  destruct (contains_type_conflict o t2 L'). crush. reflexivity. 
  eapply (IHL' _ o); auto.
  crush. apply (H1 o); crush.
  crush. apply (H1 o); crush.
  crush. apply (H1 o); crush.
  crush. apply (H1 o); crush.
  crush. apply (H1 o); crush.
  crush. apply (H1 o); crush.
Grab Existential Variables.
inversion HNone.
destruct (contains_type_conflict o' t' L'); crush.
Defined.

Lemma contains_contradiction_Some : forall L o t1 t2,
contains_contradiction L = Some (o, t1, t2) 
-> (In (o ::= t1) L 
 /\ In (o ::= t2) L
 /\ ~CommonSubtype (t1, t2)).
Proof.
  intros L; induction L as [| p L'].
  crush.
  intros o t1 t2 HSome.
  inversion HSome. destruct p as [[o' t'] | | | | | |].
  remember (contains_type_conflict o' t' L') as Hsub.
  destruct Hsub.
  symmetry in HeqHsub.  
  apply contains_conflict_Some in HeqHsub.
  inversion H0; subst.
  inversion HSome.
  remember (contains_type_conflict o t1 L') as Hsubt1.
  destruct Hsubt1. inversion H1; subst.
  symmetry in HeqHsubt1.  
  apply contains_conflict_Some_In in HeqHsubt1.
  crush.
  apply IHL' in H1. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
  apply IHL' in H0. crush.
Defined.

Lemma rem_leq : forall L P,
env_weight (rem P L) <= env_weight L.
Proof.
  intros L.
  induction L.
  crush.
  intros P.
  simpl. destruct (prop_eqdec P a); crush.
Qed.

Lemma rem_add1_lt : forall L P Pbig Psmall,
In Pbig L
-> prop_weight Psmall < prop_weight Pbig
-> proof_weight ((Psmall::(rem Pbig L)), P) < proof_weight (L, P).
Proof.
  intro L.
  induction L. crush. 
  intros P Pbig Psmall HIn Hlt.
  destruct HIn. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec Pbig Pbig).
  fold rem. remember (rem_leq L Pbig). simpl in *. 
  crush. crush.
  simpl. destruct (prop_eqdec Pbig a).
  crush. unfold proof_weight. simpl. crush.
  unfold proof_weight. simpl.
  specialize (IHL P Pbig Psmall H Hlt).
  unfold proof_weight in IHL.
  simpl in *. crush.
Qed.

Lemma rem_add2_lt : forall L P Pbig Psmall1 Psmall2,
In Pbig L
-> (prop_weight Psmall1) + (prop_weight Psmall2) < prop_weight Pbig
-> proof_weight ((Psmall1::Psmall2::(rem Pbig L)), P) < proof_weight (L, P).
Proof.
  intro L.
  induction L. crush. 
  intros P Pbig Psmall1 Psmall2 HIn Hlt.
  destruct HIn. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec Pbig Pbig).
  fold rem. remember (rem_leq L Pbig). simpl in *. 
  crush. crush.
  simpl. destruct (prop_eqdec Pbig a).
  crush. unfold proof_weight. simpl. crush.
  unfold proof_weight. simpl.
  specialize (IHL P Pbig Psmall1 Psmall2 H Hlt).
  unfold proof_weight in IHL.
  simpl in *. crush.
Qed.

Lemma rem_add3_lt : forall L P Pbig Psmall1 Psmall2 Psmall3,
In Pbig L
-> (prop_weight Psmall1) + (prop_weight Psmall2) + (prop_weight Psmall3) < prop_weight Pbig
-> proof_weight ((Psmall1::Psmall2::Psmall3::(rem Pbig L)), P) < proof_weight (L, P).
Proof.
  intro L.
  induction L. crush. 
  intros P Pbig Psmall1 Psmall2 Psmall3 HIn Hlt.
  destruct HIn. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec Pbig Pbig).
  fold rem. remember (rem_leq L Pbig). simpl in *. 
  crush. crush.
  simpl. destruct (prop_eqdec Pbig a).
  crush. unfold proof_weight. simpl. crush.
  unfold proof_weight. simpl.
  specialize (IHL P Pbig Psmall1 Psmall2 Psmall3 H Hlt).
  unfold proof_weight in IHL.
  simpl in *. crush.
Defined.  


Lemma rem_ltgoal_lt : forall L P Pbig Psmall,
In Pbig L
-> prop_weight Psmall < prop_weight Pbig
-> proof_weight (((rem Pbig L)), Psmall) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec Pbig Pbig).
  fold rem. remember (rem_leq L Pbig). simpl in *. 
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec Pbig a). crush.
  unfold proof_weight in *. crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Defined.

Definition tp_weight tp := (type_weight (fst tp)) + (prop_weight (snd tp)).

Lemma subst_weight : forall (tp: type * prop) y x, 
type_weight (subst_t (fst tp) (Some (var y)) x) <= type_weight (fst tp)
/\ prop_weight (subst_p (snd tp) (Some (var y)) x) <= prop_weight (snd tp).
Proof.
  intros tp. 
    induction tp as ((t, p),IH) using
    (well_founded_induction
      (well_founded_ltof _ tp_weight)).
  intros y x.
  split.

  destruct t; crush.
  fold subst_t.
  assert (type_weight (subst_t t1 (Some (var y)) x) <= type_weight t1) as Hlhs.
    apply (IH (t1,p)). unfold ltof. unfold tp_weight. crush.
  assert (type_weight (subst_t t2 (Some (var y)) x) <= type_weight t2) as Hrhs.
    apply (IH (t2,p)). unfold ltof. unfold tp_weight. crush.
  crush.
  fold subst_t.
  assert (type_weight (subst_t t1 (Some (var y)) x) <= type_weight t1) as Hlhs.
    apply (IH (t1,p)). unfold ltof. unfold tp_weight. crush.
  assert (type_weight (subst_t t2 (Some (var y)) x) <= type_weight t2) as Hrhs.
    apply (IH (t2,p)). unfold ltof. unfold tp_weight. crush.
  crush.
  unfold subst_t. unfold subst_t'.
  fold subst_t'. fold subst_p'.
  destruct (id_eqdec x i). crush.
  fold subst_t. fold subst_p. 
  assert (type_weight (subst_t t1 (Some (var y)) x) <= type_weight t1) as H1.
    apply (IH (t1,p)). unfold ltof. unfold tp_weight. crush.
  assert (type_weight (subst_t t2 (Some (var y)) x) <= type_weight t2) as H2.
    apply (IH (t2,p)). unfold ltof. unfold tp_weight. crush.
  assert (prop_weight (subst_p p0 (Some (var y)) x) <= prop_weight p0) as H3.
    apply (IH (t1,p0)). unfold ltof. unfold tp_weight. crush.
  crush.

  destruct p as [[[π z] t']|P1 P2|P1 P2|P1 P2| | | ]; crush.
  unfold subst_p. unfold subst_p'. fold subst_t'. 
  destruct (id_eqdec x z). fold subst_t. unfold prop_weight.
  fold type_weight.
  apply (IH (t', FF)). unfold ltof. unfold tp_weight. crush.
  destruct t; crush.
  destruct (in_dec id_eqdec z (fv_set_t t')).
  destruct t'; crush.
  unfold prop_weight. fold type_weight. crush.
  fold subst_p. 
  assert (prop_weight (subst_p P1 (Some (var y)) x) <= prop_weight P1) as Hlhs.
    apply (IH (tBot,P1)). unfold ltof. unfold tp_weight. crush.
    destruct t; crush.
  assert (prop_weight (subst_p P2 (Some (var y)) x) <= prop_weight P2) as Hrhs.
    apply (IH (tBot,P2)). unfold ltof. unfold tp_weight. crush.
    destruct t; crush.
  crush.
  fold subst_p. 
  assert (prop_weight (subst_p P1 (Some (var y)) x) <= prop_weight P1) as Hlhs.
    apply (IH (tBot,P1)). unfold ltof. unfold tp_weight. crush.
    destruct t; crush.
  assert (prop_weight (subst_p P2 (Some (var y)) x) <= prop_weight P2) as Hrhs.
    apply (IH (tBot,P2)). unfold ltof. unfold tp_weight. crush.
    destruct t; crush.
  crush.
Defined.

Lemma subst_t_weight : forall t x y,
type_weight (subst_t t (Some (var y)) x) <= type_weight t.
Proof.
  intros.
  assert (t = (fst (t,FF))) as Heq. crush.
  rewrite Heq.
  apply subst_weight.
Defined.

Lemma subst_p_weight : forall p x y,
prop_weight (subst_p p (Some (var y)) x) <= prop_weight p.
Proof.
  intros.
  assert (p = (snd (tBot,p))) as Heq. crush.
  rewrite Heq.
  apply subst_weight.
Defined.


Lemma rem_λ_weight1 : forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o o',
In (Atom (istype o (tλ x1 t1a t1r p1 o1))) L
->    proof_weight
     ([Atom (istype o (subst_t t1r (Some (var x2)) x1))],
     Atom (istype o t2r)) <
   proof_weight (L, Atom (istype o' (tλ x2 t2a t2r p2 o2))).
Proof.
  intros.
  unfold proof_weight. simpl.
  induction L. crush.
  destruct a; crush.
  assert (type_weight (subst_t t1r (Some (var x2)) x1) <= type_weight t1r) as Hleq.
    apply subst_t_weight.
  crush.
Defined.

Lemma rem_λ_weight2 : forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o o',
In (Atom (istype o (tλ x1 t1a t1r p1 o1))) L
-> proof_weight
     ([Atom (istype o t2a)],
     Atom (istype o (subst_t t1a (Some (var x2)) x1))) <
   proof_weight (L, Atom (istype o' (tλ x2 t2a t2r p2 o2))).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. simpl.
  assert (type_weight (subst_t t1a (Some (var x2)) x1) <= type_weight t1a) as Hleq.
  crush.
  rewrite subst_t_weight. crush.
  crush. 
  unfold proof_weight in *. simpl in *.
  destruct a as [[o'' t''] |P1 P2|P1 P2|P1 P2| | |]; crush.
Defined.

Lemma rem_λ_weight3 : forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o o',
In (Atom (istype o (tλ x1 t1a t1r p1 o1))) L
-> proof_weight ([subst_p p1 (Some (var x2)) x1], p2) <
   proof_weight (L, Atom (istype o' (tλ x2 t2a t2r p2 o2))).
Proof.
  intros.
  induction L. crush.
  unfold proof_weight in *. simpl in *.
  destruct H. subst.
  unfold prop_weight at 3. 
  unfold prop_weight at 3. unfold type_weight.
  fold type_weight. fold prop_weight.
  assert (prop_weight (subst_p p1 (Some (var x2)) x1) <= prop_weight p1) as Hleq.
  apply subst_p_weight.
  crush.
  assert (prop_weight (subst_p p1 (Some (var x2)) x1) <= prop_weight p1) as Hleq.
  apply subst_p_weight.
  crush.
Defined.

Lemma conj_dec : forall P Q,
{P} + {~P}
-> {Q} + {~Q}
-> {P /\ Q} + {~(P /\ Q)}.
Proof. crush. Defined.

Lemma disj_dec : forall P Q,
{P} + {~P}
-> {Q} + {~Q}
-> {P \/ Q} + {~(P \/ Q)}.
Proof. crush. Defined.

Definition obj_car (o:object) : object :=
  match o with
    | obj π x => obj (π ++ [car]) x
  end.

Definition obj_cdr (o:object) : object :=
  match o with
    | obj π x => obj (π ++ [cdr]) x
  end.

Lemma tBot_In_dec : forall L,
{o | In (o ::= tBot) L} + {forall P o, In P L -> P <> (o ::= tBot)}.
Proof.
  intros L.
  remember (fun p => match p with
                     | Atom (istype o tBot) => True
                     | _ => False
                     end) as Pfun.
  assert (forall p, {Pfun p} + {~Pfun p}) as Pfun_dec.
    intros p; destruct p; crush.
    destruct f. destruct t; crush.
  destruct (find_witness _ Pfun L Pfun_dec).
  destruct s. left. destruct x; crush. destruct f. 
  destruct t; crush. exists o. auto.
  right. intros P o HIn contra.
  apply n in HIn. subst P. apply HIn.
  crush.
Defined.  

Definition get_datum (p:prop) : opt datum :=
  match p with
    | Atom f => Some f
    | _ => None
  end.

Lemma types_nil_cut : forall L o a,
types_in o (a :: L) = []
-> types_in o L = [].
Proof.
  intros L o a Hnil.
  destruct a; crush.
  destruct f.
  destruct (obj_eqdec o o0); crush.
Defined. 

Lemma types_nil_false : forall L o t,
In (Atom (istype o t)) L
-> types_in o L = []
-> False.
Proof.
  intros L; induction L. crush.
  intros o t HIn Htypes.
  inversion HIn. subst.
  unfold types_in in Htypes.
  destruct (obj_eqdec o o).
  fold types_in in Htypes. crush. crush.
  apply types_nil_cut in Htypes.
  apply (IHL _ _ H Htypes); auto.
Defined.  

Lemma Proves_dec_pair : 
  forall (goal:(list prop * prop)), 
    {Proves (fst goal) (snd goal)} + {~Proves (fst goal) (snd goal)}.
Proof.
  induction goal as ((Γ, P),IH') using
    (well_founded_induction
      (well_founded_ltof _ proof_weight)).
  assert (forall (L : list prop) (P':prop),
       ltof (list prop * prop) proof_weight (L,P') (Γ, P) ->
       {Proves L P'} + {~ Proves L P'}) as IH.
    intros L P'.
  remember (IH' (L, P')). crush.
  clear IH'.
  (* P_Axiom *)
  assert ({f | P = Atom f /\ In P Γ} 
          + {get_datum P = None \/ ~In P Γ}) as Axiom_dec.
  {
    destruct P; crush. destruct (In_dec prop_eqdec (Atom f) Γ); crush.
    left. exists f; auto.
  }
  destruct Axiom_dec as [HAxiomIn | HNoAxiom].
  {
    simpl. destruct HAxiomIn as [f [Peq PIn]]. subst. 
    left; apply P_Axiom; auto.
  }
  (* P_True *)
  destruct (prop_eqdec TT P). { subst; left; apply P_True. }
  (* P_False *)
  destruct (In_dec prop_eqdec FF Γ).
   { left; apply P_False; auto. }
  (* P_Top *)
  assert ({otp | P = ((fst otp) ::= tTop) 
          /\ In ((fst otp) ::= (snd otp)) Γ} 
          + {forall o, P = (o ::= tTop) -> 
                       types_in o Γ = nil}) as trivTop_dec.
  {
    destruct P; try(solve[right; intros o contra; inversion contra]). 
    destruct f as [o t].
    remember (types_in o Γ) as otypes. destruct otypes as [| t' otypes']. 
    right. intros o' Heq; crush. 
    assert (In t' (types_in o Γ)) as Ht'In. rewrite <- Heqotypes. left; auto. 
    apply types_in_In in Ht'In.
    destruct (type_eqdec t tTop). subst.
    left; exists (o, t'). simpl. auto.
    right. crush.
  }
  destruct trivTop_dec as [[[o t] [Peq HIn]] | noTopWitness].
    { rewrite Peq. simpl. left; apply (P_Top _ t); auto. }
  (* P_Contra *)
  remember (contains_contradiction Γ) as contra.
  symmetry in Heqcontra.
  destruct contra as [[[o t1] t2]|].
  {
    apply contains_contradiction_Some in Heqcontra.
    left; apply (P_Contradiction _ _ t1 t2 o); crush.
  }
  (* No contradictions *)
  assert (forall o t1 t2, 
            In (o ::= t1) Γ 
            -> In (o ::= t2) Γ
            -> CommonSubtype (t1, t2)) as HNoContra.
    { apply contains_contradiction_None; crush. }
  clear Heqcontra.
  (* iterative solving from Γ *)
  destruct (
    find_In_witness _ (fun a =>
      match a with
        (* P_Simpl *)
        | P1 && P2 => Proves (P1::P2::(rem (P1 && P2) Γ)) P
        (* P_DisjElim *)
        | P1 || P2 => Proves (P1::(rem (P1 || P2) Γ)) P 
                      /\ Proves (P2::(rem (P1 || P2) Γ)) P
        (* P_MP *)
        | P1 --> P2 =>  (Proves (rem (P1 --> P2) Γ) P1)
                        /\ (Proves (P1::P2::(rem (P1 --> P2) Γ)) P)
        (* P_UnionElim *)
        | Atom (istype o (tU t1 t2)) => 
          (Proves ((o ::= t1)::(rem (o ::= (tU t1 t2)) Γ)) P)
          /\ (Proves ((o ::= t2)::(rem (o ::= (tU t1 t2)) Γ)) P)
        (* P_PairElim *)
        | Atom (istype (obj π x) (tPair t1 t2)) => 
          Proves (((obj π x) ::= tCons)
                     ::((obj (π ++ [car]) x) ::= t1)
                     ::((obj (π ++ [cdr]) x) ::= t2)
                     ::(rem ((obj π x) ::= (tPair t1 t2)) Γ)) P
        (* P_Bot *)
        | Atom (istype o tBot) => True
        (* P_Fun *)
        | Atom (istype o (tλ x1 t1a t1r p1 o1)) =>
          match P with
            | Atom (istype o' (tλ x2 t2a t2r p2 o2)) =>
              o = o'
              /\ Proves [(o ::= (subst_t t1r (Some (var x2)) x1))] (o ::= t2r)
              /\ Proves [(o ::= t2a)] (o ::= (subst_t t1a (Some (var x2)) x1))
              /\ Proves [(subst_p p1 (Some (var x2)) x1)] p2
              /\ SubObj (subst_o o1 (Some (var x2)) x1) o2
             | _ => False
          end
        | _ => False
      end
    ) Γ) as [(a,(HaA,HaB))|antecedent_nonexist].
  { (* Prove decidability of decision procedure *)
    intros a HIn.
    destruct a as [[[π x] t]|P1 P2 |P1 P2|P1 P2| | |]; try (solve[auto]).
    - destruct t as [ | | | | | |t1 t2|t1 t2| |x1 t1a t1r p1 o1]; 
      try (solve[auto]).
      + apply conj_dec; apply IH; unfold ltof; apply rem_add1_lt; crush.
      + apply IH; unfold ltof; apply rem_add3_lt; crush.
      + destruct P as [[o' t]| | | | | |]; try(solve[right; auto]).
        destruct t; try(solve[right; auto]).
        apply conj_dec. apply obj_eqdec.
        apply conj_dec. apply IH. unfold ltof. eapply rem_λ_weight1. exact HIn. 
        apply conj_dec. apply IH. unfold ltof. eapply rem_λ_weight2. exact HIn.
        apply conj_dec. apply IH. unfold ltof. eapply rem_λ_weight3. exact HIn.
        apply SO_dec.
    - apply IH; unfold ltof; apply rem_add2_lt; crush.
    - apply conj_dec; apply IH; unfold ltof; apply rem_add1_lt; crush.
    - apply conj_dec; apply IH; 
      first[apply rem_ltgoal_lt | apply rem_add2_lt]; crush.
  }
{ (* antecedent proves *)
  left. destruct a as [[[π x] t] |P1 P2|P1 P2|P1 P2| | | ].
  clear HNoAxiom.
  + destruct t as [ | | | | | | |t1 t2|t1 t2| ]; try(solve[crush]).
    eapply P_Bot; eauto.
    eapply (P_UnionElim _ P t1 t2); crush. exact HaA. auto. auto.
    eapply (P_PairElim _ _ t1 t2); crush. exact HaA. auto. 
    destruct P as [[o' t] | | | | | | ]; crush.
    destruct t; crush.
    eapply P_Fun. eassumption. auto. auto. auto. auto.
  + apply (P_Simpl _ _ P1 P2); crush.
  + apply (P_DisjElim _ _ P1 P2); crush.
  + apply (P_MP _ _ P1 P2); crush.
  + crush. 
  + crush.
  + crush. 
}
{ (* antecedent cannot prove *)
  remember
      (match P with
      (* P_Conj *)
      | PA && PB  => Proves Γ PA /\ Proves Γ PB
      (* P_Add_[lhs/rhs] *)
      | PA || PB  => Proves Γ PA \/ Proves Γ PB
      (* P_CP *)
      | PA --> PB => Proves (PA::Γ) PB
      (* P_Top *)
      | (Atom (istype o tTop)) => types_in o Γ <> nil
      (* P_UnionElim *)
      | (Atom (istype o (tU t1 t2))) =>
        Proves Γ (o ::= t1) \/ Proves Γ (o ::= t2)
      (* P_PairElim *)
      | (Atom (istype o (tPair t1 t2))) =>
        Proves Γ ((obj_car o) ::= t1)
        /\ Proves Γ ((obj_cdr o) ::= t2)
        /\ Proves Γ (o ::= tCons)
      | _ => False
    end) as succedent.
assert (succedent_dec: {succedent} + {~succedent}).
{
 subst.
 clear HNoAxiom.
 destruct P as [[o t] |P1 P2|P1 P2|P1 P2| | |]; try (solve[auto]).
 destruct t as [ | | | | | | | | | x2 t2a t2r p2 o2 ]; 
   try (solve[auto | 
              apply (In_dec prop_eqdec (Atom (istype o _)) Γ)]).
  apply disj_dec; apply IH; unfold ltof; unfold proof_weight; crush.
  apply conj_dec; first[apply IH | apply conj_dec; apply IH]; 
    unfold ltof; unfold proof_weight; crush.
  apply conj_dec; apply IH; unfold ltof; crush.
  apply disj_dec; apply IH; unfold ltof; crush.
  apply IH; unfold ltof; crush. unfold proof_weight. crush. 
}
  subst.
  destruct succedent_dec as [HSucc | HNoSucc].
{ (* succedent provable *)
  left.
  destruct P as [[o t]|P1 P2|P1 P2|P1 P2| | | ]; try (solve[crush]).
  destruct t; try (solve[apply P_Axiom; crush]).
  destruct HSucc. apply P_Union_lhs. auto. apply P_Union_rhs. auto. 
  destruct o. unfold obj_car in HSucc. unfold obj_cdr in HSucc. 
    apply P_Pair; crush.
  apply P_Conj; crush.
  destruct HSucc. apply P_Add_lhs; auto.
    apply P_Add_rhs; auto.
  apply P_CP; auto.
}
{ (* succedent not provable *)
  right.
  clear IH.
  intros Hprf.
  simpl in Hprf.
  induction Hprf as 
      [ Γ f HAtomIn | (* P_Axiom *)
        Γ P t1 t2 o Ht1In Ht2In HNoCST | (* P_Contradiction *)
        Γ P t1 t2 [π x] HIn HlhsPrf HrhsPrf | (* P_UnionElim *)
        Γ P t1 t2 π x HIn HPrf | (* P_PairElim *)
        Γ t o HIn | (* P_Top *)
        Γ t1 t2 o Ht1Prf | (* P_Union_lhs *)
        Γ t1 t2 o Ht2Prf | (* P_Union_rhs *)
        Γ t1 t2 π x HcarPrf HcdrPrf HconsPrf | (* P_Pair *)
        Γ x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 [π x] 
          HIn HretPrf HargPrf HpropPrf HSO| (* P_Fun *)
        Γ P [π x] HIn | (* P_Bot *)
        Γ | (* P_True *)
        Γ P | (* P_False *)
        Γ R P Q HIn Hprf | (* P_Simpl *)
        Γ R P Q HIn Hprf1 Hprf2 | (* P_DisjElim *)
        Γ R P Q HIn Hprf1 Hprf2 | (* P_MP *)
        Γ P Q HIn Hprf1 Hprf2 | (* P_Conj *)
        Γ P Q Hprf | (* P_Add_lhs *)
        Γ P Q Hprf | (* P_Add_rhs *)
        Γ P Q Hprf] (* P_CP *);
    try(solve[apply (antecedent_nonexist _ HIn); auto |
              apply HNoSucc; auto |
              crush]). 
  + apply HNoCST. apply (HNoContra o); auto.  
  + eapply types_nil_false. exact HIn. apply noTopWitness. auto.
} }
Defined.

Theorem P_ModusPonens : forall L P Q,
Proves L P
-> Proves L (P-->Q)
-> Proves L Q.
Proof. Admitted.

Theorem P_HypSyl : forall L P Q R,
Proves L (P --> Q)
-> Proves L (Q --> R)
-> Proves L (P --> R).
Proof.
  intros.
  apply P_CP.
  assert (Proves (P::L) P).
  


Theorem P_Cut : forall E P Q,
Proves E Q
-> Proves (P::E) Q.
Proof.
  intros E P Q HP. generalize dependent P.
  induction HP.
  intros P.
  apply P_Axiom. crush.
  intros P'.
  apply P_Contradiction with (t1:=t1) (t2:=t2) (o:=o); crush.
  intros P'.
  apply P_UnionElim with (t1:=t1) (t2:=t2) (o:=o); auto.
  right. auto. 
  destruct (prop_eqdec P' (Atom (istype o (tU t1 t2)))).
  subst. unfold rem. 
  destruct  (prop_eqdec (Atom (istype o (tU t1 t2)))
                        (Atom (istype o (tU t1 t2)))).
  subst.


feapply IHHP1.

  (*  *)


Definition P_dec : forall Γ P,
{Proves Γ P} + {~Proves Γ P}.
Proof.
  intros Γ P.
  remember (Proves_dec_pair (Γ, P)) as H.
  crush.
Defined.

Theorem ST_dec : forall t1 t2,
{Subtype t1 t2} + {~Subtype t1 t2}.
Proof.
  intros t1 t2.
  unfold Subtype. apply P_dec.
Defined.

Ltac solve_it :=
  match goal with 
    | |- Proves ?L ?P =>
      let provability := constr:(P_dec L P) in
      let proof := eval vm_compute in provability in
      match proof with
        | left ?prf => exact prf
        | right _ => fail
      end
    | |- Subtype ?t1 ?t2 =>
      let provability := constr:(ST_dec t1 t2) in
      let proof := eval vm_compute in provability in
      match proof with
        | left ?prf => exact prf
        | right _ => fail
      end
    | |- SubObj ?o1 ?o2 =>
      let provability := constr:(SO_dec o1 o2) in
      let proof := eval vm_compute in provability in
      match proof with
        | left ?prf => exact prf
        | right _ => fail
      end
  end.

Lemma subst_o_eq_id : forall o x,
(subst_o o (Some (var x)) x) = o.
Proof.
  intros o x.
  destruct o; crush.
  destruct o. destruct (id_eqdec i x); crush.
  rewrite app_nil_r. auto.
Qed.

(* Lemma subst_t_eq_id : forall t x, *)
(* (subst_t t (Some (var x)) x) = t *)
(* with subst_p_eq_id : forall p x, *)
(* (subst_p p (Some (var x)) x) = p. *)
(* Proof. *)
(*   clear subst_t_eq_id. *)
(*   intros. *)
(*   induction t; crush. *)
(*   unfold subst_t. unfold subst_t'. *)
(*   fold subst_t'. fold subst_t. crush. *)
(*   unfold subst_t. unfold subst_t'. *)
(*   fold subst_t'. fold subst_t. crush. *)
(*   unfold subst_t. unfold subst_t'. *)
(*   destruct (id_eqdec x i). auto.  *)
(*   fold subst_p'. *)
(*   fold subst_t'. fold subst_t.  *)
(*   rewrite subst_o_eq_id.  *)
(*   rewrite (subst_p_eq_id p). *)
(*   rewrite IHt1. rewrite IHt2. *)
(*   auto. *)

(*   clear subst_p_eq_id. *)
(*   intros. *)
(*   induction p; crush. *)
(*   destruct f. *)
(*   unfold subst_p. unfold subst_p'. *)
(*   fold subst_t'. fold subst_t.  *)
(*   destruct o as [π z]. *)
(*   destruct (id_eqdec x z).  *)
(*   rewrite app_nil_r.  *)
(*   rewrite (subst_t_eq_id t x). crush. *)
(*   destruct (in_dec id_eqdec z (fv_set_t t)). *)
(*   unfold subst_t. unfold subst_t'. *)
(*   fold subst_t'. fold subst_t. crush. *)
(*   unfold subst_t. unfold subst_t'. *)
(*   destruct (id_eqdec x i). auto.  *)
(*   fold subst_p'. *)
(*   fold subst_t'. fold subst_t.  *)
(*   rewrite subst_o_eq_id.  *)
(*   rewrite (subst_p_eq_id p). *)
(*   rewrite IHt1. rewrite IHt2. *)
(*   auto. *)

(*   intros t x. *)

(* Lemma S_Refl : forall t, *)
(* Subtype t t. *)
(* Proof. *)
(*   intros. *)
(*   induction t. *)
(*   solve_it. solve_it. solve_it. solve_it. *)
(*   solve_it. solve_it. solve_it. *)
(*   unfold Subtype. *)
(*   apply (P_UnionElim _ _ t1 t2 (var (Id 0))). *)
(*   crush. apply P_Union_lhs. apply P_Axiom. crush. *)
(*   apply P_Union_rhs. apply P_Axiom. crush. *)
(*   unfold Subtype. *)
(*   apply (P_PairElim _ _ t1 t2 [] (Id 0)). *)
(*   crush. apply P_Pair. apply P_Axiom. crush. *)
(*   apply P_Axiom. crush. apply P_Axiom. crush. *)
(*   unfold Subtype. *)
(*   apply (P_Fun _ i t1 t2 p o). crush. *)
(*   crush. apply P_Pair. apply P_Axiom. crush. *)
(*   apply P_Axiom. crush. apply P_Axiom. crush. *)

(*   apply P_Union_rhs. apply P_Axiom. crush. *)

(*   auto. *)
(*   solve_it. *)
(*   simpl. *)


Lemma proves_TT2 :
Proves [] TT.
Proof.
  solve_it.
Defined.


Lemma proves_ex :
let x := (Id 0) in
Proves [(var x ::= tNat)] (var x ::= (tU tNat tBool)).
Proof.
  simpl.
  solve_it.
Defined.
Print proves_ex.


Lemma proves_simple1 : 
Proves [((var (Id 0)) ::= tNat)] (((var (Id 0)) ::= tTop) || ((var (Id 0)) ::= tBot)).
Proof.
  solve_it.
Qed.

Lemma proves_simple2 : 
Proves [((var (Id 0)) ::= tNat);
       (((var (Id 0)) ::= tNat) 
          --> (((var (Id 1)) ::= tNat) 
                 || ((var (Id 1)) ::= tBool)));
       ((((var (Id 1)) ::= tT) 
          || ((var (Id 1)) ::= tF))
          --> ((var (Id 2)) ::= tStr))] 
       (((var (Id 0)) ::= tNat) 
          && (((var (Id 1)) ::= tNat) || (((var (Id 2)) ::= tStr)
                                            && ((var (Id 1)) ::= tBool)))).
Proof.
  solve_it.
Qed.
Print proves_simple2.

Theorem optobj_eqdec : forall o1 o2 : opt object,
{o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
Qed.

Ltac right_fail := solve[right; intros contra; inversion contra; crush].

Inductive ObjJoin : (opt object * opt object) -> opt object -> Prop :=
| ojoin : forall o1 o2 omin,
            SubObj o1 omin
            -> SubObj o2 omin
            ->(forall o',
              SubObj o1 o' /\ SubObj o2 o' ->
              SubObj omin o')
                -> ObjJoin (o1,o2) omin.

Hint Constructors SubObj.

Theorem min_supo : forall o1 o2,
{omin | ObjJoin (o1,o2) omin}.
Proof.
  intros o1 o2.
  destruct (optobj_eqdec o1 None).
  exists None. subst. apply ojoin; crush. 
  destruct (optobj_eqdec o2 None).
  exists None. subst. apply ojoin; crush. 
  destruct (optobj_eqdec o1 o2). subst.
  exists o2. apply ojoin; crush.
  exists None; apply ojoin; crush.
  inversion H0; crush.
  inversion H1; crush.
Qed.  

Theorem ObjJoin_unique : forall o1 o2 oa ob,
ObjJoin (o1,o2) oa
-> ObjJoin (o1,o2) ob
-> oa = ob.
Proof.
  intros o1 o2 oa ob Hoa Hob.
  inversion Hoa as [a b c HSOa1 HSOa2 HUa]; subst.
  inversion Hob as [a b c HSOb1 HSOb2 HUb]; subst.
  inversion HSOa1; subst.
  inversion HSOa2; subst.
  inversion HSOb1; subst. auto.
  specialize (HUb oa (conj HSOa1 HSOa2)).
  inversion HUb; subst. auto. auto.
  inversion HSOa2; subst.
  inversion HSOb1; subst. auto. auto.
  inversion HSOb2; subst; auto.
  inversion HSOb1; subst. auto. auto.
  specialize (HUa ob (conj HSOb1 HSOb2)).
  inversion HUa; subst. auto. auto.
Qed.

Definition prim_poly (e:exp) : bool :=
match e with
| eOp (p_op _ ) => true
| _ => false
end.

Definition car_obj (o:object) : object :=
  match o with
    | obj π x => obj (car::π) x
  end.

Definition cdr_obj (o:object) : object :=
  match o with
    | obj π x => obj (car::π) x
  end.

Definition c_λobj (c:const_op) : opt object :=
  match (const_type c) with
    | tλ x t1 t2 p opto => opto
    | _ => None
  end. 


Fixpoint exp_obj (e:exp) : opt object :=
match e with
| eNat n => None
| eTrue => None
| eFalse => None
| eStr _ => None
| eVar x => Some (var x)
| eTVar x t => Some (var x)
| eOp o => None
| eIf e1 e2 e3 =>
  let o2 := exp_obj e2 in
  let o3 := exp_obj e3 in
  proj1_sig (min_supo o2 o3)
| eλ _ _ _ => None
| eLet x xexp bexp =>
  let o0 := exp_obj xexp in
  let o1 := exp_obj bexp in
  subst_o o1 o0 x
| eCons lhs rhs => None
| eApp efun earg =>
  let o' := exp_obj earg in
  match efun with
    | (eOp (c_op c)) => 
      let fo := (c_λobj c) in
      let x := (Id 0) in
      subst_o fo o' x
    | (eOp (p_op opCar)) =>
      let x := (Id 0) in
      subst_o (Some (obj [car] x)) o' x
    | (eOp (p_op opCdr)) =>
      let x := (Id 0) in
      subst_o (Some (obj [car] x)) o' x
    | λ x t2 body =>
      let fo := (exp_obj body) in
      subst_o fo o' x      
    | _ => None
  end
end.

Definition c_λprop (c:const_op) : prop :=
  match (const_type c) with
    | tλ x t1 t2 p opto => p
    | _ => FF
  end. 

Fixpoint exp_prop (e:exp) : prop :=
match e with
| eNat n => TT
| eTrue => TT
| eFalse => FF
| eStr _ => TT
| eVar x => (var x ::~ tF)
| eTVar x t => ((var x ::= t) && (var x ::~ tF))
| eOp o => TT
| eIf e1 e2 e3 =>
  let p1 := exp_prop e1 in
  let p2 := exp_prop e2 in
  let p3 := exp_prop e3 in
  ((p1 && p2) || ((Not p1) && p3))
| eλ _ _ _ => TT
| eLet x xexp bexp =>
  (subst_p (exp_prop bexp) (exp_obj xexp) x)
| eCons lhs rhs => TT
| eApp efun earg =>
  let o := exp_obj earg in
  match efun with
    | (eOp (c_op c)) => 
      let fp := (c_λprop c) in
      let x := (Id 0) in
      subst_p fp o x
    | (eOp (p_op opCar)) =>
      let x := (Id 0) in
      subst_p ((obj [car] x) ::~ tF) o x
    | (eOp (p_op opCdr)) =>
      let x := (Id 0) in
      subst_p ((obj [cdr] x) ::~ tF) o x
    | λ x t1 body =>
      let fp := (exp_prop body) in
      subst_p fp o x      
    | _ => FF
  end
end.

(** ** TypeOf *)

Inductive TypeOf : list prop -> exp -> type -> Prop :=
| T_Nat :
    forall Γ n t,
      Subtype tNat t
      -> TypeOf Γ (#n) t
| T_Str :
    forall Γ s t,
      Subtype tStr t
      -> TypeOf Γ (Str s) t
| T_Const :
    forall Γ c t,
      Subtype (const_type c) t
      -> TypeOf Γ (eOp (c_op c)) t
| T_True :
    forall Γ t,
      Subtype tT t
      -> TypeOf Γ #t t
| T_False :
    forall Γ t,
      Subtype tF t
      -> TypeOf Γ #f t
| T_Var :
    forall Γ x t,
      Proves Γ ((var x) ::= t)
      -> TypeOf Γ ($ x) t
| T_TVar :
    forall Γ x xt t,
      Proves Γ ((var x) ::= xt)
      -> Subtype xt t
      -> TypeOf Γ (t$ x xt) t
| T_Abs :
    forall Γ x t1 e t2 t,
      TypeOf (((var x) ::= t1)::Γ) e t2
      -> Subtype (tλ x t1 t2 (exp_prop e) (exp_obj e)) t
      -> TypeOf Γ (eλ x t1 e) t
| T_App :
    forall Γ e e' t1 t2 x,
      TypeOf Γ e (tλ x t1 t2 (exp_prop e) (exp_obj e))
      -> TypeOf Γ e' t1
      -> TypeOf Γ (Apply e e') t2
| T_If : 
    forall Γ e1 e2 e3 t t1 t2 t3,
      TypeOf Γ e1 t1
      -> TypeOf ((exp_prop e1)::Γ) e2 t2
      -> TypeOf ((Not (exp_prop e1))::Γ) e3 t3
      -> Subtype t2 t
      -> Subtype t3 t
      -> TypeOf Γ (If e1 e2 e3) t
| T_Cons :
    forall Γ e1 e2 t1 t2 t,
      TypeOf Γ e1 t1
      -> TypeOf Γ e2 t2
      -> Subtype (tPair t1 t2) t
      -> TypeOf Γ (Cons e1 e2) t
| T_Car :
    forall Γ e t1 t2 t,
      TypeOf Γ e (tPair t1 t2)
      -> Subtype t1 t
      -> TypeOf Γ (Car e) t
| T_Cdr :
    forall Γ e t1 t2 t,
      TypeOf Γ e (tPair t1 t2)
      -> Subtype t2 t
      -> TypeOf Γ (Cdr e) t
| T_Let :
    forall Γ x e0 e1 t0 t1 t,
      TypeOf Γ e0 t0
      -> TypeOf (((var x) ::= t0)
                   ::(((var x) ::~ tF) --> (exp_prop e0))
                   ::(((var x) ::= tF) --> (Not (exp_prop e0)))
                   ::Γ) 
                e1
                t1
      -> (subst_t t1 (exp_obj e0) x) = t
      -> TypeOf Γ (Let x e0 e1) t.
Hint Constructors TypeOf.

Lemma ST_Refl : forall t,
Subtype t t.
Proof.
  unfold Subtype.
  intros t.
  apply P_Axiom. crush.
Qed.
Hint Resolve ST_Refl.

Lemma S_Trans : forall t1 t2 t3,
Subtype t1 t2
-> Subtype t2 t3
-> Subtype t1 t3.
Proof.
  intros t1 t2 t3 H12. generalize dependent t3. 
  unfold Subtype in *.
  induction H12; intros.
  inversion H0; subst.
  inversion H3; subst.
  rewrite <- H1. 
  apply P_Axiom; auto.
  crush.
  inversion H1; crush.
  inversion H4; crush.
  inversion H1. rewrite H4 in H0.
  re
  inversion H0; crush.
  inversion H
  destruct H23.

Theorem TypeOf_typed : forall e E,
TypedExp e
-> ({t : type | TypeOf E e t /\ forall t', TypeOf E e t' -> Subtype t t'} 
    + (forall t', ~ TypeOf E e t')).
Proof.
  intro e.
  induction e as 
      [n |
       |
       |
       s |
       x |
       x t |
       abs |
       e1 IH1 e2 IH2 e3 IH3 |
       x t e IHe |
       efun IHfun earg IHarg |
       x e0 IHe0 e1 IHe1 |
       e1 IHe1 e2 IHe2]; intros.
  { (* Nat *)
    left; exists tNat. split; intros.
    crush.
    match goal with | [H : TypeOf ?E (# ?n) ?t' |- _] => solve[inversion H; crush] end.
  }{ (* #t *)
    left; exists tT. split; intros.
    crush.
    match goal with | [H : TypeOf ?E #t ?t' |- _] => solve[inversion H; crush] end.
  }{ (* #f *)
    left; exists tF. split; intros.
    crush.
    match goal with | [H : TypeOf ?E #f ?t' |- _] => solve[inversion H; crush] end.
  }{ (* Str *)
    left; exists tStr. split; intros.
    crush.
    match goal with | [H : TypeOf ?E (Str ?s) ?t' |- _] => solve[inversion H; crush] end.
  }{ (* Var *)
    assert False. inversion H. crush.
  }{ (* TVar *)
    destruct (P_dec E (Atom (istype (var x) t))) as [HP | HNoP].
    left. exists t. split.
    apply T_TVar; auto.
    intros t' Htype.
    match goal with | [H : TypeOf ?E (t$ ?x ?t) ?t' |- _] => solve[inversion H; crush] end.
    right. intros t' contra. inversion contra; crush.
  }{ (* eOp *)
    destruct abs; try(solve[right; intros t' contra; inversion contra; crush]).
    left; exists (const_type c).
    split.
    apply T_Const; auto.
    intros.
    match goal with | [H : TypeOf ?E (eOp (c_op ?c)) ?t' |- _] => solve[inversion H; crush] end.
  }{ (* If *)
    assert ((TypedExp e1) /\ (TypedExp e2) /\ (TypedExp e3)) 
      as [HTE1 [HTE2 HTE3]]. inversion H; crush.
    destruct (IH1 E HTE1) as [[t1 [TypeH1 HU1]] | NoT1]; clear IH1.
    destruct (IH2 ((exp_prop e1)::E) HTE2) as [[t2 [TypeH2 HU2]] | NoT2]; clear IH2.
    destruct (IH3 ((Not (exp_prop e1))::E) HTE3) as [[t3 [TypeH3 HU3]] | NoT3]; clear IH3.
    {
      destruct (ST_dec t2 t3) as [st23 | Nost23].
      {
        left; exists t3. 
        split. 
        apply T_If with (t1:=t1) (t2:=t2) (t3:=t3); auto.
        intros.
        inversion H0. subst.
        apply HU3 in H7
        match goal with | [H : TypeOf ?E (If e1 e2 e3) ?t' |- _] => solve[inversion H; crush] end.

      }
      

    }
  }




Hint Constructors SubObj.
Lemma ex_min_super_obj : forall o1 o2,
{so : opt object | SubObj o1 so 
                   /\ SubObj o2 so 
                   /\ (forall o', 
                         (SubObj o1 o' /\ SubObj o2 o') ->
                                  SubObj so o')}.
Proof.
  intros o1 o2.
  destruct o1 as [o1|]. destruct o2 as [o2|].
  destruct (obj_eqdec o1 o2); subst.
  exists (Some o2). crush. 
  exists None. crush.
  inversion H0; inversion H1; crush.
  exists None; crush.
  exists None; crush.
Qed.  

Lemma U_st_lhs : forall t1 t2,
Subtype t1 (tU t1 t2).
Proof.
  intros.
  unfold Subtype. apply P_Union_lhs. apply P_Axiom; auto. crush.
Qed.

Lemma U_st_rhs : forall t1 t2,
Subtype t2 (tU t1 t2).
Proof.
  intros.
  unfold Subtype. apply P_Union_rhs. apply P_Axiom; auto. crush.
Qed.
Hint Resolve U_st_lhs U_st_rhs.

Lemma rem_t_eq : forall P L,
rem P (P :: L) = L.
Proof.
  intros.
  unfold rem.
  destruct (prop_eqdec P P); crush.
Qed.  

Lemma st_U : forall t1 t2 t3,
Subtype t1 t3
-> Subtype t2 t3
-> Subtype (tU t1 t2) t3.
Proof.
  intros.
  unfold Subtype in *.
  apply (P_UnionElim _ _ t1 t2 (var (Id 0))); auto.
  crush. 
  rewrite (rem_t_eq (Atom (istype (var (Id 0)) (tU t1 t2)))). auto.
  rewrite (rem_t_eq (Atom (istype (var (Id 0)) (tU t1 t2)))). auto.
Qed.
Hint Resolve st_U.

Hint Constructors ObjJoin.

Definition is_pair (e:exp) : bool :=
match e with
| eCons _ _ => true
| _ => false
end.

Definition is_tPair (t:type) : bool :=
match t with
| tPair _ _ => true
| _ => false
end.

Lemma if_id_eqdec_refl {T:Type} : forall x (P Q:T),
(if id_eqdec x x then P else Q) = P.
Proof.
  intros.
  destruct (id_eqdec x x); crush.
Qed.

Fixpoint exp_weight (e:exp) : nat :=
match e with
  | eIf e1 e2 e3 => 1 + (exp_weight e1)
                      + (exp_weight e2)
                      + (exp_weight e3)
  | eλ _ _ _ e => 1 + exp_weight e
  | eApp e1 e2 =>  1 + (exp_weight e1)
                     + (exp_weight e2)
  | eLet _ _ e1 e2 => 1 + (exp_weight e1)
                      + (exp_weight e2)
  | eCons e1 e2 =>  1 + (exp_weight e1)
                      + (exp_weight e2)
  | _ => 0
end.

Lemma tpo_eqdec : 
  forall (t : type)  (p :prop)  (o:opt object)
         (t' : type) (p' :prop) (o':opt object),
{(t,p,o) = (t',p',o')} + {(t,p,o) <> (t',p',o')}.
Proof.
  repeat decide equality.
Qed.

Ltac howboutno :=
try(solve[right; intros contra; inversion contra; crush]).

Lemma S_Top : forall t,
Subtype t tTop.
Proof.
  intros.
  destruct t; solve_it.
Qed.




(* Lemma T_Subsume : forall e E t, *)
(* TypeOf E e t *)
(* -> TypeOf E e tTop. *)
(* Proof. *)
(*   intros e E t HType. *)
(*   induction HType. *)
(*   eapply T_Nat; auto. solve_it. *)
(*   eapply T_Str; auto. solve_it. *)
(*   eapply T_Const; auto. destruct c; solve_it. *)
(*   eapply T_True; auto. solve_it. *)
(*   eapply T_False; auto. solve_it. *)
(*   eapply T_Var.  *)
(*   induction H. *)

(*   inversion Htype; subst. *)
  
(*   intros e; induction e; intros. *)
  
(*   crush. *)

Definition TypeOf_dec : forall e E t,
{TypeOf E e t} + {~TypeOf E e t}.
Proof.
  intros e.
  induction e as 
      [n |
       |
       |
       s |
       x |
       abs |
       econd IHcond etrue IHtrue efalse IHfalse |
       x t1 t2 body IHbody |
       efun IHfun earg IHarg |
       x xexp IHx body IHbody |
       elhs IHlhs erhs IHrhs]; intros.
  { (* # n *)
    destruct (ST_dec tNat t) as [HST | HNoST]; howboutno.
    left; apply T_Nat; auto.
  }{ (* #t *)
    destruct (ST_dec tT t) as [HST | HNoST]; howboutno.
    left; apply T_True; auto.
  }{ (* #f *)
    destruct (ST_dec tF t) as [HST | HNoST]; howboutno.
    left; apply T_False; auto.
  }{ (* Str *)
    destruct (ST_dec tStr t) as [HST | HNoST]; howboutno.
    left; apply T_Str; auto.
  }{ (* $ x *)
    destruct (P_dec E (var x ::= t)) as [HT | HNoT]; howboutno.
    left; apply T_Var; auto.
  }{ (* eOp *)
    destruct abs; howboutno.
    destruct (ST_dec (const_type c) t) as [HST | HNoST]; howboutno.
    left; apply T_Const; auto.
  }{ (* If *)
    destruct (IHcond E tTop); howboutno.
    destruct (IHtrue ((exp_prop econd)::E) t); howboutno.
    destruct (IHfalse ((Not (exp_prop econd))::E) t); howboutno.
    left. apply T_If; auto.
  }{ (* λ *)
    destruct (IHbody (Atom (istype (var x) t1) :: E) t2) 
      as [bodyTop | bodyNotTop]; howboutno.
    destruct (ST_dec (tλ x t1 t2 (exp_prop body) (exp_obj body)) t) 
      as [HST | HNotST]; howboutno.
    left. eapply T_Abs; eauto. 
  }{ (* App *)
    (* destruct (exp_eqdec efun (eOp (p_op opCar))) as [isCar | noCar]. *)
    (* { (* Car *) *)
    (* } *)
    (* destruct (exp_eqdec efun (eOp (p_op opCdr))) as [isCdr | noCdr]. *)
    (* { (* Cdr *) *)

    (* } *)
    (* destruct  *)

    (* destruct efun; howboutno. *)
    (* (* BOOKMARK *) *)
  }
  { (* Let *)

  }
  { (* Cons *)

  }

Definition TypeOf_dec : forall e E,
{l : list (type * prop * opt object) | 
(forall tpo : (type * prop * opt object),
 (match tpo with 
   | (t, p, o) => (TypeOf E e t p o)
  end)
 -> In tpo l)}.
Proof.
  intro e.
  induction e as
      [n |
       |
       |
       s |
       x |
       abs |
       econd IHcond etrue IHtrue efalse IHfalse |
       x t body IHbody |
       efun IHfun earg IHarg |
       x xexp IHx body IHbody |
       elhs IHlhs erhs IHrhs]; intros.
  {  (* Nat *)
    exists [(tNat, TT, None)].
    intros ((t,p),o) Htype.
    inversion Htype; subst.
    crush.
  }
  {  (* #t *)
    exists [(tT, TT, None)].
    intros ((t,p),o) Htype.
    inversion Htype; subst.
    crush.
  }
  { (* #f *)
    exists [(tF, FF, None)].
    intros ((t,p),o) Htype.
    inversion Htype; subst.
    crush.
  }
  { (* Str *)
    exists [(tStr, TT, None)].
    intros ((t,p),o) Htype.
    inversion Htype; subst.
    crush.
  }
  { (* eVar *)
    apply temp_axiom. (* yuck! *)
  }
  { (* eOp *)
    destruct abs.
    remember (const_type c) as t.
    exists [(t, TT, None)].
    intros ((t',p'),o') Htype.
    inversion Htype; subst.
    crush.
    exists [].
    intros ((t',p'),o') Htype.
    inversion Htype.
  }
  { (* eIf *)
    destruct (IHcond E) as [condL condH];
    clear IHcond. 
    destruct condL as [| [[ct cp] co] condL'].
    exists []. intros ((t,p),o) Htype.
    inversion Htype; subst.
    assert (In (τ', ψ1, o1) []) as condIn.
    { apply condH. auto. }
    inversion condIn.
    destruct (IHtrue (cp::E)) as [trueL trueH];
    clear IHtrue. 
    destruct trueL as [| [[tt tp] to] trueL'].
    exists []. intros ((t,p),o) Htype.
    inversion Htype; subst.
    assert (In (τ2, ψ2, o2) []) as condIn.
    { apply trueH. auto. }
    inversion condIn.



    apply condH. split. 

    specialize (condH _ _ H2 Htype).
    destruct (IHtrue (p1::E)) as [[[[t2 p2] o2] [trueT trueH]] | trueHNo];
    clear IHtrue.
    destruct (IHfalse ((Not p1)::E)) as [[[[t3 p3] o3] [falseT falseH]] | falseHNo];
    clear IHfalse.
    {
      destruct (ex_min_super_obj o2 o3) as [o [Ho2 [Ho3 Hodatum]]].
      left; exists ((tU t2 t3), (((p1 && p2) || ((Not p1) && p3))), o).
      split.
      apply (T_If _ _ _ _ _ _ _ _ _ _ _ _ _ _ condT trueT falseT); auto.
      intros t' p' o' H. 
      inversion H; subst.
      assert (p1 = ψ1) as Hp1eq. eapply condH. eassumption. subst ψ1.
      assert (t2 = τ2 /\ t3 = τ3) as [Ht2eqs Ht3eqs].
      {
        split. 
        eapply trueH. eassumption.
        eapply falseH. eassumption.
      }
      assert (p2 = ψ2 /\ p3 = ψ3) as [Hp2eqs Hp3eqs].
      {
        split.
        eapply trueH. eassumption.
        eapply falseH. eassumption.
      }
      assert (o2 = o5 /\ o3 = o6) as [Htoeqs Hfoeqs].
      {
        split.
        eapply trueH. eassumption.
        eapply falseH. eassumption.
      }
      subst. split; auto. split; auto.
      apply (ObjJoin_unique o5 o6). auto. auto.
    }
    {
      right. intros t p o Hno.
      inversion Hno; subst.
      assert (p1 = ψ1) as Hp1eq. eapply condH. eassumption. subst ψ1.
      apply (falseHNo τ3 ψ3 o5). auto.      
    }
    {
      right. intros t p o Hno.
      inversion Hno; subst.
      assert (p1 = ψ1) as Hp1eq. eapply condH. eassumption. subst ψ1.
      apply (trueHNo τ2 ψ2 o3). auto.      
    }
    {
      right. intros t p o Hno.
      inversion Hno; subst.
      apply (condHNo τ' ψ1 o1). auto.
    }
  }
  {
    destruct (IHbody ((var x ::= t)::E)) as [[[[t' p'] o'] [bodyH bodyHU]] | bodyHNo].
    {
      left. exists ((tλ x t t' p' o'), TT, None).
      split. apply T_Abs. auto.
      intros t'' p'' o'' Hbody''.
      inversion Hbody''; subst.
      assert (t' = τ /\ p' = ψ /\ o' = o) as [Hteq [Hpeq Hoeq]].
        apply bodyHU. auto.
      subst. auto.
    }
    {
      right. intros t' p' o' Hno.
      inversion Hno; subst.
      eapply bodyHNo. eassumption.
    }
  }
  { (* eApp *)
    destruct (exp_eqdec efun (eOp (p_op opCar))) as [isCar | noCar].
    { (* Car *)
      subst efun.
      destruct (IHarg E) as [[[[argt argp] argo] [argH argHU]] | argHNo].    
      {
        destruct argt;
        try(solve[right; intros t' p' o' Htype; inversion Htype; subst;
        match goal with
          | [ H: TypeOf E (eOp (p_op opCar)) ?t ?p ?o |- False] =>
            try(solve[inversion H])
          | [H: TypeOf E earg ?t0 ?ψ0 ?o0 |- _] =>
            try(solve[specialize (argHU t0 ψ0 o0 H); 
                       destruct argHU;
                       match goal with
                         | [H : _ = _ |- _ ] => try(solve[inversion H])
                       end])
        end]).
        left. 
        exists (argt1, 
                (subst_p (obj [car] (Id 0) ::~ tF) argo (Id 0)), 
                (subst_o (Some (obj [car] (Id 0))) argo (Id 0))).
        split. eapply T_Car. eassumption. 
        intros t' p' o' Htype.
        inversion Htype; subst.
        match goal with
          | [ H: TypeOf E (eOp (p_op opCar)) ?t ?p ?o |- _] =>
            solve[inversion H]
        end. 
        match goal with
          | [ H: TypeOf E earg ?t ?p ?o |- _] =>
            specialize (argHU _ _ _ H)
        end.
        destruct argHU as [tpaireq [peq oeq]].
        inversion tpaireq; subst; auto.
      }
      {
        right. intros t' o' i' Hno.
        inversion Hno; subst; eapply argHNo; eassumption.
      } 
    }
    destruct (exp_eqdec efun (eOp (p_op opCdr))) as [isCdr | noCdr].
    { (* Cdr *)
      subst efun.
      destruct (IHarg E) as [[[[argt argp] argo] [argH argHU]] | argHNo].    
      {
        destruct argt;
        try(solve[right; intros t' p' o' Htype; inversion Htype; subst;
        match goal with
          | [ H: TypeOf E (eOp (p_op opCdr)) ?t ?p ?o |- False] =>
            try(solve[inversion H])
          | [H: TypeOf E earg ?t0 ?ψ0 ?o0 |- _] =>
            try(solve[specialize (argHU t0 ψ0 o0 H); 
                       destruct argHU;
                       match goal with
                         | [H : _ = _ |- _ ] => try(solve[inversion H])
                       end])
        end]).
        left. 
        exists (argt2, 
                (subst_p (obj [cdr] (Id 0) ::~ tF) argo (Id 0)), 
                (subst_o (Some (obj [cdr] (Id 0))) argo (Id 0))).
        split. eapply T_Cdr. eassumption. 
        intros t' p' o' Htype.
        inversion Htype; subst.
        match goal with
          | [ H: TypeOf E (eOp (p_op opCdr)) ?t ?p ?o |- _] =>
            solve[inversion H]
        end. 
        match goal with
          | [ H: TypeOf E earg ?t ?p ?o |- _] =>
            specialize (argHU _ _ _ H)
        end.
        destruct argHU as [tpaireq [peq oeq]].
        inversion tpaireq; subst; auto.
      }
      {
        right. intros t' o' i' Hno.
        inversion Hno; subst; eapply argHNo; eassumption.
      } 
    }      
    { (* Non Car or Cdr app *)
      destruct (IHfun E) as [[[[ft fp] fo] [funH funHU]] | funHNo].
      {
        destruct ft as [ | | | | | | | | | ];
        try(solve[right; intros t' p' o' HNope; 
                  inversion HNope; subst;
                  match goal with 
                    | [ H : TypeOf E ?efun ?t' ?p' ?o' |- False ] =>
                      specialize (funHU _ _ _ H); destruct funHU; crush
                    | [ H : TypeOf E (eOp (p_op _)) _ _ _  |- _] => 
                      solve[crush]
                  end]).
        destruct (IHarg E) as [[[[argt argp] argo] [argH argHU]] | argHNo].    
        {
          destruct (ST_dec argt ft1) as [HargST | HargNoST].
          left. exists ((subst_t ft2 argo i),(subst_p p argo i),(subst_o o argo i)).
          split. eapply T_App. eassumption. eassumption. auto.
          intros t' p' o' Happ.
          inversion Happ; subst.
          match goal with
            | [ H: TypeOf E efun ?t ?p ?o |- _] =>
              specialize (funHU _ _ _ H)
          end.
          destruct funHU as [tfun_eq [p_eq o_eq]].
          inversion tfun_eq. subst.
          match goal with
            | [ H: TypeOf E earg ?t ?p ?o |- _] =>
              specialize (argHU _ _ _ H)
          end.
          destruct argHU as [targ_eq [parg_eq oarg_eq]]. subst.
          auto. crush. crush.
          right. intros t' o' i' Hno.
          inversion Hno; subst.
          apply HargNoST.
          assert (argt = σ /\ tλ i ft1 ft2 p o = (tλ x σ' τ fψ fo0)) as [argteq funeq].
          split. eapply argHU. eassumption. eapply funHU. eassumption.
          inversion funeq. subst. auto. crush. crush.
        }
        {
          right. intros t' o' i' Hno.
          inversion Hno; subst; eapply argHNo; eassumption.
        }
      }
      {
        right. intros t' o' i' Hno.
        inversion Hno; subst; eapply funHNo; try(eassumption || solve[crush]).
      }
    }
  }
  { (* Let *)
    destruct (IHx E) as [[[[xt xp] xo] [xH xHU]] | xHNo];
    clear IHx.
    destruct (IHbody ((var x ::= xt
                           :: (var x ::~ tF --> xp) 
                           :: (var x ::= tF --> Not xp) :: E))) 
      as [[[[bodyt bodyp] bodyo] [bodyH bodyHU]] | bodyHNo].
    {
      left. exists ((subst_t bodyt xo x),(subst_p bodyp xo x),(subst_o bodyo xo x)).
      split. eapply (T_Let _ _ _ _ _ _ _ _ _ _ xH bodyH).
      intros t' p' o' Htype.
      inversion Htype; subst.
      assert (xt = τ /\ xp = ψ0 /\ xo = o0) as [xteq [xpeq xoeq]].
      { apply xHU. auto. }
      assert (bodyt = σ /\ bodyp = ψ1 /\ bodyo = o1) as [teq [peq oeq]]. 
      { apply bodyHU. subst. auto. }
      subst. auto.
    }
    {
      right. intros t' o' i' Hno.
      inversion Hno; subst; eapply bodyHNo. 
      assert (xt = τ /\ xp = ψ0 /\ xo = o0) as [xteq [xpeq xoeq]].
      { apply xHU. auto. }
      subst. eassumption.
    }
    {
      right. intros t' o' i' Hno.
      inversion Hno; subst; eapply xHNo. eassumption.
    }
  }
  { (* Cons *)
    destruct (IHlhs E) as [[[[lhst lhsp] lhso] [lhsH lhsHU]] | lhsHNo].
    {
      destruct (IHrhs E) as [[[[rhst rhsp] rhso] [rhsH rhsHU]] | rhsHNo].
      {
        left. exists ((tPair lhst rhst),TT,None).
        split. eapply T_Cons; eauto.
        intros t' p' o' Htype.
        inversion Htype; subst.
        assert (lhst = τ1 /\ rhst = τ2) as [lhseq rhseq].
        {
          split.
          eapply lhsHU. eassumption.
          eapply rhsHU. eassumption.
        }
        subst. auto.
      }
      right. intros t' p' o' Hno.
      inversion Hno; subst. eapply rhsHNo; eassumption.
    }
      right. intros t' p' o' Hno.
      inversion Hno; subst. eapply lhsHNo; eassumption.
  }
Grab Existential Variables.
auto. auto. auto. auto. auto. auto.
Qed.  