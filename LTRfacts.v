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

Fixpoint types_in (o:object) (L:list prop) : list type :=
  match L with
    | nil => nil
    | (Atom (istype o' t)) :: ps => 
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
  destruct f as [o' t'].
  destruct (obj_eqdec o o'); subst.
  destruct HIn. subst. left; auto.
  right; auto. right; auto.
Defined.

Lemma types_in_nonnil : forall L o t,
In (Atom (istype o t)) L
-> types_in o L <> [].
Proof.
  intros L; induction L; crush.
  destruct (obj_eqdec o o). crush. crush.
  destruct a; crush. destruct f.
  destruct (obj_eqdec o o0). crush.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
  apply (IHL o t). auto. auto.
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

Fixpoint contains_type_conflict (o:object) (t:type) (L:list prop) : opt type :=
  match L with
    | nil => None
    | (Atom (istype o' t')) :: L' =>
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
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec Pbig a). crush.
  simpl. fold rem.
  eapply (IHL P Pbig Psmall) in H. 
  unfold proof_weight in *. crush. auto.
Defined.  

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
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec Pbig a). crush.
  simpl. fold rem.
  eapply (IHL P Pbig Psmall1 Psmall2) in H. 
  unfold proof_weight in *. crush. auto.
Defined.  

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
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec Pbig a). crush.
  simpl. fold rem.
  eapply (IHL P Pbig Psmall1 Psmall2 Psmall3) in H. 
  unfold proof_weight in *. crush. auto.
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
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec Pbig a). crush.
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

Definition get_fact (p:prop) : opt fact :=
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
  (* Proves_dec *)
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
          + {get_fact P = None \/ ~In P Γ}) as Axiom_dec.
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

Definition Proves_dec : forall Γ P,
{Proves Γ P} + {~Proves Γ P}.
Proof.
  intros Γ P.
  remember (Proves_dec_pair (Γ, P)) as H.
  crush.
Defined.


Lemma proves_TT :
Proves [] TT.
Proof.
  remember (Proves_dec [] TT).
  compute in Heqs. exact (P_True []).
Defined.

Ltac solve_it :=
  match goal with 
    | |- Proves ?L ?P =>
      let provability := constr:(Proves_dec L P) in
      let proof := eval vm_compute in provability in
      match proof with
        | left ?prf => exact prf
        | right _ => idtac
      end
  end.

Lemma proves_TT2 :
Proves [] TT.
Proof.
  solve_it.
Defined.


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




Definition Subtype_dec : forall t1 t2,
{Subtype t1 t2} + {~Subtype t1 t2}.
Proof.
  intros t1 t2.
  unfold Subtype. apply Proves_dec.
Defined.