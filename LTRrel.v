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

Require Import LTRbase.
Require Import Relations.
Require Import Permutation.
Require Import Morphisms.
Require Import Setoid.
Require Import Perm.
Import ListNotations.
(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)


Inductive CommonSubtype : (type * type) -> Prop :=
| CST_Refl :
    forall t, CommonSubtype (t, t)
| CST_Top_rhs :
    forall t, CommonSubtype (t, tTop)
| CST_Top_lhs :
    forall t, CommonSubtype (tTop, t)
| CST_lhsUnion_lhs :
    forall t1 t2 t, 
      CommonSubtype (t1, t)
      -> CommonSubtype ((tU t1 t2), t)
| CST_lhsUnion_rhs :
    forall t1 t2 t, 
      CommonSubtype (t2, t)
      -> CommonSubtype ((tU t1 t2), t)
| CST_rhsUnion_lhs :
    forall t1 t2 t, 
      CommonSubtype (t, t1)
      -> CommonSubtype (t, (tU t1 t2))
| CST_rhsUnion_rhs :
    forall t1 t2 t, 
      CommonSubtype (t, t2)
      -> CommonSubtype (t, (tU t1 t2))
| CST_Abs :
    forall x y t1 t2 t3 t4 p1 p2 o1 o2,
      CommonSubtype ((tλ x t1 t2 p1 o1), (tλ y t3 t4 p2 o2))
| CST_Pair :
    forall t1 t2 t3 t4, 
      CommonSubtype (t1, t3)
      -> CommonSubtype (t2, t4)
      -> CommonSubtype ((tPair t1 t2), (tPair t3 t4))
| CST_Cons_lhs :
    forall t1 t2,
      CommonSubtype (tCons, (tPair t1 t2))
| CST_Cons_rhs :
    forall t1 t2,
      CommonSubtype ((tPair t1 t2), tCons).
Hint Resolve CST_Refl CST_Top_rhs CST_Top_lhs
             CST_Cons_lhs CST_Cons_rhs
             CST_Pair CST_Abs.

Inductive Contradictory : relation formula :=
| con_type : 
    forall o t1 t2,
      ~CommonSubtype (t1,t2)
      -> Contradictory (o ::= t1) (o ::= t2)
(* | con_pair_cons_lhs :  *)
(*     forall o t1 t2 t3, *)
(*       ~CommonSubtype (t3,tCons) *)
(*       -> Contradictory (o ::= (tPair t1 t2)) (o ::= t3) *)
(* | con_pair_cons_rhs :  *)
(*     forall o t1 t2 t3, *)
(*       ~CommonSubtype (t3,tCons) *)
(*       -> Contradictory (o ::= t3) (o ::= (tPair t1 t2)) *)
| con_pair_car_lhs : 
    forall π x t1 t2 P,
      Contradictory (((obj (π ++ [car])) x) ::= t1) P
      -> Contradictory ((obj π x) ::= (tPair t1 t2)) P
| con_pair_cdr_lhs : 
    forall π x t1 t2 P,
      Contradictory (((obj (π ++ [cdr])) x) ::= t2) P
      -> Contradictory ((obj π x) ::= (tPair t1 t2)) P
| con_pair_car_rhs : 
    forall π x t1 t2 P,
      Contradictory P (((obj (π ++ [car])) x) ::= t1)
      -> Contradictory P ((obj π x) ::= (tPair t1 t2))
| con_pair_cdr_rhs : 
    forall π x t1 t2 P,
      Contradictory P (((obj (π ++ [cdr])) x) ::= t2)
      -> Contradictory P ((obj π x) ::= (tPair t1 t2)).


(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** ** Proves Relation *)

Inductive Proves : list formula -> formula -> Prop :=
| P_Axiom :
    forall L P,
      In P L
      -> Proves L P
| P_Contradiction :
    forall L P P1 P2,
      Contradictory P1 P2
      -> In P1 L
      -> In P2 L
      -> Proves L P
| P_UnionElim :
    forall L1 L2 P t1 t2 o,
      Proves ((o ::= t1)::L1) P
      -> Proves ((o ::= t2)::L1) P
      -> Permutation ((o ::= (tU t1 t2))::L1) L2
      -> Proves L2 P
| P_PairElim :
    forall L1 L2 P t1 t2 π x,
      Proves (((obj π x) ::= tCons)
                ::((obj (π ++ [car]) x) ::= t1)
                ::((obj (π ++ [cdr]) x) ::= t2)
                ::L1) 
             P
      -> Permutation (((obj π x) ::= (tPair t1 t2))::L1) L2
      -> Proves L2 P
| P_Top :
  forall L t o,
    In (o ::= t) L
    -> Proves L (o ::= tTop)
| P_Union_lhs :
    forall L t1 t2 o,
      Proves L (o ::= t1)
      -> Proves L (o ::= (tU t1 t2))
| P_Union_rhs :
    forall L t1 t2 o,
      Proves L (o ::= t2)
      -> Proves L (o ::= (tU t1 t2))
| P_Pair :
    forall L t1 t2 π x,
      Proves L ((obj (π ++ [car]) x) ::= t1)
      -> Proves L ((obj (π ++ [cdr]) x) ::= t2)
      -> Proves L ((obj π x) ::= tCons)
      -> Proves L ((obj π x) ::= (tPair t1 t2))
| P_Fun :
    forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 ox,
      In (ox ::= (tλ x1 t1a t1r p1 o1)) L
      -> Proves [(ox ::= (subst_t t1r (Some (var x2)) x1))] (ox ::= t2r)
      -> Proves [(ox ::= t2a)] (ox ::= (subst_t t1a (Some (var x2)) x1))
      -> Proves [(assume (subst_p p1 (Some (var x2)) x1))] (question p2)
      -> SubObj (subst_o o1 (Some (var x2)) x1) o2
      -> Proves L (ox ::= (tλ x2 t2a t2r p2 o2))
| P_Bot :
    forall L P o,
      In (o ::= tBot) L
      -> Proves L P
| P_True :
    forall L,
      Proves L TT
| P_False :
    forall L P,
      In FF L
      -> Proves L P
| P_Simpl :
    forall L1 L2 R P Q,
      Proves (P::Q::L1) R
      -> Permutation ((P && Q)::L1) L2
      -> Proves L2 R
| P_DisjElim :
    forall L1 L2 R P Q,
      Proves (P::L1) R
      -> Proves (Q::L1) R
      -> Permutation ((P || Q)::L1) L2
      -> Proves L2 R
| P_MP :
     forall L1 L2 R P Q,
       Proves L1 P
       -> Proves (Q::L1) R
       -> Permutation ((P =-> Q)::L1) L2
       -> Proves L2 R
| P_Conj :
    forall L P Q,
      Proves L P
      -> Proves L Q
      -> Proves L (P && Q)
| P_Add_lhs :
    forall L P Q,
      Proves L P
      -> Proves L (P || Q)
| P_Add_rhs :
    forall L P Q,
      Proves L Q
      -> Proves L (P || Q)
 | P_CP :
     forall L P Q,
       Proves (P::L) Q
       -> Proves L (P =-> Q).

Definition Subtype (t1 t2:type) := 
  Proves [((var (Id 0)) ::= t1)] ((var (Id 0)) ::= t2).

Definition Implies (p1 p2:prop) : Prop :=
Proves [(assume p1)] (question p2).

Lemma contra_unionL_lhs : forall o t1 t2 P,
Contradictory (o ::= (tU t1 t2)) P
-> Contradictory (o ::= t1) P.
Proof.
  intros o t1 t2 P2 Hcontra.
  remember (o ::= tU t1 t2) as P1.
  induction Hcontra; try(solve[inversion HeqP1]).
- inversion HeqP1; subst.
  apply con_type.
  intros contra. apply H. apply CST_lhsUnion_lhs; auto.
(* - inversion HeqP1; subst. *)
(*   apply con_pair_cons_rhs. *)
(*   intros contra. apply H.  *)
(*   apply CST_lhsUnion_lhs; auto. *)
- subst P.
  apply con_pair_car_rhs. crush.
- subst P.
  apply con_pair_cdr_rhs. crush.
Qed.              

Lemma contra_unionL_rhs : forall o t1 t2 P,
Contradictory (o ::= (tU t1 t2)) P
-> Contradictory (o ::= t2) P.
Proof.
  intros o t1 t2 P2 Hcontra.
  remember (o ::= tU t1 t2) as P1.
  induction Hcontra; try(solve[inversion HeqP1]).
- inversion HeqP1; subst.
  apply con_type.
  intros contra. apply H. apply CST_lhsUnion_rhs; auto.
(* - inversion HeqP1; subst. *)
(*   apply con_pair_cons_rhs. *)
(*   intros contra. apply H.  *)
(*   apply CST_lhsUnion_rhs; auto. *)
- subst P.
  apply con_pair_car_rhs. crush.
- subst P.
  apply con_pair_cdr_rhs. crush.
Qed.              

Lemma contra_unionR_lhs : forall o t1 t2 P,
Contradictory P (o ::= (tU t1 t2))
-> Contradictory P (o ::= t1).
Proof.
  intros o t1 t2 P2 Hcontra.
  remember (o ::= tU t1 t2) as P1.
  induction Hcontra; try(solve[inversion HeqP1]).
- inversion HeqP1; subst.
  apply con_type.
  intros contra. apply H. apply CST_rhsUnion_lhs; auto.
(* - inversion HeqP1; subst. *)
(*   apply con_pair_cons_rhs. *)
(*   intros contra. apply H.  *)
(*   apply CST_lhsUnion_lhs; auto. *)
- subst P.
  apply con_pair_car_lhs. crush.
- subst P.
  apply con_pair_cdr_lhs. crush.
Qed.              

Lemma contra_unionR_rhs : forall o t1 t2 P,
Contradictory P (o ::= (tU t1 t2))
-> Contradictory P (o ::= t2).
Proof.
  intros o t1 t2 P2 Hcontra.
  remember (o ::= tU t1 t2) as P1.
  induction Hcontra; try(solve[inversion HeqP1]).
- inversion HeqP1; subst.
  apply con_type.
  intros contra. apply H. apply CST_rhsUnion_rhs; auto.
(* - inversion HeqP1; subst. *)
(*   apply con_pair_cons_rhs. *)
(*   intros contra. apply H.  *)
(*   apply CST_lhsUnion_rhs; auto. *)
- subst P.
  apply con_pair_car_lhs. crush.
- subst P.
  apply con_pair_cdr_lhs. crush.
Qed.              


Lemma contra_pairL : forall π x t1 t2 P,
Contradictory ((obj π x) ::= (tPair t1 t2)) P
-> (Contradictory ((obj π x) ::= tCons) P
    \/ Contradictory ((obj (π++[car]) x) ::= t1) P
    \/ Contradictory ((obj (π++[cdr]) x) ::= t2) P).
Proof.
  intros π x t1 t2 P2 Hcontra.
  remember ((obj π x) ::= (tPair t1 t2)) as P1 in Hcontra.
  induction Hcontra; try(solve[inversion HeqP1]).
- inversion HeqP1; subst. 
  induction t3.
  + assert False. apply H. auto. crush.
  + left. apply con_type. intros contra; inversion contra; crush.
  + destruct (type_eqdec tCons (tBase b)) as [Heq | Hneq].
    * assert False. apply H. rewrite <- Heq. auto. crush.
    * left. apply con_type. intros contra; inversion contra. crush.
  + left. apply con_type. intros contra; inversion contra; crush.
  + assert (~ CommonSubtype (tPair t1 t2, t3_1)) as HNotlhs.
      intros contra. apply H. apply CST_rhsUnion_lhs; auto.
      apply IHt3_1 in HNotlhs. clear IHt3_1.
    assert (~ CommonSubtype (tPair t1 t2, t3_2)) as HNotrhs.
      intros contra. apply H. apply CST_rhsUnion_rhs; auto.
      apply IHt3_2 in HNotrhs. clear IHt3_2.
      
    destruct HNotlhs as [Hnotlhs | [Hnotlhs | Hnotlhs]].
    destruct HNotrhs as [Hnotrhs | [Hnotrhs | Hnotrhs]].
    
    left. 

    


      eapply contra_unionR_lhs. apply con_type. exact H.
      eapply con_type in H0.
      apply IHt3_1 in H0.

left. apply con_type. intro Hcon.
 apply (con_type (obj π x)) in H. 
    
    assert (~CommonSubtype ).

left. apply con_type. intros contra; inversion contra; crush.

  induction (obj π x ::= tPair t1 t2)
        using (well_founded_induction
                 (well_founded_ltof _ formula_weight)).


 inversion HeqP1; subst.
  destruct 


  left. apply con_pair_cons_rhs. con_type. intros Hcons.
  apply H.


Lemma perm_split {X:Type} : 
  forall L1 L2 L' (P:X),
    Permutation (L1 ++ P :: L2) L'
    -> exists L1' L2', 
         L' = L1'++P::L2'.
Proof.
  intros L1 L2 L' P Hperm.
  apply in_split.
  eapply Permutation_in. exact Hperm.
  eapply Permutation_in.
  eapply Permutation_cons_app.
  apply Permutation_refl.
  left; auto.
Qed.

Lemma P_Perm : forall L1 L2 P,
Proves L1 P
-> Permutation L1 L2
-> Proves L2 P.
Proof.
  intros L1 L2 P HL1.
  generalize dependent L2.
  induction HL1 as 
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros L1 HPerm.
  eapply P_Axiom. eapply Permutation_in; eauto.
- intros L' HPerm.
  apply (P_Contradiction L' P P1 P2); 
    try (apply Permutation_in with (l:=L)); auto.
- intros L' HPerm.
  eapply P_UnionElim. exact HP1. exact HP2.
  eapply Permutation_trans; eauto. 
- intros L' HPerm.
  eapply P_PairElim. exact HP.
  eapply Permutation_trans; eauto.
- intros L' HPerm.
  eapply P_Top. 
  eapply Permutation_in. exact HPerm. exact HIn.
- intros L' HPerm.
  eapply P_Union_lhs; crush.  
- intros L' HPerm.
  eapply P_Union_rhs; crush.
- intros L' HPerm.
  apply P_Pair; crush.
- intros L' HPerm.
  eapply P_Fun; crush.
  eapply Permutation_in. exact HPerm.
  eassumption. crush.
- intros L' HPerm.
  eapply P_Bot. eapply Permutation_in. exact HPerm. eauto.
- intros L' HPerm. apply P_True.
- intros L' HPerm.
  apply P_False. eapply Permutation_in; eauto.
- intros L' HPerm.
  eapply P_Simpl; eauto.
  eapply Permutation_trans; eauto.
- intros L' HPerm.
  assert (Permutation (P || Q :: L1) L') as Hperm'.
    eapply Permutation_trans. exact Hperm. auto.
  apply (P_DisjElim _ _ _ _ _ HPP HPQ Hperm').
- intros L' HPerm.
  eapply (P_MP _ _ R P Q); eauto.
  eapply Permutation_trans; eauto.
- intros L' HPerm.
  apply P_Conj; crush.
- intros L' HPerm.
  apply P_Add_lhs; crush.
- intros L' HPerm.
  apply P_Add_rhs; crush.
- intros L' HPerm.
  apply P_CP; crush.
Qed.

Instance Proves_compat : Proper (@Permutation _==>eq==>iff) Proves.
Proof.
unfold Proper,respectful.
intros L1 L2 HPerm P1 P2 Heq. split.
intros H1. subst. apply (P_Perm L1 L2); auto.
intros H2. subst. apply (P_Perm L2 L1); crush.
Qed.

Ltac swap L := apply (P_Perm L); try(solve[perm]).

Lemma P_Weak :
    forall L1 L2 P Q,
      Proves L1 P
      -> Permutation (Q::L1) L2
      -> Proves L2 P.
Proof.
  intros L1 L2 P Q HProves.
  generalize dependent Q.
  generalize dependent L2.
  induction HProves as 
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
Proof.
- intros L' P1 HPerm.
  rewrite <- HPerm.
  eapply (P_Axiom (P1::L)). 
  right; auto. 
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply (P_Contradiction _ P P1 P2); crush.
- intros L' P' HPerm.
  rewrite <- HPerm. rewrite <- Hperm. rewrite perm_swap.
  apply (P_UnionElim (P' :: L1) _ P t1 t2 o); auto.
  apply (IH1 _ P'). perm.
  apply (IH2 _ P'). perm.
- intros L' P' HPerm.
  rewrite <- HPerm. rewrite <- Hperm. rewrite perm_swap.
  apply (P_PairElim (P' :: L1) _ P t1 t2 π x); auto.
  apply (IHP _ P'). perm.
- intros L2 P' HPerm.
  rewrite <- HPerm.
  eapply P_Top. right; eauto.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Union_lhs. apply (IHP _ P'). auto.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Union_rhs. apply (IHP _ P'). auto.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Pair. 
  apply (IHPcar _ P'); auto.
  apply (IHPcdr _ P'); auto.
  apply (IHPcons _ P'); auto.
- intros L' P' HPerm.
  rewrite <- HPerm.
  eapply P_Fun. right. exact HIn.
  auto. auto. auto. auto.
- intros L' P' HPerm.
  rewrite <- HPerm. 
  eapply P_Bot. right; eauto.
- intros L' P' HPerm.
  apply P_True.
- intros L' P' HPerm.
  rewrite <- HPerm. 
  eapply P_False. right; eauto.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply (P_Simpl (P'::L1) _  R P Q).
  apply (IH _ P'). perm.
  rewrite <- Hperm2. perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply (P_DisjElim (P'::L1) _  R P Q).
  apply (IHP _ P'). perm.
  apply (IHQ _ P'). perm.
  rewrite <- Hperm. perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply (P_MP (P'::L1) _  R P Q).
  apply (IHP _ P'). perm.
  apply (IHPQ _ P'). perm.
  rewrite <- Hperm. perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Conj.
  apply (IHP _ P'). perm.
  apply (IHQ _ P'). perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Add_lhs.
  apply (IHP _ P'). perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_Add_rhs.
  apply (IHQ _ P'). perm.
- intros L' P' HPerm.
  rewrite <- HPerm.
  apply P_CP.
  apply (IHP _ P'). perm.
Qed.

Lemma contr_perm {X:Type} : 
  forall (a b:X) 
         (l1 l2:list X),
Permutation (a::l1) (b::b::l2) 
-> (a = b /\ Permutation l1 (b::l2)) 
   \/ (exists l2',
          Permutation l2 (a::l2') 
          /\ Permutation l1 (b::b::l2')).
Proof.
intros a b l1 l2 HPerm.
assert (H:=in_eq a l1). rewrite HPerm in H.
assert (H2:In a (b::l2)).
{ destruct H.
  left; auto. 
  auto. }
clear H.
destruct H2 as [H|H].
- left. split; auto.
  rewrite <-H in HPerm.
  apply Permutation_cons_inv in HPerm; auto.
- right.
  destruct (in_split _ _ H) as (lA,(lB,Hl2eq)).
  exists (lA++lB).
  split. subst. perm. 
  apply Permutation_cons_inv with (a:=a).
  rewrite HPerm. rewrite Hl2eq. perm.
Qed.

Lemma both_in_perm {X:Type} : forall (a b c:X) (l1 l2:list X),
In a l1
-> In b l1
-> a <> b
-> Permutation l1 (c :: c :: l2)
-> ((a = c /\ In b l2)
    \/ (b = c /\ In a l2)
    \/ (In a l2 /\ In b l2)).
Proof.
  intros a b c l1 l2 HaIn HbIn Hneq HPerm.
  rewrite HPerm in HaIn.
  rewrite HPerm in HbIn.
  destruct HaIn as [Haeq | [ Haeq | Harest]]; subst.
  destruct HbIn as [Hcontra | [Hcontra | Hbrest]]; crush.
  destruct HbIn as [Hcontra | [Hcontra | Hbrest]]; crush.
  destruct HbIn as [Hcontra | [Hcontra | Hbrest]]; crush.
Qed.

Lemma Contradictory_neq : forall P1 P2,
Contradictory P1 P2
-> P1 <> P2.  
Proof.  
  intros P1 P2 HCon Heq. subst.
  inversion HCon; crush.
Qed.

Definition flip_pair {X:Type} (p:X*X) : X*X := ((snd p), (fst p)).
Hint Unfold flip_pair.

Fixpoint type_pair_weight (tp : (type * type)) : nat :=
(type_weight (fst tp)) + (type_weight (snd tp)).

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
  inversion H; subst; crush. compute. apply CST_Cons_rhs.
  inversion H; subst; crush. compute. apply CST_Cons_lhs.
  inversion H; subst.
  compute. apply CST_Refl.
  apply CST_Pair. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto. 
    rewrite flip_eq. apply IH. auto_tp_weight. auto.
Defined.

Lemma Contradictory_sym : forall P1 P2,
Contradictory P1 P2
-> Contradictory P2 P1.  
Proof.  
  intros P1 P2 HCon. 
  inversion HCon; crush.
  apply contratype.
  intros HCST.
  apply CST_symmetric in HCST. compute in HCST.
  crush.
Qed.

Lemma cons_perm {X:Type} : forall (a b :X) L1 L2,
Permutation (a::L1) (b::L2)
-> ((a=b /\ Permutation L1 L2)
    \/ (In a L2 /\ In b L1)).
Proof.
  intros a b L1 L2 HPerm.
  assert (In a (b::L2)) as HaIn.
    eapply Permutation_In_In. eauto. crush.
  assert (In b (a::L1)) as HbIn.
    eapply Permutation_In_In. apply Permutation_sym. eauto. crush.
  destruct HaIn as [Heq | HaIn]; subst.
  apply Permutation_cons_inv in HPerm.
  left; crush.
  destruct HbIn as [Heq | HbIn]; subst.
  apply Permutation_cons_inv in HPerm.
  left; crush.
  right; crush.
Qed.

Lemma perm_dbl_cons_app1 {X:Type} : forall (P1 P2:X) L1 L2 L3 L4,
Permutation (P1 :: L1 ++ P2 :: L2)
            (P2 :: L3 ++ P1 :: L4)
-> Permutation (L1++L2) (L3++L4).
Proof. 
  intros P1 P2 L1 L2 L3 L4 HP.
  assert (Permutation (P2 :: L3 ++ P1 :: L4) (P1 :: L4 ++ P2 :: L3)). perm.
  rewrite H in HP.
  apply Permutation_cons_inv in HP.
  rewrite <- Permutation_middle in HP. rewrite <- Permutation_middle in HP.
  apply Permutation_cons_inv in HP.
  assert (Permutation (L4++L3) (L3++L4)) as Hcomm.
  apply Permutation_app_comm.
  rewrite <- Hcomm. auto.
Qed.  

Lemma In_perm {X:Type} : forall L (x:X),
In x L 
-> exists L', Permutation L (x::L').
Proof.
  intros L x HIn.
  destruct (in_split _ _ HIn) as [L1 [L2 Leq]].
  exists (L1++L2).
  subst; perm.
Qed.


Lemma P_disj_elimL_lhs:
  forall P1 P2 P L1,
    Proves ((P1 || P2)::L1) P 
    -> Proves (P1::L1) P.
Proof.
  intros P1 P2 P L1 HProves.
  remember (P1 || P2::L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert P1 P2 L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros P1 P2 L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Add_lhs. eapply P_Axiom. crush. 
  eapply P_Axiom; crush.
- intros P3 P4 L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. inversion HContra. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. inversion HContra. 
  apply (P_Contradiction _ P P1 P2); crush.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  eapply (P_UnionElim (P1::L3') _ P t1 t2 o).
  rewrite perm_swap. eapply (IH1 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite perm_swap. eapply (IH2 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t1 t2))).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  eapply (P_PairElim (P1::L3') _ P t1 t2 π x).
  swap (P1:: Elem (istype (obj π x) tCons)
          :: Elem (istype (obj (π ++ [car]) x) t1)
          :: Elem (istype (obj (π ++ [cdr]) x) t2) :: L3').
  eapply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Top _ t o). right; auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_rhs. apply (IHP P1 P2); auto.
- intros P1 P2 L2 HPerm.
  apply P_Pair. apply (IHPcar P1 P2); auto.
  apply (IHPcdr P1 P2); auto.
  apply (IHPcons P1 P2); auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. right; auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o). right; auto.
- intros P1 P2 L1 HPerm. apply P_True.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. right; auto.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_Simpl (P1::L3') _ R P Q).
  swap(P1 :: P :: Q :: L3').
  apply (IH P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_DisjElim (P1::L3') _ _ P Q).
  rewrite perm_swap. apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite perm_swap. apply (IHQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_MP (P1::L3') _ _ P Q).
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (P1 :: Q :: L3').
  apply (IHPQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  apply P_Conj. apply (IHP P1 P2); auto. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_rhs. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_CP. rewrite perm_swap. apply (IHP P1 P2); auto.
  rewrite HPerm. perm.
Qed.

Lemma P_union_elimL_lhs:
  forall P L1 o t1 t2,
    Proves ((o::= (tU t1 t2))::L1) P 
    -> Proves ((o ::= t1)::L1) P.
Proof.
  intros P L1 o t1 t2 HProves.
  remember (o ::= tU t1 t2 :: L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert o t1 t2 L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t3 t4 o1 HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t3 t4 π x HP IHP Hperm | (* P_PairElim *)
       L t o1 HIn | (* P_Top *)
       L t3 t4 o1 HP IHP | (* P_Union_lhs *)
       L t3 t4 o1 HP IHP | (* P_Union_rhs *)
       L1 t3 t4 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o' HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o1 HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros o t1 t2 L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Union_lhs. eapply P_Axiom. crush. 
  eapply P_Axiom. crush.
- intros o t1 t2  L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. crush.
  apply (P_Contradiction _ P (o ::= t1) P2).
  eapply contra_unionL_lhs. eauto. crush. crush.
  destruct HIn2 as [Heqor | HIn2]. subst P2. 
  apply (P_Contradiction _ P (o ::= t1) P1).
  clear HeqHneq.
  apply Contradictory_sym in HContra.
  eapply contra_unionL_lhs. eauto. crush. crush.
  apply (P_Contradiction _ P P1 P2); crush.
- intros o t1 t2  L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o1 (tU t3 t4))).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  eapply (P_UnionElim (Elem (istype o t1)::L3') _ P t3 t4 o1).
  rewrite perm_swap. eapply (IH1 o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite perm_swap. eapply (IH2 o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros o t1 t2  L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t3 t4))).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  eapply (P_PairElim (Elem (istype o t1)::L3') _ P t3 t4 π x).
  swap (Elem (istype o t1) :: Elem (istype (obj π x) tCons)
             :: Elem (istype (obj (π ++ [car]) x) t3)
             :: Elem (istype (obj (π ++ [cdr]) x) t4) :: L3').
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. subst.
  apply (P_Top _ t1 o1). crush.
  apply (P_Top _ t o1). crush.
- intros o t1 t2 L1 HPerm. 
  apply P_Union_lhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Union_rhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L3 HPerm. 
  apply P_Pair. 
  apply (IHPcar o t1 t2 L3); auto.
  apply (IHPcdr o t1 t2 L3); auto.
  apply (IHPcons o t1 t2 L3); auto.
- intros o t1 t2 L3 HPerm. 
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. crush. 
- intros o t1 t2  L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o1). crush. 
- intros; apply P_True.
- intros o t1 t2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. crush. 
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. 
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_Simpl (Elem (istype o t1)::L3') _ R P Q).
  swap ((Elem (istype o t1)) :: P :: Q :: L3').
  apply (IH o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_DisjElim (Elem (istype o t1)::L3') _ _ P Q).
  swap (Elem (istype o t1) :: P :: L3').
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  swap (Elem (istype o t1) :: Q :: L3').
  apply (IHQ o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq. 
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_MP (Elem (istype o t1)::L3') _ _ P Q).
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (Elem (istype o t1) :: Q :: L3').
  apply (IHPQ o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L1 HPerm. 
  apply P_Conj. apply (IHP o t1 t2); auto.
  apply (IHQ o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Add_lhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Add_rhs. apply (IHQ o t1 t2); auto.
- intros o t1 t2 L1 HPerm.
  apply P_CP. 
  rewrite perm_swap.
  apply (IHP o t1 t2); auto.
  rewrite HPerm. perm.
Qed.


Lemma P_disj_elimL_rhs:
  forall P1 P2 P L1,
    Proves ((P1 || P2)::L1) P 
    -> Proves (P2::L1) P.
Proof.
  intros P1 P2 P L1 HProves.
  remember (P1 || P2::L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert P1 P2 L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros P1 P2 L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Add_rhs. eapply P_Axiom. crush. 
  eapply P_Axiom; crush.
- intros P3 P4 L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. inversion HContra. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. inversion HContra. 
  apply (P_Contradiction _ P P1 P2); crush.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  eapply (P_UnionElim (P2::L3') _ P t1 t2 o).
  rewrite perm_swap. eapply (IH1 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite perm_swap. eapply (IH2 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t1 t2))).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  eapply (P_PairElim (P2::L3') _ P t1 t2 π x).
  swap (P2:: Elem (istype (obj π x) tCons)
                  :: Elem (istype (obj (π ++ [car]) x) t1)
                  :: Elem (istype (obj (π ++ [cdr]) x) t2) :: L3').
  eapply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Top _ t o). right; auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_rhs. apply (IHP P1 P2); auto.
- intros P1 P2 L2 HPerm.
  apply P_Pair. apply (IHPcar P1 P2); auto.
  apply (IHPcdr P1 P2); auto.
  apply (IHPcons P1 P2); auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. right; auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o). right; auto.
- intros P1 P2 L1 HPerm. apply P_True.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. right; auto.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_Simpl (P2::L3') _ R P Q).
  swap (P2 :: P :: Q :: L3').
  apply (IH P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_DisjElim (P2::L3') _ _ P Q).
  rewrite perm_swap. apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite perm_swap. apply (IHQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=(P1||P2)). auto.
  }
  apply (P_MP (P2::L3') _ _ P Q).
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (P2 :: Q :: L3').
  apply (IHPQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  apply P_Conj. apply (IHP P1 P2); auto. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_rhs. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_CP. rewrite perm_swap. apply (IHP P1 P2); auto.
  rewrite HPerm. perm.
Qed.

Lemma P_union_elimL_rhs:
  forall P L1 o t1 t2,
    Proves ((o::= (tU t1 t2))::L1) P 
    -> Proves ((o ::= t2)::L1) P.
Proof.
  intros P L1 o t1 t2 HProves.
  remember (o ::= tU t1 t2 :: L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert o t1 t2 L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t3 t4 o1 HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t3 t4 π x HP IHP Hperm | (* P_PairElim *)
       L t o1 HIn | (* P_Top *)
       L t3 t4 o1 HP IHP | (* P_Union_lhs *)
       L t3 t4 o1 HP IHP | (* P_Union_rhs *)
       L1 t3 t4 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o' HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o1 HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros o t1 t2 L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Union_rhs. eapply P_Axiom. crush. 
  eapply P_Axiom. crush.
- intros o t1 t2  L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. crush.
  apply (P_Contradiction _ P (o ::= t2) P2). 
  eapply contra_unionL_rhs. eauto. crush. crush.
  destruct HIn2 as [Heqor | HIn2]. subst P2. 
  apply (P_Contradiction _ P (o ::= t2) P1).
  clear HeqHneq.
  apply Contradictory_sym in HContra.
  eapply contra_unionL_rhs. eauto. crush. crush.
  apply (P_Contradiction _ P P1 P2); crush.
- intros o t1 t2  L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o1 (tU t3 t4))).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  eapply (P_UnionElim (Elem (istype o t2)::L3') _ P t3 t4 o1).
  rewrite perm_swap. eapply (IH1 o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite perm_swap. eapply (IH2 o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros o t1 t2  L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t3 t4))).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  eapply (P_PairElim (Elem (istype o t2)::L3') _ P t3 t4 π x).
  swap (Elem (istype o t2) :: Elem (istype (obj π x) tCons)
             :: Elem (istype (obj (π ++ [car]) x) t3)
             :: Elem (istype (obj (π ++ [cdr]) x) t4) :: L3').
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. subst.
  apply (P_Top _ t2 o1). crush.
  apply (P_Top _ t o1). crush.
- intros o t1 t2 L1 HPerm. 
  apply P_Union_lhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Union_rhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L3 HPerm. 
  apply P_Pair. 
  apply (IHPcar o t1 t2 L3); auto.
  apply (IHPcdr o t1 t2 L3); auto.
  apply (IHPcons o t1 t2 L3); auto.
- intros o t1 t2 L3 HPerm. 
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. crush. 
- intros o t1 t2  L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o1). crush. 
- intros; apply P_True.
- intros o t1 t2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. crush. 
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. 
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_Simpl (Elem (istype o t2)::L3') _ R P Q).
  swap ((Elem (istype o t2)) :: P :: Q :: L3').
  apply (IH o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_DisjElim (Elem (istype o t2)::L3') _ _ P Q).
  swap (Elem (istype o t2) :: P :: L3').
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  swap (Elem (istype o t2) :: Q :: L3').
  apply (IHQ o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq. 
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))). auto.
  }
  apply (P_MP (Elem (istype o t2)::L3') _ _ P Q).
  apply (IHP o t1 t2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (Elem (istype o t2) :: Q :: L3').
  apply (IHPQ o t1 t2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros o t1 t2 L1 HPerm. 
  apply P_Conj. apply (IHP o t1 t2); auto.
  apply (IHQ o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Add_lhs. apply (IHP o t1 t2); auto.
- intros o t1 t2 L1 HPerm. 
  apply P_Add_rhs. apply (IHQ o t1 t2); auto.
- intros o t1 t2 L1 HPerm.
  apply P_CP. 
  rewrite perm_swap.
  apply (IHP o t1 t2); auto.
  rewrite HPerm. perm.
Qed.


Lemma P_conj_elimL:
  forall P1 P2 P3 L1,
    Proves ((P1 && P2)::L1) P3 
    -> Proves (P1::P2::L1) P3.
Proof.
  intros P1 P2 P L1 HProves.
  remember (P1 && P2::L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert P1 P2 L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros P1 P2 L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Conj. eapply P_Axiom. crush. 
  eapply P_Axiom. crush.
  eapply P_Axiom. right; right; crush.
- intros P3 P4 L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. inversion HContra. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. inversion HContra. 
  apply (P_Contradiction _ P P1 P2); crush.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))).
    apply Permutation_cons_inv with (a:=(P1 && P2)). auto.
  }
  eapply (P_UnionElim (P1::P2::L3') _ P t1 t2 o).
  swap (P1 :: P2 :: Elem (istype o t1) :: L3').
  eapply (IH1 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  swap (P1 :: P2 :: Elem (istype o t2) :: L3').
  eapply (IH2 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t1 t2))).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  eapply (P_PairElim (P1::P2::L3') _ P t1 t2 π x).
  swap (P1 :: P2 :: Elem (istype (obj π x) tCons)
                  :: Elem (istype (obj (π ++ [car]) x) t1)
                  :: Elem (istype (obj (π ++ [cdr]) x) t2) :: L3').
  eapply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Top _ t o). right; right; auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_rhs. apply (IHP P1 P2); auto.
- intros P1 P2 L2 HPerm.
  apply P_Pair. apply (IHPcar P1 P2); auto.
  apply (IHPcdr P1 P2); auto.
  apply (IHPcons P1 P2); auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. right; right; auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o). right; right; auto.
- intros P1 P2 L1 HPerm. apply P_True.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. right; right; auto.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. subst. rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_Simpl (P1::P2::L3') _ R P Q).
  swap (P1 :: P2 :: P :: Q :: L3').
  apply (IH P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_DisjElim (P1::P2::L3') _ _ P Q).
  swap (P1 :: P2 :: P :: L3').
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  swap (P1 :: P2 :: Q :: L3').
  apply (IHQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_MP (P1::P2::L3') _ _ P Q).
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (P1 :: P2 :: Q :: L3').
  apply (IHPQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  apply P_Conj. apply (IHP P1 P2); auto. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_rhs. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_CP. 
  swap (P1 :: P2 :: P :: L1).
  apply (IHP P1 P2); auto.
  rewrite HPerm. perm.
Qed.

Lemma P_impl_antecedent_weak:
  forall P1 P2 P3 L1,
    Proves ((P1 =-> P2)::L1) P3 ->
    Proves (P2::L1) P3.
Proof.
  intros P1 P2 P3 L1 HProves.
  remember ((P1 =-> P2)::L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert L1 HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P3 P4 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros L3 HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_CP. eapply P_Axiom. crush. 
  eapply P_Axiom. crush.
- intros L1 HPerm.  
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P3. inversion HContra. 
  destruct HIn2 as [Heqor | HIn2]. subst P4. inversion HContra. 
  apply (P_Contradiction _ P P3 P4); crush.
- intros L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))).
    apply Permutation_cons_inv with (a:=(P1 =-> P2)). auto.
  }
  eapply (P_UnionElim (P2::L3') _ P t1 t2 o).
  swap (P2 :: Elem (istype o t1) :: L3').
  eapply IH1. rewrite HPerm1. rewrite HPerm''. perm.   
  swap (P2 :: Elem (istype o t2) :: L3').
  eapply IH2. rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t1 t2))).
    apply Permutation_cons_inv with (a:=(P1=->P2)). auto.
  }
  eapply (P_PairElim (P2::L3') _ P t1 t2 π x).
  swap (P2 :: Elem (istype (obj π x) tCons)
           :: Elem (istype (obj (π ++ [car]) x) t1)
           :: Elem (istype (obj (π ++ [cdr]) x) t2) :: L3').
  apply IHP. rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Top _ t o). right; auto.
- intros; apply P_Union_lhs; crush. 
- intros; apply P_Union_rhs; crush. 
- intros. apply P_Pair; crush. 
- intros L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. crush. 
- intros L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o). crush. 
- intros; apply P_True.
- intros L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. crush. 
- intros L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. 
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=(P1=->P2)). auto.
  }
  apply (P_Simpl (P2::L3') _ R P Q).
  swap (P2 :: P :: Q :: L3').
  apply IH. rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=(P1=->P2)). auto.
  }
  apply (P_DisjElim (P2::L3') _ _ P Q).
  swap (P2 :: P :: L3').
  apply IHP. rewrite HPerm1. rewrite HPerm''. perm.
  swap (P2 :: Q :: L3').
  apply IHQ. rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. subst. rewrite <- HPerm1. assumption.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=(P1=->P2)). auto.
  }
  apply (P_MP (P2::L3') _ _ P Q).
  apply IHP. rewrite HPerm1. rewrite HPerm''. auto.
  swap (P2 :: Q :: L3').
  apply IHPQ. rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros  L1 HPerm. apply P_Conj; crush. 
- intros L1 HPerm. apply P_Add_lhs; crush.
- intros L1 HPerm. apply P_Add_rhs; crush.
- intros L1 HPerm.
  apply P_CP. 
  swap (P2 :: P :: L1).
  apply IHP; auto.
  rewrite HPerm. perm.
Qed.

Lemma P_PairElimL : forall L1 P t1 t2 π x,
Proves (((obj π x) ::= (tPair t1 t2))::L1) P
-> Proves (((obj π x) ::= tCons)
             ::((obj (π ++ [car]) x) ::= t1)
             ::((obj (π ++ [cdr]) x) ::= t2)
             ::L1) 
          P.
Proof.
  intros L1 P t1 t2 π x HProves.
  remember (obj π x ::= tPair t1 t2 :: L1) as L2 in HProves.
  apply eq_then_Permutation in HeqL2.
  revert L1 t1 t2 π x HeqL2.
  induction HProves as
      [L P HIn | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros L1 t1 t2 π x HPerm.
  rewrite HPerm in HIn. destruct HIn as [Heq | HIn].
  rewrite <- Heq. apply P_Pair; eapply P_Axiom; crush. 
  apply P_Axiom. crush.
- intros L1 t1 t2 π x HPerm.
  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq. clear HeqHneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. crush.
  

  apply (P_Contradiction _ P (Elem (istype (obj π x) (tPair t1 t2))) P2). auto.
  eapply contra_unionL_lhs. eauto. crush. crush.
  destruct HIn2 as [Heqor | HIn2]. subst P2. 
  apply (P_Contradiction _ P (o ::= t1) P1).
  clear HeqHneq.
  apply Contradictory_sym in HContra.
  eapply contra_unionL_lhs. eauto. crush. crush.
  apply (P_Contradiction _ P P1 P2); crush.








  rewrite HPerm in HIn1, HIn2.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct HIn1 as [Heqor | HIn1]. subst P1. 
  destruct HIn2 as [Heqor | HIn2]. subst P2. 
  crush.
  apply (P_Contradiction _ P P1 P2); crush.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype o (tU t1 t2))).
    apply Permutation_cons_inv with (a:=(P1 && P2)). auto.
  }
  eapply (P_UnionElim (P1::P2::L3') _ P t1 t2 o).
  swap (P1 :: P2 :: Elem (istype o t1) :: L3').
  eapply (IH1 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  swap (P1 :: P2 :: Elem (istype o t2) :: L3').
  eapply (IH2 P1 P2). rewrite HPerm1. rewrite HPerm''. perm.   
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=Elem (istype (obj π x) (tPair t1 t2))).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  eapply (P_PairElim (P1::P2::L3') _ P t1 t2 π x).
  swap (P1 :: P2 :: Elem (istype (obj π x) tCons)
                  :: Elem (istype (obj (π ++ [car]) x) t1)
                  :: Elem (istype (obj (π ++ [cdr]) x) t2) :: L3').
  eapply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm in HPerm'.
  remember HPerm' as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Top _ t o). right; right; auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Union_rhs. apply (IHP P1 P2); auto.
- intros P1 P2 L2 HPerm.
  apply P_Pair. apply (IHPcar P1 P2); auto.
  apply (IHPcdr P1 P2); auto.
  apply (IHPcons P1 P2); auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Fun _ x1 t1a t1r p1 o1); auto. right; right; auto.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply (P_Bot _ _ o). right; right; auto.
- intros P1 P2 L1 HPerm. apply P_True.
- intros P1 P2 L1 HPerm.
  destruct (In_perm _ _ HIn) as [L' HPerm'].
  rewrite HPerm' in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  apply P_False. right; right; auto.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm2 in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq. subst. rewrite <- HPerm1. auto.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=(P&&Q)).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_Simpl (P1::P2::L3') _ R P Q).
  swap (P1 :: P2 :: P :: Q :: L3').
  apply (IH P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. 
  inversion Heq; subst.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P||Q).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_DisjElim (P1::P2::L3') _ _ P Q).
  swap (P1 :: P2 :: P :: L3').
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  swap (P1 :: P2 :: Q :: L3').
  apply (IHQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L3 HPerm.
  rewrite <- Hperm in HPerm.
  remember HPerm as HPerm2. clear HeqHPerm2.
  apply cons_perm in HPerm2.
  destruct HPerm2 as [[Heq HPerm1] | [HIn1 HIn2]]. inversion Heq.
  destruct (In_perm _ _ HIn1) as [L3' HPerm3].
  destruct (In_perm _ _ HIn2) as [L1' HPerm1].
  assert (Permutation L1' L3') as HPerm''.
  {
    rewrite HPerm3 in HPerm. rewrite HPerm1 in HPerm.
    rewrite perm_swap in HPerm.
    apply Permutation_cons_inv with (a:=P=->Q).
    apply Permutation_cons_inv with (a:=(P1&&P2)). auto.
  }
  apply (P_MP (P1::P2::L3') _ _ P Q).
  apply (IHP P1 P2). rewrite HPerm1. rewrite HPerm''. auto.
  swap (P1 :: P2 :: Q :: L3').
  apply (IHPQ P1 P2). rewrite HPerm1. rewrite HPerm''. perm.
  rewrite HPerm3. perm.
- intros P1 P2 L1 HPerm.
  apply P_Conj. apply (IHP P1 P2); auto. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_lhs. apply (IHP P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_Add_rhs. apply (IHQ P1 P2); auto.
- intros P1 P2 L1 HPerm.
  apply P_CP. 
  swap (P1 :: P2 :: P :: L1).
  apply (IHP P1 P2); auto.
  rewrite HPerm. perm.
Qed.
  


Lemma P_contr : forall P1 P2 L1,
Proves (P1::P1::L1) P2
-> Proves (P1::L1) P2.
Proof.
intro P1.
induction P1 as (KP1,HI_rank) using (well_founded_ind (well_founded_ltof _ formula_weight)).
intros KP2 KL1 HProves.
remember (KP1::KP1::KL1) as KL2 in HProves.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction HProves as
      [L1 L2 P Hperm | (* P_Axiom *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2 Hperm| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm | (* P_PairElim *)
       L t o HIn | (* P_Top *)
       L t1 t2 o HP IHP | (* P_Union_lhs *)
       L t1 t2 o HP IHP | (* P_Union_rhs *)
       L1 t1 t2 π x HPcar IHPcar HPcdr IHPcdr HPCons IHPcons | (* P_Pair *)
       L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o HIn HPa IHPa HPr IHPr HPp IHPp | (* P_Fun *)
       L P o HIn | (* P_Bot *)
       L | (* P_True *)
       L P HIn | (* P_False *)
       L1 L2 R P Q Hperm IH Hperm2 | (* P_Simpl *)
       L1 L2 R P Q HPP IHP HPQ IHQ Hperm| (* P_DisjElim *)
       L1 L2 R P Q HP IHP HPQ IHPQ Hperm | (* P_MP *)
       L P Q HP IHP HQ IHQ | (* P_Conj *)
       L P Q HP IHP | (* P_Add_lhs *)
       L P Q HQ IHQ | (* P_Add_rhs *)
       L P Q HP IHP] (* P_CP *).
- intros KL1 HPerm.
  rewrite HPerm in Hperm.
  apply contr_perm in Hperm.
  destruct Hperm as [(Hperm1,Hperm2) | (KL2',(Hperm1,Hperm2))].
  subst KP1. apply (P_Axiom KL1). auto. 
  rewrite Hperm1. eapply (P_Axiom (KP1::KL2')). perm. 
- intros KL1 HPerm.
  remember (Contradictory_neq _ _ HContra) as Hneq.
  destruct (both_in_perm _ _ _ _ _ HIn1 HIn2 Hneq HPerm) 
    as [[Heq HIn] | [[Heq HIn] | [HIn1' HIn2']]].
  subst KP1.
  apply (P_Contradiction _ _ P1 P2); crush.
  subst KP1.
  apply (P_Contradiction _ _ P1 P2); crush.
  apply (P_Contradiction _ _ P1 P2); crush.
- intros KL1 HPerm.
  rewrite HPerm in Hperm.
  apply contr_perm in Hperm.
  destruct Hperm as [(Hperm1,Hperm2) | (KL2',(Hperm1,Hperm2))].
  subst KP1. 
  eapply (P_UnionElim _ _ _ t1 t2 o).
  apply HI_rank. unfold ltof. crush.

  eapply P_UnionElim.
  apply HI_rank.
 exact HP1. exact HP2.

clear HPerm. clear L2.
  assert 
    (forall KL0 : list formula,
       Permutation 
         (Elem (istype o t1) :: KL1)
         (Elem (istype o (tU t1 t2)) :: KL0) ->
       Proves (Elem (istype o (tU t1 t2)) :: KL0) P) as IH1'.
  {
    intros KL0 HP. apply IH1. rewrite <- HP.
    rewrite Hperm2. perm.
  } clear IH1.
  assert 
    (forall KL0 : list formula,
       Permutation 
         (Elem (istype o t2) :: KL1)
         (Elem (istype o (tU t1 t2)) :: KL0) ->
       Proves (Elem (istype o (tU t1 t2)) :: KL0) P) as IH2'.
  {
    intros KL0 HP. apply IH2. rewrite <- HP.
    rewrite Hperm2. perm.
  } clear IH2.
  rewrite Hperm2 in *.
  apply IH1'.
  rewrite HPerm. rewrite perm_swap.
  apply IH1. rewrite Hperm2. perm.
  a
rewrite Hperm2 in HP1. rewrite Hperm2 in HP2.
  

  apply HI_rank. unfold ltof. simpl.
  Check P_UnionElim.
  
rewrite Hperm2 in IH1. subst L1. clear IH1. clear IH2.
  rewrite Hperm2 in HP1. rewrite Hperm2 in HP2.
  apply (P_UnionElim L2 _ _ t1 t2 o); auto.
  apply HI_rank. unfold ltof. crush.
  apply HI_rank. unfold ltof. crush. 
  apply HI_rank. unfold ltof. crush.
  apply HI_rank. unfold ltof. crush.

  apply IH1.

  (* BOOKMARK *)


Fixpoint replicate{A:Type} (n:nat) (a:A):list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Lemma In_replicate_eq: forall{A:Type} (a b:A) (n:nat), In a (replicate n b) -> a = b.
Proof.
intros A a b n.
induction n.
- intros [].
- intros [H|H].
  + congruence.
  + apply IHn,H.
Qed.

Lemma LJ_cut_permselect:
  forall(P1 P2:PProp) (L1 L2:list PProp) (n:nat),
    Permutation (P1::L1) (replicate n P2++L2) ->
      (
        P1 = P2 /\ match n with
        | O => False
        | S n' => Permutation L1 (replicate n' P2++L2)
        end
      ) \/ (
        exists L2',
          Permutation L2 (P1::L2') /\
          Permutation L1 (replicate n P2++L2')
      ).
Proof.

Lemma LJ_cut_permselect_nil:
  forall(P1 P2:PProp) (L2:list PProp) (n:nat),
    Permutation (P1::nil) (replicate n P2++L2) ->
      (
        P1 = P2 /\ n = 1 /\ L2 = nil
      ) \/ (
        n = 0 /\ L2 = (P1::nil)
      ).

Lemma LJ_disj_elim2_withcut:
  forall P1 P2 P3 L1 L2,
    (forall PA LA1 LA2,
      LJ_provable LA1 P1 -> LJ_provable (P1::LA2) PA -> LJ_provable (LA1++LA2) PA) ->
    (forall PA LA1 LA2,
      LJ_provable LA1 P2 -> LJ_provable (P2::LA2) PA -> LJ_provable (LA1++LA2) PA) ->
    LJ_provable L1 (PPdisj P1 P2) ->
    LJ_provable (P1::L2) P3 ->
    LJ_provable (P2::L2) P3 ->
    LJ_provable (L1++L2) P3.
Proof.


Lemma LJ_weakN: forall P1 L1 L2, LJ_provable L1 P1 -> LJ_provable (L2++L1) P1.
Proof.
intros P1 L1 L2 H.
induction L2.
- exact H.
- apply LJ_weak,IHL2.
Qed.

Lemma LJ_contrN: forall P1 L1 L2, 
Proves (L2++L2++L1) P1 -> LJ_provable (L2++L1) P1.
Proof.
intros P1 L1 L2 H.
revert L1 H.
induction L2.
- intros L1 H.
  exact H.
- intros L1 H.
  LJ_reorder_antecedent (L2++(a::L1)).
  apply IHL2.
  LJ_reorder_antecedent (a::L2++L2++L1).
  apply LJ_contr.
  LJ_reorder_antecedent ((a::L2)++(a::L2)++L1).
  (* If we define an ++ s.t. it is associative/commutative
     and it removes duplicates, then we can turn
     (a::L2++L2++L1) into 
     ((a::L2)++(a::L2)++L1)
     since the a's would cancel/simplify *)
  exact H.
Qed.


Lemma LJ_bot_elim: forall P1 L1, LJ_provable L1 PPbot -> LJ_provable L1 P1.
Proof.
intros P1 L1 H.
remember PPbot as P2 in H.
induction H.

Lemma LJ_conj_elim_l:
  forall P1 P2 L1,
    LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P1.
Proof.
intros P1 P2 L1 H.
remember (PPconj P1 P2) as P3 in H.
induction H.


Lemma LJ_conj_elim_r:
  forall P1 P2 L1,
    LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P2.
Proof.
intros P1 P2 L1 H.
remember (PPconj P1 P2) as P3 in H.
induction H.


Lemma LJ_cut_general:
  forall P1 P2 L1 L2 n,
    LJ_provable L1 P1 ->
    LJ_provable (replicate n P1++L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 KL2 n HPrL HPrR.
remember (replicate n KP1 ++ KL2) as KL3 in HPrR.
assert (HKL3: Permutation KL3 (replicate n KP1 ++ KL2)) by (rewrite HeqKL3; reflexivity).
clear HeqKL3.
revert KL1 KL2 n HKL3 HPrL.
induction HPrR.



Lemma LJ_cut2:
  forall P1 P2 L1 L2,
    LJ_provable L1 P1 ->
    LJ_provable (P1::L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
intros P1 P2 L1 L2.
apply LJ_cut_general with (n:=1).
Qed.


Theorem LJ_cut:
  forall P1 P2 L1,
    LJ_provable L1 P1 ->
    LJ_provable (P1::L1) P2 ->
    LJ_provable L1 P2.
Proof.
intros P1 P2 L1 HPrL HPrR.
rewrite (app_nil_end L1).
apply LJ_contrN.
rewrite app_nil_r.
revert HPrL HPrR.
apply LJ_cut2.
Qed.