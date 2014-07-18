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


(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

Inductive Contradictory : relation formula :=
| contratype : forall o t1 t2,
~CommonSubtype (t1,t2)
-> Contradictory (o ::= t1) (o ::= t2).

(** ** Proves Relation *)

Inductive Proves : list formula -> formula -> Prop :=
| P_Axiom :
    forall L1 L2 P,
      Permutation (P::L1) L2
      -> Proves L2 P
| P_Weak :
    forall L1 L2 P Q,
      Proves L1 Q
      -> Permutation (P::L1) L2
      -> Proves L2 Q
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
       Proves (L1) P
       -> Proves (P::Q::L1) R
       -> Permutation ((P --> Q)::L1) L2
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
       -> Proves L (P --> Q).

Definition Subtype (t1 t2:type) := 
  Proves [((var (Id 0)) ::= t1)] ((var (Id 0)) ::= t2).

Definition Implies (p1 p2:prop) : Prop :=
Proves [(assume p1)] (question p2).

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

Theorem P_Perm : forall L1 L2 P,
Proves L1 P
-> Permutation L1 L2
-> Proves L2 P.
Proof.
  intros L1 L2 P HL1.
  generalize dependent L2.
  induction HL1 as 
      [L1 L2 P Hperm | (* P_Axiom *)
       L1 L2 P Q Hproves IH Hperm | (* P_Weak *)
       L P P1 P2 HContra HIn1 HIn2 | (* P_Contradiction *)
       L1 L2 P t1 t2 o HP1 IH1 HP2 IH2| (* P_UnionElim *)
       L1 L2 P t1 t2 π x HP IHP Hperm IHp | (* P_PairElim *)
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
       L1 L2 R P HP IHP Q HQ IHQ | (* P_MP *)
       L P HP Q HQ | (* P_Conj *)
       L P HP Q HQ | (* P_Add_lhs *)
       L P HP Q HQ | (* P_Add_rhs *)
       L P HP Q HQ] (* P_CP *).
- intros L HPerm.
  eapply P_Axiom. eauto.
  eapply Permutation_trans; eauto.
- intros L' HPerm.
  eapply P_Weak with (P:=P). eauto.
  eapply Permutation_trans; eauto.
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
- 


Lemma LJ_cut2:
  forall P1 P2 L1 L2,
    LJ_provable L1 P1 ->
    LJ_provable (P1::L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
intros P1 P2 L1 L2.
apply LJ_cut_general with (n:=1).
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