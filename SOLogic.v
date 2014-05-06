

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
Require Import Bool.

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

Record fact : Type := mkFact {
  fbool : bool;
  fvar  : id;
  fprop : X
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

Inductive ψ : Type :=
| ψfact : fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ.


Theorem ψ_eqdec : forall p1 p2 : ψ,
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality.
Defined.
Hint Resolve ψ_eqdec.

Theorem ψψ_eqdec : forall p1 p2 : (ψ * ψ),
{p1 = p2}+{p1 <> p2}.
Proof.
  decide equality.
Defined.
Hint Resolve ψψ_eqdec.


Fixpoint ψsize (p:ψ) : nat :=
match p with
| ψimpl p q => 1 + ψsize p + ψsize q
| ψor   p q => 1 + ψsize p + ψsize q
| ψand  p q => 1 + ψsize p + ψsize q
| _ =>  1
end.

Definition ψψsize (p:ψ*ψ) : nat :=
(ψsize (fst p)) + (ψsize (snd p)).

Fixpoint ψlistsize (l:list ψ) : nat :=
match l with
| nil => 0
| x :: xs => ψsize x + ψlistsize xs
end.
Hint Unfold ψlistsize.

Fixpoint ψψlistsize (l:list (ψ*ψ)) : nat :=
match l with
| nil => 0
| xx :: xxs => ψψsize xx + ψψlistsize xxs
end.
Hint Unfold ψψlistsize.

Definition boolsize (b:bool) : nat :=
match b with
| false => 0
| true  => 1
end.
Hint Unfold boolsize.

(*
Implication simplification:
A \/ B -> C ==> A -> C, B -> C Sort of Case Analysis
A /\ B -> C ==> A -> (B -> C) Exportation
tt -> C ==> C
ff -> C ==> nil

(A -> B) -> C  ==> (A -> B) -> C   (no change)


*)

Record Γ : Type := mkΓ {
  ff_proven : bool;
  Γfacts : list fact;
  Γimpls : list (ψ * ψ);
  Γdisjs : list (ψ * ψ)
}.

Definition Γsize (Ε:Γ) : nat :=
boolsize (ff_proven Ε) +
length (Γfacts Ε) +
ψψlistsize (Γimpls Ε) +
ψψlistsize (Γdisjs Ε).

(*
Inductive Γ : Type :=
| Γnil  : Γ
| Γfact : fact -> Γ -> Γ
| Γimpl : ψ -> ψ -> Γ -> Γ
| Γor   : ψ -> ψ -> Γ -> Γ
| Γff   : Γ -> Γ.

Fixpoint Γsize (E:Γ) : nat :=
match E with
| Γnil  => 0
| Γfact _ rest => 1 + Γsize rest
| Γimpl p q rest => ψsize p + ψsize q + Γsize rest
| Γor p q rest => ψsize p + ψsize q + Γsize rest
| Γff rest => 1 + Γsize rest
end.

Fixpoint inΓ (prop:ψ) (E:Γ) : bool :=
match E with
| Γnil  => false
| Γfact f rest => if (ψ_eqdec prop (ψfact f)) 
                  then true
                  else inΓ prop rest
| Γimpl p q rest => if (ψ_eqdec prop (ψimpl p q)) 
                    then true
                    else inΓ prop rest
| Γor p q rest => if (ψ_eqdec prop (ψor p q)) 
                  then true
                  else inΓ prop rest
| Γff rest => if (ψ_eqdec prop ψff) 
              then true
              else inΓ prop rest
end.

Fixpoint addψ (prop:ψ) (E:Γ) : Γ :=
match inΓ prop E, prop with
| true , _ => E
| _ , ψfact f => Γfact f E
| _ , ψimpl p q => Γimpl p q E
| _ , ψor p q => Γor p q E
| _ , ψand p q => addψ p (addψ q E)
| _ , ψff => Γff E
| _ , ψtt => E
end.


Fixpoint removeψ (prop:ψ) (E:Γ) : Γ :=
match E with
| Γnil  => Γnil
| Γfact f rest => if (ψ_eqdec prop (ψfact f)) 
                  then removeψ prop rest
                  else Γfact f (removeψ prop rest)
| Γimpl p q rest => if (ψ_eqdec prop (ψimpl p q)) 
                    then removeψ prop rest
                    else Γimpl p q (removeψ prop rest)
| Γor p q rest => if (ψ_eqdec prop (ψor p q)) 
                  then removeψ prop rest
                  else Γor p q (removeψ prop rest)
| Γff rest => if (ψ_eqdec prop ψff)
              then removeψ prop rest
              else Γff (removeψ prop rest)
end.
*)

Theorem impl_gt_parts : forall p q,
ψsize (ψimpl p q) > ψsize p + ψsize q.
Proof.
  induction p; crush.
Qed.
Hint Resolve impl_gt_parts.

Theorem and_gt_parts : forall p q,
ψsize (ψand p q) > ψsize p + ψsize q.
Proof.
  induction p; crush.
Qed.
Hint Resolve and_gt_parts.

Theorem or_gt_parts : forall p q,
ψsize (ψor p q) > ψsize p + ψsize q.
Proof.
  induction p; crush.
Qed.
Hint Resolve or_gt_parts.

Fixpoint inΓ (prop:ψ) (E:Γ) : bool :=
match prop with
| ψfact f => if in_dec fact_eqdec f (Γfacts E) then true else false
| ψimpl p q => if in_dec ψψ_eqdec (p, q) (Γimpls E) then true else false
| ψor p q => if in_dec ψψ_eqdec (p, q) (Γdisjs E) then true else false
| ψand p q => andb (inΓ p E) (inΓ q E)
| ψff => (ff_proven E)
| ψtt => true
end.

Definition set_ff (b:bool) (E:Γ) : Γ :=
mkΓ b
    (Γfacts E)
    (Γimpls E)
    (Γdisjs E).

Definition add_fact (f:fact) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (set_add fact_eqdec f (Γfacts E))
    (Γimpls E)
    (Γdisjs E).
Hint Unfold add_fact.


Definition remove_fact (f:fact) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (set_remove fact_eqdec f (Γfacts E))
    (Γimpls E)
    (Γdisjs E).
Hint Unfold remove_fact.

Definition add_impl (pp:(ψ*ψ)) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (Γfacts E)
    (set_add ψψ_eqdec pp (Γimpls E))
    (Γdisjs E).
Hint Unfold add_impl.

Definition remove_impl (pp:(ψ*ψ)) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (Γfacts E)
    (set_remove ψψ_eqdec pp (Γimpls E))
    (Γdisjs E).
Hint Unfold remove_impl.

Definition add_disj (pp:(ψ*ψ)) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (Γfacts E)
    (Γimpls E)
    (set_add ψψ_eqdec pp (Γdisjs E)).
Hint Unfold add_disj.


Definition remove_disj (pp:(ψ*ψ)) (E:Γ) : Γ :=
mkΓ (ff_proven E)
    (Γfacts E)
    (Γimpls E)
    (set_remove ψψ_eqdec pp (Γdisjs E)).
Hint Unfold remove_disj.

(* TODO: Theorems about size changes from each add/remove? *)

Fixpoint addψ (prop:ψ) (E:Γ) : Γ :=
match prop with
| ψfact f => add_fact f E
| ψimpl p q => add_impl (p, q) E
| ψor p q => add_disj (p, q) E
| ψand p q => addψ p (addψ q E)
| ψff => (set_ff true E)
| ψtt => E
end.
Hint Unfold addψ.


Fixpoint removeψ (prop:ψ) (E:Γ) : Γ :=
match prop with
| ψfact f => remove_fact f E
| ψimpl p q => remove_impl (p, q) E
| ψor p q => remove_disj (p, q) E
| ψand p q => removeψ p (removeψ q E)
| ψff => (set_ff false E)
| ψtt => E
end.
Hint Unfold removeψ.


Lemma set_removal_length {A:Type} : forall Adec (x:A) xs,
In x xs ->
length (set_remove Adec x xs) < length xs.
Proof.
  induction xs. intros. tryfalse.
  intros.
  simpl.
  destruct (Adec x a). crush. 
  simpl. inversion H; subst; crush. 
Qed.
Hint Resolve set_removal_length.

Lemma set_removal_length2 {A:Type} : forall Adec (x:A) xs,
length (set_remove Adec x xs) <= length xs.
Proof.
  induction xs. simpl. omega.
  simpl.
  destruct (Adec x a). crush. 
  simpl. omega.
Qed.
Hint Resolve set_removal_length2.


Theorem ψsize_min : forall p : ψ,
ψsize p > 0.
Proof.
  destruct p; crush.
Qed.  
Hint Resolve ψsize_min.

Theorem ψψsize_min : forall pp : (ψ*ψ),
ψψsize pp > 1.
Proof.
  intros pp.
  induction pp.
  unfold ψψsize. simpl.
  remember (ψsize_min a).
  remember (ψsize_min b).
  omega.
Qed.

Theorem ψψcons_size : forall pp pps,
ψψlistsize pps < ψψlistsize (pp :: pps).
Proof.
  intros pp pps.
  induction pps. simpl. 
  remember (ψψsize_min pp). omega.
  simpl. remember (ψψsize_min pp). omega.
Qed.

Lemma fremoval_size : forall f fs,
In f fs ->
length (set_remove fact_eqdec f fs) < length fs.
Proof.
  induction fs.
  crush.
  intros fin.
  simpl.
  destruct (fact_eqdec f a) as [faeq | faneq].
  subst. omega.
  destruct fin. tryfalse.
  crush.
Qed.    

Lemma ψremoval_size : forall p ps,
In p ps ->
ψlistsize (set_remove ψ_eqdec p ps) < ψlistsize ps.
Proof.
  induction ps. crush.
  intros Hin. inversion Hin; subst.
  simpl. destruct (ψ_eqdec p p); tryfalse.
  remember (ψsize_min p). omega.
  apply IHps in H. simpl. destruct (ψ_eqdec p a); tryfalse.
  remember (ψsize_min a). omega. simpl.
  remember (ψsize_min a). omega. 
Qed. 

Lemma ψψremoval_size : forall pp pps,
In pp pps ->
ψψlistsize (set_remove ψψ_eqdec pp pps) < ψψlistsize pps.
Proof.
  induction pps. crush.
  intros Hin. inversion Hin; subst.
  simpl. destruct (ψψ_eqdec pp pp); tryfalse.
  remember (ψψsize_min pp). omega.
  apply IHpps in H. simpl. destruct (ψψ_eqdec pp a); tryfalse.
  remember (ψψsize_min a). omega. simpl.
  remember (ψψsize_min a). omega. 
Qed. 

Lemma not_In_cons {A:Type} : forall xs (x a:A),
(~ In x (a :: xs)) ->
~ In x xs.
Proof.
  induction xs.
  intros. intros contra. tryfalse.
  intros. intros contra.
  apply H. right. auto.
Qed.

Lemma set_remove_not_In {A:Type} : forall Adec (x:A) xs,
~In x xs ->
set_remove Adec x xs = xs.
Proof.
  induction xs. intros. simpl. reflexivity.
  intros.
  simpl.
  destruct (Adec x a). crush.
  apply not_In_cons in H.
  crush.
Qed.
Hint Resolve set_remove_not_In.

Lemma ψremove_not_In : forall p E,
inΓ p E = false ->
removeψ p E = E.
Proof.
  induction p;
  intros; destruct E as [ffval facts impls ors].

  
  (* fact *)
  simpl. unfold remove_fact. simpl.
  (* BOOKMARK *)


Theorem removal_size : forall p E,
inΓ p E = true -> 
Γsize (removeψ p E) < Γsize E.
Proof.
  intro p.
  induction p as [f | p1 IH p2 | p1 IH p2 | p1 IHp2 | |];
  intros E HIn;
  destruct E as [ffval facts impls ors].
  
  (* p = fact *)
  simpl in *. 
  unfold remove_fact.
  simpl. remember (fremoval_size f facts) as Hrem.
  clear HeqHrem. unfold Γsize. simpl.
  destruct (in_dec fact_eqdec f facts) as [HIn2 | contra].
  crush. tryfalse.
  
  (* p = (ψimpl p1 p2) *)
  simpl in *. 
  unfold remove_impl.
  simpl. remember (ψψremoval_size (p1, p2) impls) as Hrem.
  clear HeqHrem. unfold Γsize. simpl.
  destruct (in_dec ψψ_eqdec (p1, p2) impls) as [HIn2 | contra].
  crush. tryfalse.

  (* p = (ψor p1 p2) *)
  simpl in *. 
  unfold remove_disj.
  simpl. remember (ψψremoval_size (p1, p2) ors) as Hrem.
  clear HeqHrem. unfold Γsize. simpl.
  destruct (in_dec ψψ_eqdec (p1, p2) ors) as [HIn2 | contra].
  crush. tryfalse.

  (* p = (ψand p1 p2) *)
  simpl in *. 
  remember {|
     ff_proven := ffval;
     Γfacts := facts;
     Γimpls := impls;
     Γdisjs := ors |} as E.
  apply andb_true_iff in HIn.
  destruct HIn as [Hp1In Hp2In].
  apply (IHp1 E) in Hp2In.
  remember (inΓ p1 (removeψ p2 E)) as p1b.
  destruct p1b. symmetry in Heqp1b.
  apply IHp2 in Heqp1b. omega.
  symmetry in Heqp1b.
  Check set_remove_not_In.
  forwards*: (set_remove_not_In ψ_eqdec p1 _).



Lemma remψ_notIn : forall p E,
inΓ p E = false ->
(removeψ p E) = E.
Proof.
  induction p;
  intros E H;
  destruct E as [ffval facts impls ors].

  simpl in *. unfold remove_fact. simpl.
  apply (IHp2 E) in Hp1In. 
  destruct (ψ_eqdec p1 p2) as [Hpeq | Hpneq].
  subst p1.
,
Lemma dbl_set_remove : forall X xs (x:X) xdec,
set_remove xdec x (set_remove xdec x xs) =
set_remove xdec x xs.
Proof.
  induction xs.
  simpl. reflexivity.
  intros x xdec. 
  destruct (in_dec xdec x (a :: xs)) as [HIn | HnIn].
  inversion HIn. subst. simpl.
  destruct (xdec x x).


unfold set_remove.
  simpl. destruct (xdec x a). eapply IHxs.
  subst. crush.


Lemma dbl_removeψ : forall p E,
(removeψ p (removeψ p E))
= (removeψ p E).
Proof.
  induction p.
  intros E.
  simpl. unfold remove_fact.
  simpl. omega.

Lemma 

  apply (IHp2 (removeψ p2 E)) in Hp1In.
  


  (* BOOKMARK *)



(* This is disgusting - we need more supporting lemmas! *)

Fixpoint try_impl (pq:(ψ*ψ)) (E:Γ) : Γ :=
match pq with
| pair p q => if andb (inΓ p E) (inΓ (ψimpl p q) E)
              then addψ q (removeψ (ψimpl p q) E)
              else E
end.

Theorem try_use_imply_size : forall p q E,
Γsize E <= Γsize (try_impl (p,q) E).
Proof.
  induction E.
  simpl.


(* tries to remove implications if antecedant is satisfied *)
Fixpoint tryimpls' (E1 E2 : Γ) : Γ :=
match E2 with
| Γnil  => Γnil
| Γfact f rest => Γfact f (tryimpls' E1 rest)
| Γimpl p q rest => if (inΓ p E1) 
                    then addψ q (tryimpls' E1 rest)
                    else Γimpl p q (tryimpls' E1 rest)
| Γor p q rest => Γor p q (tryimpls' E1 rest)
| Γff rest => Γff (tryimpls' E1 rest)
end.

Definition tryimpls (E:Γ) : Γ :=
tryimpls' E E.

Theorem impls_lessen_Γ : forall E,
Γsize (tryimpls E) <= Γsize E.
Proof.
  induction E.
  simpl. omega. crush.
  simpl. omega.


Fixpoint extendΓ (prop: P) (E:Env) : Env :=
match prop with
| ψfact f => 
| ψimpl p q => 
| ψor   p q => 
| ψand  p q => 
| _ =>  1



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







(*

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
*)







Definition inb {X:Type} (Xeqdec : forall x y : X, {x=y}+{x<>y}) (x:X) (l:list X) := if in_dec Xeqdec x l then true else false.

Fixpoint inEnv (prop:P) (E:Env) : bool :=
match prop with
| Implies p q => (inb P_eqdec prop (Implications E))
| Or p q => inb P_eqdec prop (Disjunctions E)
| And p q => andb (inEnv p E) (inEnv q E)
| _ => inb P_eqdec prop (Facts E)
end.

Definition Envsize (E:Env) : nat :=
Plistsize (Facts E) +
Plistsize (Implications E) +
Plistsize (Disjunctions E).

Definition simpl_env_add (prop:P) (E:Env) : Env :=
match prop with
| Valid f => 
| Invalid f => 1
| Implies p q => 1 + Psize p + Psize q
| Or p q => 1 + Psize p + Psize q
| And p q => 1 + Psize p + Psize q
| Absurd => 1
| Trivial => 1
end.



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
  
