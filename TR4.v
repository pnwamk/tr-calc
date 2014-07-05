(* begin hide *)
Require Import LibTactics.
Require Import List.
Require Import Permutation.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.
Require Import Coq.Program.Wf.
Require Import String.

Import ListNotations.
Open Scope list_scope.
(* end hide *)

Section LTR.
(** * Basic Definitions for λTR *)

(** Identifiers and objects: *)

Notation opt := option.
Definition boolean {P Q:Prop} (sb: sumbool P Q) : bool :=
if sb then true else false.

Inductive id : Set :=
  Id : nat -> id.

Inductive step : Set := car | cdr.
Hint Constructors step.

Definition path : Set := list step.

Inductive object : Set :=
| obj : path -> id -> object.
Hint Constructors object.

Notation var := (obj []).

(** Types and propositions: *)
(** Types and propositions: *)
Inductive type : Set :=
| tTop  : type
| tBot  : type
| tNat  : type
| tStr  : type
| tT    : type
| tF    : type
| tU    : type -> type -> type
| tCons : type -> type -> type
| tλ    : id -> type -> type -> prop -> opt object -> type

with prop : Set :=
| Atom : fact -> prop
| And  : prop -> prop -> prop
| Or   : prop -> prop -> prop
| Imp  : prop -> prop -> prop
| FF   : prop
| Unk  : prop

with fact : Set :=
| istype : object -> type -> fact.
Hint Constructors type prop fact.

Fixpoint Not (P:prop) : prop :=
  match P with
    | Atom f => (Imp (Atom f) FF)
    | And P Q => Or (Not P) (Not Q)
    | Or P Q  => And (Not P) (Not Q)
    | Imp P Q => And P (Not Q)
    | FF => (Imp FF FF)
    | Unk => Unk
  end.

Hint Resolve eq_nat_dec.

Notation tBool := (tU tT tF).

Infix "::=" := (fun o t => Atom (istype o t)) 
                 (at level 30, right associativity).
Infix "::~" := (fun o t => (Imp (Atom (istype o t)) FF))
                 (at level 30, right associativity).
Notation "P '&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Or P Q) (at level 50, left associativity).
Notation "P '-->' Q" := (Imp P Q) (at level 90).
Notation TT := (Imp FF FF).


(** Expressions and primitive operations: *)
Inductive const_op :=
  opAdd1 | opIsZero | opIsNat | opIsBool | opIsProc | 
  opIsCons | opIsStr | opStrLen | opPlus.
Hint Constructors const_op.

Inductive poly_op :=
 opCar | opCdr.
Hint Constructors poly_op.

Inductive op : Type :=
| c_op : const_op -> op
| p_op : poly_op -> op.
Hint Constructors op.

Inductive exp : Type :=
| eVar : id -> exp
| eOp  : op -> exp
| eTrue  : exp
| eFalse : exp
| eNat : nat -> exp
| eStr : string -> exp
| eIf  : exp -> exp -> exp -> exp
| eλ : id -> type -> exp -> exp
| eApp : exp -> exp -> exp
| eLet : id -> exp -> exp -> exp
| eCons : exp -> exp -> exp.
Hint Constructors exp.

Notation "$" := eVar.
Notation "#t" := eTrue.
Notation "#f" := eFalse.
Notation "#" := eNat.
Notation λ := eλ.
Notation Str := eStr.
Notation If := eIf.
Notation Let := eLet.
Notation Apply := eApp.
Notation Car  := (eApp (eOp (p_op opCar))).
Notation Cdr := (eApp (eOp (p_op opCdr))).
Notation Add1 := (eApp (eOp (c_op opAdd1))).
Notation "Zero?" := (eApp (eOp (c_op opIsZero))).
Notation "Nat?" := (eApp (eOp (c_op opIsNat))).
Notation "Bool?" := (eApp (eOp (c_op opIsBool))).
Notation "Proc?" := (eApp (eOp (c_op opIsProc))).
Notation "Cons?" := (eApp (eOp (c_op opIsCons))).
Notation Cons := eCons.
Notation "Str?" := (eApp (eOp (c_op opIsStr))).
Notation StrLen := (eApp (eOp (c_op opStrLen))).
Notation Plus := (fun x y =>
                    (eApp (eApp (eOp (c_op opPlus)) x) y)).


(** Decidable equality of defined types thus far: *)

Theorem id_eqdec : 
  forall (x y : id),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

Theorem step_eqdec : 
  forall (x y: step),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve step_eqdec.

Hint Resolve list_eq_dec.

Theorem path_eqdec : 
  forall (x y: path),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eqdec.

Theorem obj_eqdec : 
  forall (x y: object),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec.

Fixpoint type_eqdec (x y : type) : {x=y}+{x<>y}
with prop_eqdec (x y : prop) : {x=y}+{x<>y}
with fact_eqdec (x y : fact) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec fact_eqdec.


(** Environment Functions *)

(** Constant types: *)
Definition const_type (c : const_op) (x:id) : type :=
  match c with
    | opIsNat =>
      (tλ x 
          tTop tBool
          ((var x) ::= tNat)
          (Some (var x)))
    | opIsProc =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tλ x tBot tTop TT None)) 
          None)
    | opIsBool =>
      (tλ x 
          tTop tBool
          ((var x) ::= tBool)
          None)
    | opIsCons =>
      (tλ x 
          tTop tBool
          ((var x) ::= (tCons tTop tTop))
          None)
    | opAdd1 =>
      (tλ x 
          tNat tNat
          TT
          None)
    | opIsZero =>
      (tλ x 
          tNat tBool
          TT
          None)
    | opIsStr =>
      (tλ x 
          tTop tBool
          ((var x) ::= tStr)
          None)
    | opStrLen =>
      (tλ x 
          tStr tNat
          TT
          None)
    | opPlus =>
      (tλ x 
          tNat 
          (tλ x 
              tNat tNat
              TT
              None)
          TT
          None)
  end.

(** * Utility Functions 
 Substitution, free variable checking, etc... *)

Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y})
         (l:list (set X)) : set X :=
  match l with
    | nil => nil
    | x :: xs => set_union dec x (setU dec xs)
  end.

(** Free variable calculations: *)
(* free variables in objects *)
Definition fv_set_o (opto : opt object) : set id :=
  match opto with
    | None => []
    | Some (obj _ x) => [x]
  end.

(* free variables in types *)

Fixpoint fv_set_t (t : type) : set id :=
  match t with
    | tU lhs rhs =>
      set_union id_eqdec (fv_set_t lhs) (fv_set_t rhs)
    | tλ x t1 t2 p1 o =>
      setU id_eqdec
           [[x];
             (fv_set_t t1);
             (fv_set_t t2);
             (fv_set_p p1);
             (fv_set_o o)]
    | tCons t1 t2 =>
      set_union id_eqdec
                (fv_set_t t1)
                (fv_set_t t2)
    | _ => nil
  end

(* free variables in propositions *)
with fv_set_p (p: prop) : set id :=
  match p with
    | Atom f => fv_set_f f
    | p && q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p || q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | _ => nil
  end

with fv_set_f (f:fact) : set id :=
  match f with
    | istype o t => 
      set_union id_eqdec (fv_set_o (Some o)) (fv_set_t t)
  end.

(** Substitution functions: *)
Definition subst_o (o newobj: opt object) (z:id) : opt object :=
  match o with
    | None => None
    | Some (obj pth1 x) =>
      match id_eqdec x z, newobj with
        | left _, None => None
        | left _, Some (obj pth2 y) => Some (obj (pth1 ++ pth2) y)
        | right _, _ => o
      end
  end.


(** _we use true/false instead of +/- for substitution_ *)
Fixpoint subst_p'
         (b:bool)
         (p:prop)
         (opto:opt object)
         (x:id) : prop :=
  match p with
    | Atom f => 
      match (subst_f b f opto x) with
        | None => TT
        | Some f' => Atom f'
      end
    | P || Q => (subst_p' b P opto x) || (subst_p' b Q opto x)
    | P && Q => (subst_p' b P opto x) && (subst_p' b Q opto x)
    | _ => p
  end

with subst_f
       (b:bool)
       (f:fact)
       (opto:opt object)
       (x:id) : opt fact :=     
  match f with
    | istype (obj pth1 z) t =>
      match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
        | left _, _ =>
          match opto with
            | None => None
            | Some (obj pth2 y) =>
              Some (istype (obj (pth1 ++ pth2) y) (subst_t' b t opto x))
          end
        | right _, false => Some f
        | right _, true => None
      end
  end

with subst_t'
       (b:bool)
       (t:type)
       (opto:opt object)
       (x:id) : type :=
  match t with
    | tU lhs rhs => tU (subst_t' b lhs opto x) 
                       (subst_t' b rhs opto x)
    | tλ y t1 t2 p1 opto2 =>
      if id_eqdec x y
      then t
      else tλ y
                (subst_t' b t1 opto x)
                (subst_t' b t2 opto x)
                (subst_p' b p1 opto x)
                (subst_o opto2 opto x)
    | tCons t1 t2 => tCons (subst_t' b t1 opto x)
                           (subst_t' b t2 opto x)
    | _ => t
  end.

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 
Definition subst_p := subst_p' true.
Definition subst_t := subst_t' true.

Lemma split_nonnil {X:Type} : forall l1 l2 (x:X),
nil <> l1 ++ (x :: l2).
Proof.
  intros. destruct l1; destruct l2; crush.
Qed.


(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 

(** A few helpers to reason about subtyping: *)

Fixpoint is_tU (t:type) : opt (type * type) :=
  match t with
    | tU t1 t2 => Some (t1,t2)
    | _ => None
  end.

Lemma is_tU_eq : forall t t1 t2,
Some (t1,t2) = is_tU t
-> t = tU t1 t2.
Proof.
  intros.
  destruct t; crush.
Qed.
  
Fixpoint is_tλ (t:type) : opt (id * type * type * prop * (opt object)) :=
  match t with
    | tλ x t1 t2 p opto => Some (x,t1,t2,p,opto)
    | _ => None
  end.

Lemma is_tλ_eq : forall t x t1 t2 p opto,
Some (x,t1,t2,p,opto) = is_tλ t
-> t = tλ x t1 t2 p opto.
Proof.
  intros.
  destruct t; crush.
Qed.

Fixpoint is_tCons (t:type) : opt (type * type) :=
  match t with
    | tCons t1 t2 => Some (t1,t2)
    | _ => None
  end.

Lemma is_tCons_eq : forall t t1 t2,
Some (t1,t2) = is_tCons t
-> t = tCons t1 t2.
Proof.
  intros.
  destruct t; crush.
Qed.

Fixpoint type_weight (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      S (plus (type_weight t1) (type_weight t2))
    | tλ x t1 t2 _ _ => S (plus (type_weight t1) (type_weight t2))
    | tCons t1 t2 => S (plus (type_weight t1) (type_weight t2))
    | _ => 1
  end.

Program Fixpoint common_subtype (type1 type2:type)
        {measure (plus (type_weight type1) (type_weight type2))} : bool :=
  match type1, type2 with
    | tTop , _ => true
    | _, tTop => true
    | tBot, _ => false
    | _, tBot => false
    | tU t1 t2, _ => orb (common_subtype t1 type2) 
                         (common_subtype t2 type2)
    | _, tU t1 t2 => orb (common_subtype type1 t1) 
                         (common_subtype type1 t2)
    | tNat, tNat => true
    | tNat, _ => false
    | tStr, tStr => true
    | tStr, _ => false
    | tT, tT => true
    | tT, _ => false
    | tF, tF => true
    | tF, _ => false
    | tλ _ _ _ _ _, tλ _ _ _ _ _ => true
    | tλ _ _ _ _ _, _ => false
    | tCons t1 t2, tCons t3 t4 => andb (common_subtype t1 t3)
                                       (common_subtype t2 t4)
    | tCons _ _, _ => false
  end.
Solve Obligations using crush.

(*
TODO - We must prove all types have a principal type
if we're going to use this for Removed *)

(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

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

(** ** Proves Relation *)

(*** ***Proves Relation This relation "Proves Γ P" can be interpreted
    as follows: if we assume all propositions in Γ evaluate to true
    then E evaluates to true.

    This means "Unknown" propositions in Γ may not truly be of unknown
    value (i.e. we may be able to deduce their underlying value from
    the assumption that their containing formula is true). This merely
    means Unk values in Γ are like truth-functional variables that are
    not equal to any other truth-functional variables in the universe
    of discourse (i.e. if we infer some Unk is true, that fact alone
    does not imply any other Unk is true). On the right hand side of
    the relation (in the prop P), Unk propositions are *truly*
    unknown; It is impossible to deduce their truth value, and they
    merely are either ignored or act as barriers to what can be proven
    depending on their context (e.g. (P || Unk) can only be proven if
    P can be proven, and (P && Unk) can never be proven).  *)

Fixpoint rem (p:prop) (l:list prop) : list prop :=
  match l with
    | nil => nil
    | p' :: ps =>
      if prop_eqdec p p' 
      then ps
      else p' :: (rem p ps)
  end.

Inductive Proves : (list prop * prop) -> Prop :=
| P_SubType :
  forall t' t o Γ,
    SubType (t, t')
    -> In (Atom (istype o t')) Γ
    -> Proves (Γ, (Atom (istype o t)))
(*
| P_Absurd :
  forall P Q,
    (forall Γ, In Γ (poss_truth_tables P)
               -> Valid absurd_fact Γ)
    -> Proves P Q
*)
| P_False :
    forall Γ P,
      In FF Γ
      -> Proves (Γ, P)
| P_Simpl :
    forall Γ P Q R,
      In (P && Q) Γ
      -> Proves ((P::Q::(rem (P && Q) Γ)), R)
      -> Proves (Γ, R)
| P_DisjElim :
    forall Γ P Q R,
      In (P || Q) Γ
      -> Proves ((P::(rem (P || Q) Γ)), R)
      -> Proves ((Q::(rem (P || Q) Γ)), R)
      -> Proves (Γ, R)
| P_MP :
     forall Γ P Q R,
       In (P --> Q) Γ
       -> Proves ((rem (P --> Q) Γ), P)
       -> Proves ((P::Q::(rem (P --> Q) Γ)), R)
       -> Proves (Γ, R)
| P_Conj :
    forall P Q Γ,
      Proves (Γ, P)
      -> Proves (Γ, Q)
      -> Proves (Γ, (P && Q))
| P_Add_lhs :
    forall P Q Γ,
      Proves (Γ, P)
      -> Proves (Γ, (P || Q))
| P_Add_rhs :
    forall Γ P Q,
      Proves (Γ, Q)
      -> Proves (Γ, (P || Q))
 | P_CP :
     forall Γ P Q,
       Proves ((P::Γ), Q)
       -> Proves (Γ, (P --> Q))

(** SubType *)
with SubType : (type * type) -> Prop :=
| S_Refl : 
    forall τ, SubType (τ, τ)
| S_Top : 
    forall τ, SubType (τ, tTop)
| S_Bot : 
    forall τ, SubType (tBot, τ)
| S_UnionSuper_lhs :
    forall τ σ1 σ2,
      SubType (τ, σ1)
      -> SubType (τ, (tU σ1 σ2))
| S_UnionSuper_rhs :
    forall τ σ1 σ2,
      SubType (τ, σ2)
      -> SubType (τ, (tU σ1 σ2))
| S_UnionSub :
    forall τ1 τ2 σ,
      SubType (τ1, σ)
      -> SubType (τ2, σ)
      -> SubType ((tU τ1 τ2), σ)
| S_Abs :
    forall x y τ τ' σ σ' ψ ψ' o o',
      SubType ((subst_t τ (Some (var y)) x), τ')
      -> SubType (σ', (subst_t σ (Some (var y)) x))
      -> Proves ([(subst_p ψ (Some (var y)) x)], ψ')
      -> SubObj (subst_o o (Some (var y)) x) o'
      -> SubType ((tλ x σ τ ψ o),
                 (tλ y σ' τ' ψ' o'))
| S_Cons :
    forall τ1 σ1 τ2 σ2,
      SubType (τ1, τ2)
      -> SubType (σ1, σ2)
      -> SubType ((tCons τ1 σ1), (tCons τ2 σ2)).

Fixpoint prop_weight (p:prop) : nat :=
  match p with
    | Atom f => 1
    | And P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Or P Q => 1 + (prop_weight P) + (prop_weight Q)
    | Imp P Q => 1 + (prop_weight P) + (prop_weight Q)
    | FF => 1
    | Unk => 1
  end.

Fixpoint env_weight (l:list prop) : nat :=
  match l with
    | nil => 0
    | p :: ps => (prop_weight p) + (env_weight ps)
  end.

Definition proof_weight (p:(list prop) * prop) : nat :=
plus (env_weight (fst p)) (prop_weight (snd p)).

Lemma find_witness:
  forall(A:Type) (P:A->Prop) (L:list A),
    (forall a, {P a}+{~P a}) ->
    { a | In a L /\ P a } + { forall a, In a L -> ~P a }.
Proof.
intros A P L P_dec.
induction L; auto. 
destruct IHL as [(b,(HbA,HbB))|IHL].
- left.
  exists b. crush.
- destruct (P_dec a) as [Ha|Ha].
  + left.
    exists a. crush.
  + right.
    intros b [Hb|Hb].
    * rewrite <-Hb. crush.
    * crush. iauto. 
Qed.


Lemma find_In_witness:
  forall(A:Type) (P:A->Prop) (L:list A),
    (forall a, In a L -> {P a}+{~P a}) ->
    { a | In a L /\ P a } + { forall a, In a L -> ~P a }.
Proof.
intros A P L P_dec.
induction L; auto.
destruct IHL as [(b,(HbA,HbB))|IHL].
- crush. 
- left.
  exists b. crush.
- destruct (P_dec a) as [Ha|Ha].
  + crush.
  + left.
    exists a. crush.
  + right.
    intros b [Hb|Hb].
    * rewrite <-Hb. crush.
    * apply IHL. crush.
Qed.

Inductive Verifier : relation prop :=
| V_subtype : 
    forall o t t',
      SubType (t, t') ->
      Verifier (Atom (istype o t')) (Atom (istype o t)).

Lemma Verifier_dec : forall P2 P1,
(forall (t1 t2 : type),  {SubType (t1, t2)} + {~SubType (t1, t2)})
-> {Verifier P1 P2} + {~Verifier P1 P2}.
Proof.
  intros P1 P2 ST_dec.
  destruct P1; try (solve [right; intros contra; inversion contra; crush]).
  destruct f as [o t]. destruct P2; try (solve [right; intros contra; inversion contra; crush]).
  destruct f as [o' t']. destruct (obj_eqdec o o').
  subst. destruct (ST_dec t t') as [Hsub|HNsub].
  left; apply V_subtype; crush.
  right; intros contra; inversion contra; crush.
  right; intros contra; inversion contra; crush.
Qed.

Lemma prop_in_get:
  forall(P1:prop) (L1:list prop), In P1 L1 -> { L2 | Permutation L1 (P1::L2) }.
Proof.
intros P1 L1.
induction L1. crush. 
destruct (prop_eqdec P1 a) as [HP1e|HP1n].
- intros _.
  exists L1. crush.
- intros H.
  destruct IHL1 as (L2,HL2). crush.
  exists (a::L2). rewrite perm_swap.
  rewrite <-HL2. auto.
Qed.

Lemma rem_hd : forall P L,
rem P (P::L) = L.
Proof.
  intros.
  induction L.
  simpl. destruct (prop_eqdec P P); crush.
  unfold remove in IHL. 
  simpl. destruct (prop_eqdec P P). auto. tryfalse.
Qed.  

Lemma rem_And_weight : forall P P1 P2 L,
In (P1 && P2) L
-> proof_weight ((P1::P2::(rem (P1 && P2) L)), P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (P1 && P2) (P1 && P2)).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (P1 && P2) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.  

Lemma rem_Or_lhs_weight : forall P P1 P2 L,
In (P1 || P2) L
-> proof_weight ((P1::(rem (P1 || P2) L)), P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (P1 || P2) (P1 || P2)).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (P1 || P2) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.  

Lemma rem_Or_rhs_weight : forall P P1 P2 L,
In (P1 || P2) L
-> proof_weight ((P2::(rem (P1 || P2) L)), P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (P1 || P2) (P1 || P2)).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (P1 || P2) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.  

Lemma rem_Imp_weight_lhs : forall P P1 P2 L,
In (P1 --> P2) L 
-> proof_weight (rem (P1 --> P2) L, P1) < proof_weight (L,P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (P1 --> P2) (P1 --> P2)).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (P1 --> P2) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.

Lemma rem_Imp_weight_rhs : forall P P1 P2 L,
In (P1 --> P2) L 
-> proof_weight (P1 :: P2 :: rem (P1 --> P2) L, P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (P1 --> P2) (P1 --> P2)).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (P1 --> P2) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.

Lemma split_And_weight_lhs : forall L P1 P2,
proof_weight (L, P1) < proof_weight (L, P1 && P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Qed.

Lemma split_And_weight_rhs : forall L P1 P2,
proof_weight (L, P2) < proof_weight (L, P1 && P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Qed.

Lemma split_Or_weight_lhs : forall L P1 P2,
proof_weight (L, P1) < proof_weight (L, P1 || P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Qed.

Lemma split_Or_weight_rhs : forall L P1 P2,
proof_weight (L, P2) < proof_weight (L, P1 || P2).
Proof.
  intros.
  unfold proof_weight.
  crush.
Qed.
Hint Resolve split_And_weight_lhs split_And_weight_rhs 
             split_Or_weight_lhs split_Or_weight_rhs.
     

Hint Constructors Verifier.

Lemma Proves_dec : forall (Γ:list prop) (P: prop), {Proves (Γ, P)} + {~Proves (Γ, P)}
with SubType_dec : forall (t1 t2 : type),  {SubType (t1, t2)} + {~SubType (t1, t2)}.
Proof.
  (* Proves_dec *)
  clear Proves_dec.
  intros Γ' P'.
  induction (Γ',P') as ((Γ, P),IH) using
    (well_founded_induction
      (well_founded_ltof _ proof_weight)).
  clear Γ' P'.
  destruct (find_witness _ (fun P' => Verifier P' P) Γ (fun P' => (Verifier_dec P P' SubType_dec)))
  as [[ver [ver_In Is_Ver]] | No_Ver].
  (* Verifier! *)
  left. destruct Is_Ver. apply (P_SubType t'); auto.
  (* No Verifier =( *)
  destruct (
    find_In_witness _ (fun a =>
      match a with
      | FF => True
      | P1 && P2 => Proves ((P1::P2::(rem (P1 && P2) Γ)), P)
      | P1 || P2 => Proves ((P1::(rem (P1 || P2) Γ)), P) 
                    /\ Proves ((P2::(rem (P1 || P2) Γ)), P)
      | P1 --> P2 =>  (Proves ((rem (P1 --> P2) Γ), P1))
                      /\ (Proves ((P1::P2::(rem (P1 --> P2) Γ)), P))
      | _ => False
      end
    ) Γ) as [(a,(HaA,HaB))|antecedent_nonexist].
- intros a HIn.
  destruct a as [f|P1 P2|P1 P2|P1 P2| |]; try (solve[auto]).
+ apply IH. apply (rem_And_weight P) in HIn. crush.
+ assert ({Proves ((P1 :: rem (P1 || P2) Γ), P)} + 
          {~(Proves ((P1 :: rem (P1 || P2) Γ), P))}) as Hlhs.
* apply IH. apply (rem_Or_lhs_weight P) in HIn. crush.
* assert ({Proves ((P2 :: rem (P1 || P2) Γ), P)} + 
          {~(Proves ((P2 :: rem (P1 || P2) Γ), P))}) as Hrhs.
  apply IH. apply (rem_Or_rhs_weight P) in HIn. crush.
  crush.
+ assert ({Proves (rem (P1 --> P2) Γ, P1)} +
   {~ (Proves (rem (P1 --> P2) Γ, P1))}) as Hlhs.
  apply IH. apply (rem_Imp_weight_lhs P) in HIn. crush.
  assert ({Proves (P1 :: P2 :: rem (P1 --> P2) Γ, P)} +
   {~ Proves (P1 :: P2 :: rem (P1 --> P2) Γ, P)}) as Hrhs.
  apply IH. apply (rem_Imp_weight_rhs P) in HIn. crush.
  crush.
- left. destruct a as [f|P1 P2|P1 P2|P1 P2| |]; crush.
  apply (P_Simpl _ P1 P2); crush.
  apply (P_DisjElim _ P1 P2); crush.
  apply (P_MP _ P1 P2); crush.
  apply P_False; auto.
- assert (succedent_dec:
  {
    match P with
    | PA && PB  => Proves (Γ, PA) /\ Proves (Γ, PB)
    | PA || PB  => Proves (Γ, PA) \/ Proves (Γ, PB)
    | PA --> PB => Proves (PA::Γ, PB)
    | _ => False
    end
  } + {~
    match P with
    | PA && PB => Proves (Γ, PA) /\ Proves (Γ, PB)
    | PA || PB => Proves (Γ, PA) \/ Proves (Γ, PB)
    | PA --> PB => Proves (PA::Γ, PB)
    | _ => False
    end
  }).
  destruct P as [f|P1 P2|P1 P2|P1 P2| |]; try (solve[auto]).
+ assert ({Proves (Γ, P1)} + {~ (Proves (Γ, P1))}) as Hlhs.
    apply IH. unfold ltof. auto. 
  assert ({Proves (Γ, P2)} + {~ (Proves (Γ, P2))}) as Hrhs.
    apply IH. unfold ltof. auto. 
  crush.
+ assert ({Proves (Γ, P1)} + {~ (Proves (Γ, P1))}) as Hlhs.
    apply IH. unfold ltof. auto. 
  assert ({Proves (Γ, P2)} + {~ (Proves (Γ, P2))}) as Hrhs.
    apply IH. unfold ltof. auto. 
  crush.
+ assert ({Proves (P1::Γ, P2)} + {~ (Proves (P1::Γ, P2))}) as Himpl.
    apply IH. unfold ltof. unfold proof_weight. crush. 
  crush.
+ destruct succedent_dec as [succedent_exist|succedent_nonexist].
  left.
  destruct P as [f|P1 P2|P1 P2|P1 P2| |]; try (solve[crush]).
  apply P_Conj; crush.
  destruct succedent_exist as [Hlhs | Hrhs].
  apply P_Add_lhs; auto.
  apply P_Add_rhs; auto.
  apply P_CP; auto.
  destruct (In_dec prop_eqdec FF Γ).
  left; apply P_False; auto.
  right; intros contra; inversion contra; subst; try (solve[crush]).
  apply (No_Ver _ H2). auto. 
  apply (antecedent_nonexist (P0 && Q) H1). auto.
  apply (antecedent_nonexist (P0 || Q) H1). auto.
  apply (antecedent_nonexist (P0 --> Q) H1). auto.




Hint Resolve S_Refl S_Bot S_Top S_UnionSub.


Lemma U_super : forall t t1 t2,
is_tU t = None
-> (forall y : type * type,
          type_weight (fst y) + type_weight (snd y) <
          type_weight (fst (t, tU t1 t2)) +
          type_weight (snd (t, tU t1 t2)) ->
          {SubType y} + {~ SubType y})
-> {SubType (t, tU t1 t2)} + {~ SubType (t, tU t1 t2)}.
Proof.
  intros t t1 t2 HnoU IHSub.
  assert ({SubType (t, t1)} + {~ SubType (t, t1)}) as Hlhs.
    apply IHSub. crush. 
  assert ({SubType (t, t2)} + {~ SubType (t, t2)}) as Hrhs.
    apply IHSub. crush.
  destruct Hlhs. left. apply S_UnionSuper_lhs; auto.
  destruct Hrhs. left. apply S_UnionSuper_rhs; auto.
  right; intros contra; inversion contra; crush.
Qed.

Lemma U_sub : forall t t1 t2,
is_tU t = None
-> (forall y : type * type,
          type_weight (fst y) + type_weight (snd y) <
          type_weight (fst (tU t1 t2, t)) +
          type_weight (snd (tU t1 t2, t)) ->
          {SubType y} + {~ SubType y})
-> {SubType (tU t1 t2, t)} + {~ SubType (tU t1 t2, t)}.
Proof.
  intros t t1 t2 HnoU IHSub.
  assert ({SubType (t1, t)} + {~ SubType (t1, t)}) as Hlhs.
    apply IHSub. crush. 
  assert ({SubType (t2, t)} + {~ SubType (t2, t)}) as Hrhs.
    apply IHSub. crush.
  destruct Hlhs. destruct Hrhs. left. apply S_UnionSub; auto.
  right; intros contra; inversion contra; crush.
  right; intros contra; inversion contra; crush.
Qed.


  (* SubType *)
- clear SubType_dec. 
  intros t t'. 
  induction (t,t') as ((t1, t2),IHSub) using
    (well_founded_induction
      (well_founded_ltof _ (fun tp => ((type_weight (fst tp)) 
                                       + (type_weight (snd tp)))))).
  clear t t'. unfold ltof in IHSub.
  destruct t1; destruct t2; 
    try (solve[right; intros contra; inversion contra; crush |
               left; crush |
               apply U_super; crush |
               apply U_sub; crush]).
  assert ({SubType (tU t1_1 t1_2, t2_1)} 
          + {~ SubType (tU t1_1 t1_2, t2_1)}) as Hrlhs.
    apply IHSub. crush. 
  assert ({SubType (tU t1_1 t1_2, t2_2)} 
          + {~ SubType (tU t1_1 t1_2, t2_2)}) as Hrrhs.
    apply IHSub. crush.
  assert ({SubType (t1_1, tU t2_1 t2_2)} 
          + {~ SubType (t1_1, tU t2_1 t2_2)}) as Hllhs.
    apply IHSub. crush. 
  assert ({SubType (t1_2, tU t2_1 t2_2)} 
          + {~ SubType (t1_2, tU t2_1 t2_2)}) as Hlrhs.
    apply IHSub. crush.
  destruct (type_eqdec (tU t1_1 t1_2) (tU t2_1 t2_2)) as [Heq | Hneq].
  rewrite Heq. left; apply S_Refl.
  destruct Hrlhs. left. apply S_UnionSuper_lhs; auto. 
  destruct Hrrhs. left. apply S_UnionSuper_rhs; auto.
  destruct Hllhs. destruct Hlrhs. left. apply S_UnionSub; auto.
  right; intros contra; inversion contra; try (solve[crush]).
  right; intros contra; inversion contra; try (solve[crush]).
  assert ({SubType (t1_1, t2_1)} 
          + {~ SubType (t1_1, t2_1)}) as Hlhs.
    apply IHSub. crush. 
  assert ({SubType (t1_2, t2_2)} 
          + {~ SubType (t1_2, t2_2)}) as Hrhs.
    apply IHSub. crush.
  destruct Hlhs; destruct Hrhs; 
    try(solve [left; apply S_Cons; auto |
               right; intros contra; inversion contra; crush]).

Lemma subst_t_weight : forall t x y,
type_weight (subst_t t (Some (var y)) x) = type_weight t.
Proof.
  induction t; crush.
  unfold subst_t. simpl.
  destruct (id_eqdec x i). subst.
  simpl. crush.
  crush.
Qed.  
    assert ({SubType ((subst_t t1_2 (Some (var i0)) i), t2_2)} 
          + {~ SubType ((subst_t t1_2 (Some (var i0)) i), t2_2)}) as Hrhs.
    apply IHSub. simpl. rewrite (subst_t_weight t1_2 i i0). crush.
    assert ({SubType (t2_1, (subst_t t1_1 (Some (var i0)) i))} 
          + {~ SubType (t2_1, (subst_t t1_1 (Some (var i0)) i))}) as Hlhs.
      apply IHSub. simpl. rewrite (subst_t_weight t1_1 i i0). crush.
    assert ({Proves ([(subst_p p (Some (var i0)) i)], p0)} 
            + {~Proves ([(subst_p p (Some (var i0)) i)], p0)}) as HP.
      apply Proves_dec.
    assert ({(SubObj (subst_o o (Some (var i0)) i) o0)} 
            + {~(SubObj (subst_o o (Some (var i0)) i) o0)})  as HO.
      apply SO_dec.
  destruct (type_eqdec (tλ i t1_1 t1_2 p o) (tλ i0 t2_1 t2_2 p0 o0)) as [Heq | Hneq].
  rewrite Heq. left; apply S_Refl.
  destruct Hlhs; destruct Hrhs; destruct HP; destruct HO;
    try(solve[right; intros contra; inversion contra; crush |
              left; apply S_Abs; crush]).
Qed.


(** ** TypeOf *)

Inductive TypeOf : prop -> exp -> type -> prop -> opt object -> Prop :=
| T_Nat :
    forall Γ n,
      TypeOf Γ (#n) tNat TT None
| T_Str :
    forall Γ s,
      TypeOf Γ (Str s) tStr TT None
| T_Const :
    forall τ Γ c x,
      τ = (const_type c x)
      -> TypeOf Γ (eOp (c_op c)) τ TT None
| T_True :
    forall Γ,
      TypeOf Γ #t tT TT None
| T_False :
    forall Γ,
      TypeOf Γ #f tF FF None
| T_Var :
    forall τ Γ x,
      Proves Γ ((var x) ::= τ)
      -> TypeOf Γ ($ x) τ ((var x) ::~ tF) (Some (var x))
| T_Abs :
    forall σ τ o Γ x ψ e,
      TypeOf (Γ && ((var x) ::= σ)) e τ ψ o
      -> TypeOf Γ 
                (eλ x σ e) 
                (tλ x σ τ ψ o) 
                TT 
                None
| T_App :
    forall τ'' σ τ o'' o o' Γ e x fψ fo ψ e' ψ' ψf'',
      (subst_t τ o' x) = τ''
      -> (subst_p fψ o' x) = ψf''
      -> (subst_o fo o' x) = o''
      -> TypeOf Γ e (tλ x σ τ fψ fo) ψ o
      -> TypeOf Γ e' σ ψ' o'
      -> TypeOf Γ (Apply e e') τ'' ψf'' o''
| T_If :
    forall τ τ' o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ' ψ1 o1
      -> TypeOf (Γ && ψ1) e2 τ ψ2 o
      -> TypeOf (Γ && (Not ψ1)) e3 τ ψ3 o
      -> TypeOf Γ (If e1 e2 e3) τ ((ψ1 && ψ2) || ((Not ψ1) && ψ3)) o
| T_Cons :
    forall τ1 τ2 o1 o2 Γ e1 ψ1 e2 ψ2,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf Γ e2 τ2 ψ2 o2
      -> TypeOf Γ (Cons e1 e2) (tCons τ1 τ2) TT None
| T_Car :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [car] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [car] x)) o x) = o'
      -> TypeOf Γ e (tCons τ1 τ2) ψ0 o
      -> TypeOf Γ (Car e) τ1 ψ o'
| T_Cdr :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [cdr] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [cdr] x)) o x) = o'
      -> TypeOf Γ e (tCons τ1 τ2) ψ0 o
      -> TypeOf Γ (Cdr e) τ2 ψ o'
| T_Let :
    forall σ' τ σ o1' o0 o1 Γ e0 ψ0 e1 ψ1 x ψ1',
      (subst_t σ o0 x) = σ'
      -> (subst_p ψ1 o0 x) = ψ1'
      -> (subst_o o1 o0 x) = o1'
      -> TypeOf Γ e0 τ ψ0 o0
      -> TypeOf (Γ && ((var x) ::= τ)
                   && (((var x) ::~ tF) --> ψ0)
                   && (((var x) ::= tF) --> (Not ψ0))) 
                e1
                σ
                ψ1
                o1
      -> TypeOf Γ (Let x e0 e1) σ' ψ1' o1'
| T_Subsume :
    forall τ' τ o' o Γ e ψ ψ',
      TypeOf Γ e τ ψ o
      -> Proves (Γ && ψ) ψ'
      -> SubType τ τ'
      -> SubObj o o'
      -> TypeOf Γ e τ' ψ' o'.


(** * Proof Helpers *)

(** * Proof Helpers/Lemmas and Automation *)
Hint Resolve P_DisjElim P_Conjr.

(** Universally valid tactics (if these go wrong, we're already in a bad
    proof state is the idea) *)
Hint Extern 6 (Proves FF ?P) => apply P_False.
Hint Extern 6 (Proves ?P TT) => apply P_True.
Hint Extern 6 (Proves (?P (Not ?P)) ?Q) => apply P_Contra.
Hint Extern 6 (Proves ((Not ?P) && (?P || ?Q)) ?Q) => apply P_DisjSyl.
Hint Extern 6 (SubType ?P ?P) => apply S_Refl.
Hint Extern 6 (SubType ?P tTop) => apply S_Top.
Hint Extern 6 (SubType ?P tBot) => apply S_Bot.
Hint Extern 6 (SubType ?P (tU ?P ?Q)) => apply S_UnionSuper_lhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU ?Q ?R)) => apply S_UnionSuper_rhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU (tU ?P ?Q) ?R)) => 
  apply S_UnionSuper_lhs; apply S_UnionSuper_lhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU (tU ?Q ?P) ?R)) => 
  apply S_UnionSuper_lhs; apply S_UnionSuper_rhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU ?R (tU ?P ?Q))) => 
  apply S_UnionSuper_rhs; apply S_UnionSuper_lhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU ?R (tU ?Q ?P))) => 
  apply S_UnionSuper_rhs; apply S_UnionSuper_rhs; apply S_Refl.
Hint Extern 6 (SubType ?P (tU ?Q ?R)) => apply S_UnionSuper_rhs; apply S_Refl.
Hint Extern 6 (SubType ?P tBot) => apply S_Bot.
Hint Extern 6 (SubObj ?o ?o) => apply SO_Refl.
Hint Extern 6 (SubObj ?o None) => apply SO_Top.
Hint Extern 6 (SubObj None ?o) => eapply SO_Refl.


Axiom prop_equality : forall P Q,
Proves P Q
-> Proves Q P
-> P = Q.

Lemma P_Refl : forall P,
Proves P P.
Proof.
  intros P.
  apply P_Atom; crush.
Qed.
Hint Resolve P_Refl.

Hint Extern 6 (Proves (?P && ?Q) (?P || ?R)) => 
apply P_Conjl_lhs; apply P_Add_lhs; apply P_Refl.
Hint Extern 6 (Proves (?P && ?Q) (?R || ?P)) => 
apply P_Conjl_lhs; apply P_Add_rhs; apply P_Refl.
Hint Extern 6 (Proves (?Q && ?P) (?P || ?R)) => 
apply P_Conjl_rhs; apply P_Add_lhs; apply P_Refl.
Hint Extern 6 (Proves (?Q && ?P) (?R || ?P)) => 
apply P_Conjl_rhs; apply P_Add_rhs; apply P_Refl.


Lemma P_Conjl_lhs_Refl : forall P Q,
Proves (P && Q) P.
Proof with crush.
  intros. apply P_Conjl_lhs...
Qed.
Hint Resolve P_Conjl_lhs_Refl.

Lemma P_Conjl_rhs_Refl : forall P Q,
Proves (P && Q) Q.
Proof with crush.
  intros. apply P_Conjl_rhs...
Qed.
Hint Resolve P_Conjl_rhs_Refl.

Lemma P_Simpl_lhs : forall P Q R,
Proves P (Q && R)
-> Proves P Q.
Proof with crush.
  intros. apply (P_HypSyl P (Q && R) Q)...
Qed.

Lemma P_Simpl_rhs : forall P Q R,
Proves P (Q && R)
-> Proves P R.
Proof with crush.
  intros. apply (P_HypSyl P (Q && R) R)...
Qed.

Lemma P_Add_lhs_Refl : forall P Q,
Proves P (P || Q).
Proof with crush.
  intros; apply P_Add_lhs...
Qed.
Hint Resolve P_Add_lhs_Refl.

Lemma P_Add_rhs_Refl : forall P Q,
Proves P (Q || P).
Proof with crush.
  intros; apply P_Add_rhs...
Qed.
Hint Resolve P_Add_rhs_Refl.

Hint Extern 11 (Proves ?P (?Q || ?R)) =>
match goal with
| [ H : Proves P Q |- Proves P (Q || R)] =>
  apply P_Add_lhs; exact H
| [ H : Proves P R |- Proves P (Q || R)] =>
  apply P_Add_rhs; exact H
end.

Lemma then_else_eq : forall (T:Type) (P1 P2:Prop) (test: sumbool P1 P2) (Q:T),
(if test then Q else Q) = Q.
Proof.
  crush.
Qed.
Hint Rewrite then_else_eq.

Lemma if_eq_id : forall (T:Type) x (t1 t2: T),
(if id_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (id_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_id.

Lemma if_eq_obj : forall (T:Type) x (t1 t2: T),
(if obj_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (obj_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_obj.

Lemma neq_id_neq : forall (T:Type) x y (P Q:T),
x <> y ->
((if (id_eqdec x y) then P else Q) = Q).
Proof.
  intros.
  destruct (id_eqdec x y); crush.
Qed.

Lemma neq_obj_neq : forall (T:Type) x y (P Q:T) pth1 pth2,
x <> y ->
((if (obj_eqdec (obj pth1 x) (obj pth2 y)) then P else Q) = Q).
Proof.
  intros.
  destruct (obj_eqdec (obj pth1 x) (obj pth2 y)); crush.
Qed.

Lemma if_eq_type : forall (T:Type) x (t1 t2: T),
(if type_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (type_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_type.

Lemma if_eq_prop : forall (T:Type) x (t1 t2: T),
(if prop_eqdec x x then t1 else t2) = t1.
Proof.
  intros T x t1 t2.
  destruct (prop_eqdec x x); auto. tryfalse.
Qed.
Hint Rewrite if_eq_prop.

Fixpoint in_disj (P Q: prop) : bool :=
  match Q with
    | p || q => if (prop_eqdec P p) then true
                else if (prop_eqdec P q) then true
                     else if (in_disj P p) then true
                          else if (in_disj P q) then true
                               else false
    | _ => false
  end.


(** Proves goals "Proves P Q" where Q is a tree of disjunctions of
arbitrary depth such that P is somewhere in the tree. *)
Lemma P_in_disj : forall Q P,
in_disj P Q = true
-> Proves P Q.
Proof with crush.
  intros Q; induction Q...
  specialize (IHQ1 P). specialize (IHQ2 P).
  destruct (prop_eqdec P Q1)...
  destruct (prop_eqdec P Q2)...
  destruct (in_disj P Q2)...
  destruct (in_disj P Q1)...
Qed.

Ltac indisj := 
  progress (match goal with
              | [ |- Proves ?P (?Q || ?R)] =>
                solve[apply P_in_disj; crush]
              | _ => idtac
            end).
Hint Extern 5 (Proves ?P (?P || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || ?P)) => indisj.
Hint Extern 5 (Proves ?P (?P || _ || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || ?P || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || (?P || _))) => indisj.
Hint Extern 5 (Proves ?P (_ || _ || ?P)) => indisj.
Hint Extern 5 (Proves ?P (_ || (_ || ?P))) => indisj.
Hint Extern 5 (Proves ?P (?P || (_ || _))) => indisj.
Hint Extern 5 (Proves ?P (_ || (?P || _))) => indisj.
Hint Extern 5 (Proves ?P (_ || (_ || ?P))) => indisj.
Hint Extern 5 (Proves ?P (?P || _ || _ || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || ?P || _ || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || _ || ?P || _)) => indisj.
Hint Extern 5 (Proves ?P (_ || _ || _ || ?P)) => indisj.

Lemma Or_comm_imp : forall P Q R,
Proves P (Q || R)
-> Proves P (R || Q).
Proof with crush.
  intros P Q R H. apply (P_HypSyl _ _ _ H)...
Qed.

Lemma Or_comm : forall P Q,
(P || Q) = (Q || P).
Proof with crush.
  intros.
  apply prop_equality; (apply Or_comm_imp; crush).
Qed.

Lemma Or_assoc : forall P Q R,
(P || (Q || R)) = ((P || Q) || R).
Proof with crush.
  intros.
  apply prop_equality. 
  eapply P_DisjElim... 
  apply P_DisjElim. apply P_DisjElim. apply P_Add_lhs...
  apply P_Add_rhs...
  apply P_Add_rhs...
Qed.
  

Hint Extern 3 (Proves ?P (?R || ?Q)) =>
match goal with
  | [ H : Proves P (Q || R) |- Proves P (R || Q)] =>
    apply Or_comm; auto
end.

Lemma And_comm_imp : forall P Q R,
Proves P (Q && R)
-> Proves P (R && Q).
Proof with crush.
  intros P Q R H.
  apply P_Conjr.
  apply P_Simpl_rhs in H...
  apply P_Simpl_lhs in H...
Qed.

Lemma And_comm : forall P Q,
P && Q = Q && P.
Proof with crush.
  intros; apply prop_equality...
Qed.  

Lemma And_assoc : forall P Q R,
(P && (Q && R)) = ((P && Q) && R).
Proof with crush.
  intros P Q R.
  apply prop_equality.
  repeat apply P_Conjr... apply P_Conjl_rhs...
  apply P_Conjl_rhs... 
  repeat apply P_Conjr... apply P_Conjl_lhs...
  apply P_Conjl_lhs...
Qed.

Lemma And_FF : forall P,
P && FF = FF.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite And_FF.

Lemma FF_And : forall P,
FF && P = FF.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite FF_And.

Lemma And_TT : forall P,
P && TT = P.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite And_TT.

Lemma TT_And : forall P,
TT && P = P.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite TT_And.

Lemma Or_FF : forall P,
P || FF = P.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite Or_FF.

Lemma FF_Or : forall P,
FF || P = P.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite FF_Or.


Lemma Or_TT : forall P,
P || TT = TT.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite Or_TT.

Lemma TT_Or : forall P,
TT || P = TT.
Proof with crush.
  intros. apply prop_equality...
Qed.
Hint Rewrite TT_Or.

Lemma P_DisjSyl_rhs : forall P R Q,
Proves P (Not Q)
-> Proves P (Q || R)
-> Proves P R.
Proof with crush.
  intros P R Q HnotQ HQorR.
  apply (P_HypSyl P ((Not Q) && (Q || R)))...
Qed.

Lemma P_DisjSyl_lhs : forall P Q R,
Proves P (Not R)
-> Proves P (Q || R)
-> Proves P Q.
Proof with crush.
  intros P Q R HnotR HQorR.
  rewrite Or_comm in HQorR.
  apply P_DisjSyl_rhs in HQorR...
Qed.

Lemma And_over_Or : forall P Q R,
P && (Q || R) = (P && Q) || (P && R).
Proof with crush.
  intros.
  apply prop_equality.
  eapply P_ConstrDilemma...
  eapply P_DisjElim... 
Qed.

Lemma Or_over_And : forall P Q R,
P || (Q && R) = (P || Q) && (P || R).
Proof with crush.
  intros.
  apply prop_equality.
  eapply P_DisjElim...
  rewrite And_over_Or.
  apply P_DisjElim...
  rewrite And_comm.
  rewrite And_over_Or.
  eapply P_DisjElim...
  rewrite And_comm...
Qed.

Fixpoint in_type (t U : type) : bool :=
if type_eqdec t U then true else
match U with
  | tU t1 t2 => orb (in_type t t1) (in_type t t2)
  | _ => false
end.

Lemma in_type_SubType : forall t2 t1,
in_type t1 t2 = true
-> SubType t1 t2.
Proof.
  Hint Rewrite orb_true_iff.
  Hint Rewrite andb_true_iff.
  intros t2.
  induction t2; intros; crush.
  destruct (type_eqdec t1 tBot); crush.
  destruct (type_eqdec t1 tNat); crush.
  destruct (type_eqdec t1 tStr); crush.
  destruct (type_eqdec t1 tT); crush.
  destruct (type_eqdec t1 tF); crush.
  destruct (type_eqdec t1 (tU t2_1 t2_2)); crush.
  eapply S_UnionSuper_lhs; crush.
  eapply S_UnionSuper_rhs; crush.
  destruct (type_eqdec t1 (tCons t2_1 t2_2)); crush.
  destruct (type_eqdec t1 (tλ i t2_1 t2_2 p o)); crush.
Qed.

  
Fixpoint bound_in (o:object) (p:prop) : bool :=
  match p with
    | Is o' t =>
      if obj_eqdec o o' then true else false
    | IsNot _ _ => false
    | And lhs rhs => orb (bound_in o lhs) (bound_in o rhs)
    | Or lhs rhs => andb (bound_in o lhs) (bound_in o rhs)
    | FF => true
    | _ => false
  end.

Lemma bound_in_Proves_Top : forall P o',
bound_in o' P = true
-> Proves P (o' ::= tTop).
Proof with crush.
  intros p; induction p...
  destruct (obj_eqdec o' o). eapply P_Sub... crush.
  eapply P_Conjl_lhs... 
  eapply P_Conjl_rhs...
Qed.

Lemma In_disjsyl_lhs : forall o t t' P,
In (o ::~ t') P
-> In (o ::= (tU t t')) P
-> Proves P (o ::= t).
Proof with crush.
  intros o t t' P H1 H2.
  apply P_Atom in H1. apply P_Atom in H2.
  eapply (P_UnionNeg_lhs P o t t'); auto.
Qed.

Lemma In_disjsyl_rhs : forall o t t' P,
In (o ::~ t') P
-> In (o ::= (tU t' t)) P
-> Proves P (o ::= t).
Proof with crush.
  intros o t t' P H1 H2.
  apply P_Atom in H1. apply P_Atom in H2.
  eapply (P_UnionNeg_rhs P o t t'); auto.
Qed. 

Fixpoint find_types P o : list type := 
  match P with
    | (o' ::= t) => if obj_eqdec o o' then [t] else nil
    | (P1 && P2) =>  
      (find_types P1 o) ++ (find_types P2 o)
      | _ => nil
  end.
Hint Unfold find_types.

Fixpoint find_disj_neighbor (P p : prop) : list prop :=
  match P with
    | Q || R =>
      if (prop_eqdec Q p) then [P]
      else if (prop_eqdec R p) then [P]
      else nil
    | Q && R =>
      (find_disj_neighbor Q p) ++ (find_disj_neighbor R p)
    | _ => nil
  end.

Ltac unionnegtac o types :=
  match types with
    | (tU ?t1 ?t2) :: ?ts =>
      (solve [first [(eapply (In_disjsyl_lhs o t1 t2); crush)    |
                     ((eapply (In_disjsyl_rhs o t2 t1)); crush)] | 
                    (unionnegtac o ts)
      ])
    | _ :: ?ts => (unionnegtac o ts)
    | nil => fail
  end.

Ltac disjsyltac P Q disjs solver :=
  match disjs with
    | (Q || ?R) :: ?ds =>
      first [(solve [apply (P_DisjSyl_lhs P Q R); solver]) |
             (disjsyltac P Q ds)]
    | (?R || Q) :: ?ds =>
      first [(solve [apply (P_DisjSyl_rhs P Q R); solver]) |
            (disjsyltac P Q ds)]
    | _ => fail
  end.

Lemma nat_subst : forall t o1 o2,
t = tNat
-> subst_t t o1 o2 = tNat.
Proof. crush. Qed.

Lemma top_subst : forall t o1 o2,
t = tTop
-> subst_t t o1 o2 = tTop.
Proof. crush. Qed.

Lemma bot_subst : forall t o1 o2,
t = tBot
-> subst_t t o1 o2 = tBot.
Proof. crush. Qed.

Lemma str_subst : forall t o1 o2,
t = tStr
-> subst_t t o1 o2 = tStr.
Proof. crush. Qed.

Lemma true_subst : forall t o1 o2,
t = tT
-> subst_t t o1 o2 = tT.
Proof. crush. Qed.

Lemma false_subst : forall t o1 o2,
t = tF
-> subst_t t o1 o2 = tF.
Proof. crush. Qed.

Lemma bool_subst : forall t o1 o2,
t = tBool
-> subst_t t o1 o2 = tBool.
Proof. crush. Qed.

Lemma TT_subst : forall P o1 o2,
P = TT
-> subst_p P o1 o2 = TT.
Proof. crush. Qed.

Lemma FF_subst : forall P o1 o2,
P = FF
-> subst_p P o1 o2 = FF.
Proof. crush. Qed.

Lemma Unk_subst : forall P o1 o2,
P = Unk
-> subst_p P o1 o2 = Unk.
Proof. crush. Qed.

Lemma None_subst : forall o o1 o2,
o = None
-> subst_o o o1 o2 = None.
Proof. crush. Qed.

Fixpoint simple_subtype (tsub tsuper: type)  : bool :=
if (type_eqdec tsub tsuper) then true else
match tsub, tsuper with
| _ , tTop    => true
| _, tU t1 t2 => 
  orb (simple_subtype tsub t1)
      (simple_subtype tsub t2)
| tCons t1 t2, tCons t3 t4 =>
  andb (simple_subtype t1 t3)
       (simple_subtype t2 t4)
| _, _ => false
end.

Lemma simple_subtype_valid : forall t2 t1,
simple_subtype t1 t2 = true
-> SubType t1 t2.
Proof with (crush; first[solve [apply S_UnionSuper_lhs; crush] | 
                         solve [apply S_UnionSuper_rhs; crush] |
                         auto]).
  intros t2; induction t2; destruct t1...
  specialize (IHt2_1 (tU t1_1 t1_2)). specialize (IHt2_2 (tU t1_1 t1_2)).
  destruct (type_eqdec t1_1 t2_1); destruct (type_eqdec t1_2 t2_2)...
  destruct (type_eqdec t1_1 t2_1); destruct (type_eqdec t1_2 t2_2)...
  apply S_Cons... apply S_Cons... apply S_Cons...
  destruct o. destruct o0.
  destruct (id_eqdec i0 i); destruct (type_eqdec t1_1 t2_1);
  destruct (type_eqdec t1_2 t2_2); destruct (obj_eqdec o o0);
  destruct (prop_eqdec p0 p)... destruct (obj_eqdec o0 o).
  crush. crush. crush. destruct (id_eqdec i0 i)...
  destruct (type_eqdec t1_1 t2_1)... destruct (type_eqdec t1_2 t2_2)...
  destruct (prop_eqdec p0 p)... destruct (id_eqdec i0 i)...
  destruct (type_eqdec t1_1 t2_1)... destruct (type_eqdec t1_2 t2_2)...
  destruct (prop_eqdec p0 p)... destruct o0. crush. crush.
Qed.

Definition join (t1 t2:type) : type :=
if simple_subtype t1 t2 then t2
else if simple_subtype t2 t1 then t1
else tU t1 t2.

Lemma join_super_lhs : forall t1 t2 tsuper,
join t1 t2 = tsuper
-> SubType t1 tsuper.
Proof with crush.
  intros.
  unfold join in H.
  remember (simple_subtype t1 t2) as simpb.
  destruct simpb. apply simple_subtype_valid...
  remember (simple_subtype t2 t1) as simpb.
  destruct simpb... 
Qed.
 
Lemma join_super_rhs : forall t1 t2 tsuper,
join t1 t2 = tsuper
-> SubType t2 tsuper.
Proof with crush.
  intros.
  unfold join in H.
  remember (simple_subtype t1 t2) as simpb.
  destruct simpb...  
  remember (simple_subtype t2 t1) as simpb.
  destruct simpb... apply simple_subtype_valid...
Qed.

Lemma join_super_lhs_Refl : forall t1 t2,
SubType t1 (join t1 t2).
Proof with crush.
  intros.
  unfold join.
  remember (simple_subtype t1 t2) as simpb.
  destruct simpb...  apply simple_subtype_valid...
  remember (simple_subtype t2 t1) as simpb.
  destruct simpb...
Qed.
Hint Resolve join_super_lhs_Refl.

Lemma join_super_rhs_Refl : forall t1 t2,
SubType t2 (join t1 t2).
Proof with crush.
  intros.
  unfold join.
  remember (simple_subtype t1 t2) as simpb.
  destruct simpb...  
  remember (simple_subtype t2 t1) as simpb.
  destruct simpb... apply simple_subtype_valid...
Qed.
Hint Resolve join_super_rhs_Refl.

Lemma neg_And_comm : forall o t P,
(o ::~ t) && P = P && (o ::~ t).
Proof. intros. apply And_comm. Qed.

Lemma contra : forall P,
P && (Not P) = FF.
Proof.
  intros. apply prop_equality.
  apply P_Contra. auto.
Qed.
Hint Rewrite contra.

Lemma contra_rev : forall P,
(Not P) && P = FF.
Proof.
  intros. apply prop_equality.
  rewrite And_comm. apply P_Contra. auto.
Qed.

Lemma contra_type1 : forall o t,
(o ::~ t) && (o ::= t) = FF.
Proof.
  intros. apply prop_equality.
  apply P_Contra. auto.
Qed.
Hint Rewrite contra_type1.

Lemma contra_type2 : forall o t,
(o ::= t) && (o ::~ t) = FF.
Proof.
  intros. apply prop_equality.
  apply P_Contra. auto.
Qed.
Hint Rewrite contra_type2.

Fixpoint smash (rock p: prop) : prop :=
  if (prop_eqdec rock (Not p)) then FF else
    match p with
      | q && r => (smash rock q) && (smash rock r)
      | q || r => (smash rock q) || (smash rock r)
      | _ => p
    end.

Lemma And_disjsyl : forall P Q,
Not P && (P || Q) = Not P && Q.
Proof with crush.
 intros. rewrite And_over_Or.
  rewrite contra_rev...
Qed.
Hint Resolve And_disjsyl.

Lemma And_disjsyl2 : forall P Q,
Not P && (Q || P) = Not P && Q.
Proof with crush.
 intros. rewrite And_over_Or.
  rewrite contra_rev...
Qed.
Hint Resolve And_disjsyl2.


Lemma smash_valid : forall Q P,
P && Q = P && (smash P Q).
Proof with crush.
  intros Q; induction Q...
  destruct (prop_eqdec P (o ::~ t))...
  destruct (prop_eqdec P (o ::= t))...
  destruct (prop_eqdec P (Q1 --> Not Q2))...
  rewrite <- IHQ2. rewrite (And_comm ((Q1 --> Not Q2))).
  rewrite contra...
  destruct (prop_eqdec (smash P Q1) FF)...
  rewrite And_assoc... 
  destruct (prop_eqdec (smash P Q2) FF)...
  rewrite And_comm. rewrite <- IHQ2.
  rewrite <- And_assoc. rewrite (And_comm Q2 P).
  rewrite IHQ2...
  rewrite <- IHQ2. rewrite And_assoc.
  rewrite IHQ1. rewrite And_comm.
  rewrite And_assoc. rewrite (And_comm Q2 P).
  rewrite IHQ2. rewrite <- And_assoc. 
  rewrite (And_comm (smash P Q2)). reflexivity.
  destruct (prop_eqdec P (Not Q1 && Not Q2))...
  rewrite And_comm. apply contra.
  rewrite And_over_Or. rewrite And_over_Or...
  destruct (prop_eqdec P FF)...
  destruct (prop_eqdec P Unk)...
Qed.  

Lemma T_If_join :
    forall τ τ1 τ2 τ3 o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf (Γ && ψ1) e2 τ2 ψ2 o
      -> TypeOf (Γ && (Not ψ1)) e3 τ3 ψ3 o
      -> (τ = join τ2 τ3 \/ τ = join τ3 τ2)
      -> TypeOf Γ (If e1 e2 e3) τ ((ψ1 && ψ2) || ((Not ψ1) && ψ3)) o.
Proof with crush.
  intros.
  eapply T_If... eassumption. crush.
  eapply (T_Subsume _ τ2)... eassumption. crush.
  eapply (T_Subsume _ τ2)... eassumption. crush.
  eapply (T_Subsume _ τ3)... eassumption. crush.
  eapply (T_Subsume _ τ3)... eassumption. crush.
Qed.

Ltac bamcis' subsuming :=
  crush;
     (match goal with
        | [ |- ?lhs = ?rhs] => first[solve [reflexivity] |
                                     solve [crush] |
                                     solve [(eapply nat_subst); crush] |
                                     solve [(eapply top_subst); crush] |
                                     solve [(eapply bot_subst); crush] |
                                     solve [(eapply str_subst); crush] |
                                     solve [(eapply true_subst); crush] |
                                     solve [(eapply false_subst); crush] |
                                     solve [(eapply bool_subst); crush] |
                                     solve [(eapply TT_subst); crush] |
                                     solve [(eapply FF_subst); crush] |
                                     solve [(eapply Unk_subst); crush] |
                                     solve [(eapply None_subst); crush] ]
        | [ |- Proves _ _] => 
          (solve [(eapply P_Atom; crush)])
        | [H : Proves ?P ?Q |- Proves (?Γ && ?P) ?Q] =>
          (eapply P_Conjl_rhs; exact H)
        | [H : Proves ?P ?Q |- Proves (?P && ?Γ) ?Q] =>
          (eapply P_Conjl_lhs; exact H)
        | [H : Proves ?P ?Q |- Proves ?P (?Q || ?R)] =>
          (eapply P_Add_lhs; exact H)
        | [H : Proves ?P ?R |- Proves ?P (?Q || ?R)] =>
          (eapply P_Add_rhs; exact H)
        | |- SubObj ?o ?o => eapply SO_Refl
        | |- SubObj None ?o => eapply SO_Refl
        | |- SubObj ?o None => eapply SO_Top
        | |- Proves ?P ?P => eapply P_Atom
        | |- Proves (TT && _) _ =>
          eapply P_Conjl_rhs; bamcis' False
        | |- Proves (_ && TT) _ =>
          eapply P_Conjl_lhs; bamcis' False
        | [ |- Proves _ (?o ::= tTop)] => 
          (solve [(eapply bound_in_Proves_Top; crush)])
        (* Union w/ not to specify*)
        | [ |- Proves ?P (?o ::= ?t)] =>
          let types_exp := constr:(find_types P o) in
          let types := eval simpl in types_exp in
          (unionnegtac o types)
        (* Simple Disjunctive Syllogism *)
        | [ |- Proves ?P ?Q] =>
          let disjs_exp := constr:(find_disj_neighbor P Q) in
          let disjs := eval simpl in disjs_exp in
          (disjsyltac P Q disjs ltac:(bamcis' False))
        | |- SubType ?P tTop => eapply S_Top
        | |- SubType ?P ?P => eapply S_Refl
        | |- TypeOf _ (# _) _ _ _ => 
          solve [eapply T_Nat; bamcis' False]
        | |- TypeOf _ (eOp _) _ _ _ => 
          solve [eapply T_Const; bamcis' False]
        | |- TypeOf _ #t _ _ _ =>
          solve [eapply T_True; bamcis' False]
        | |- TypeOf _ #f _ _ _ =>
          solve [eapply T_False; bamcis' False]
        | |- TypeOf _ ($ _) _ _ _ =>
          solve [eapply T_Var; bamcis' False]
        | |- TypeOf _ (λ _ _ _) _ _ _ =>
          solve [eapply T_Abs; bamcis' False]
        | |- TypeOf _ (Apply _ _) _ _ _ =>
          solve [eapply T_App; bamcis' False]
        | |- TypeOf _ (If _ _ _) _ _ _ =>
          first [solve[eapply T_If_join with (o := None); bamcis' False] |
                 solve[eapply T_If with (o := None); bamcis' False] |
                 solve[eapply T_If; bamcis' False]]
        | |- TypeOf _ (Let _ _ _) _ _ _ =>
          solve [eapply T_Let; bamcis' False]
        | |- TypeOf _ _ ?t _ _ =>
          match subsuming with
          | True => fail
          | False => 
            first [solve[(eapply (T_Subsume t t)); bamcis' True] |
                   solve[(eapply T_Subsume); bamcis' True]]
          end
        (* EJECT!! EJECT!! *)
        | |- SubObj None (Some _) => fail 1
        | |- SubObj tTop tNat => fail 1
        (* I give up *)
        | _ => auto
        end).

Ltac bamcis := bamcis' False.

(** Macros *)
(** Unhygeinic Or macro *)
Notation TMP := (Id 0).
Notation X := (Id 1).
Notation Y := (Id 2).
Notation F := (Id 3).
Notation G := (Id 4).
Notation OR := (fun p q => 
                  (Let TMP p
                       (If ($ TMP)
                           ($ TMP)
                           q))).
(** And Macro *)
Notation AND := (fun p q =>
                (If p q #f)).
Hint Extern 10 (id) => exact X.
Hint Extern 10 (prop) => exact TT.

(** ** Automation Tests *)

(* Disjunctive Syllogism Test *)
Example bamcis_disjsyl1 : 
Proves ((((var X) ::= tNat) || ((var X) ::= tStr)) 
          && TT 
          && ((var X) ::~ tNat) 
          && TT)
       ((var X) ::= tStr).
Proof. bamcis. Qed.

(* Disjunctive Syllogism Test *)
Example bamcis_disjsyl2 : 
Proves ((((var X) ::= tNat) || ((var X) ::= tTop)) 
          && (((var X) ::= tNat) || ((var X) ::= tStr))
          && ((var X) ::~ tNat) 
          && TT)
       ((var X) ::= tStr).
Proof. bamcis. Qed.

(* Disjunctive Syllogism Test *)
Example bamcis_disjsyl3 : 
Proves ((((var X) ::= tNat) || ((var X) ::= tStr))  
          && (((var X) ::= tNat) || ((var X) ::= tTop))
          && ((var X) ::~ tNat) 
          && TT)
       ((var X) ::= tStr).
Proof. bamcis. Qed.

(* Union not-rhs Test *)
Example bamcis_unionnot1 : 
Proves (((var X) ::= (tU tStr tNat)) 
          && TT 
          && ((var X) ::~ tNat) 
          && TT)
       ((var X) ::= tStr).
Proof. bamcis. Qed.

(* Union not-lhs Test *)
Example bamcis_unionnot2 : 
Proves (((var X) ::= (tU tNat tStr)) 
          && TT 
          && ((var X) ::~ tNat) 
          && TT)
       ((var X) ::= tStr).
Proof. bamcis. Qed.

(* Union not-lhs Test w/ other type value present*)
Example bamcis_unionnot3 : 
Proves (((var X) ::= tTop) 
          && ((var X) ::= (tU tNat tStr)) 
          && TT 
          && ((var X) ::~ tNat))
       ((var X) ::= tStr).
Proof. bamcis. Qed.  

(* Checking propositions flow through If *)
Example bamcis_ifwrapper1:
  TypeOf ((var X) ::= tTop)
         (If (Nat? ($ X))
             #t
             #f)
         tBool
         ((var X) ::= tNat)
         None.
Proof. 
  bamcis. 
Grab Existential Variables.
auto.
Qed.
  
(* Checking propositions flow through If flipped *)
Example bamcis_ifwrapper2:
  TypeOf ((var X) ::= tTop)
         (If (Nat? ($ X))
             #f
             #t)
         tBool
         ((var X) ::~ tNat)
         None.
Proof.
  bamcis. 
Grab Existential Variables.
auto.
Qed.


(* Checking propositions flow through If wrapped in a λ *)
Example bamcis_ifwrapper3:
    TypeOf TT
           (λ X tTop
              (If (Nat? ($ X))
                  #f
                  #t))
           (tλ X
               tTop tBool
               ((var X) ::~ tNat)
               None)
           TT
           None.
Proof.
  bamcis.
Grab Existential Variables.
auto.
Qed.

Example bamcis_OR1:
  TypeOf ((var X) ::= tTop)
         (OR (Nat? ($ X)) (Str? ($ X)))
         tBool
         ((var X) ::= (tU tNat tStr))
         None.
Proof with bamcis.
  eapply T_Subsume.
  eapply T_Let...
  do 4 (rewrite And_over_Or).
  do 10 (rewrite And_over_Or).
  do 10 (rewrite And_over_Or).
  do 10 (rewrite And_over_Or).
  do 10 (rewrite And_over_Or).

  bamcis.
  rewrite <- (And_assoc (var X ::= tTop)).
  rewrite <- (And_assoc (var X ::= tTop)).

  rewrite (smash_valid (var X ::~ tF)).
  

P && Q = P && (smash P Q).

  repeat rewrite And_over_Or.
  do 2 (rewrite neg_And_comm).

  repeat rewrite Or_over_And.
crush.
  bamcis. Admitted.

(** *Typechecked Examples *)

Example example1:
    TypeOf ((var X) ::= tTop)
           (If (Nat? ($ X))
               (Add1 ($ X))
               (#0))
           tNat
           TT
           None.
Proof.
  bamcis.
Solve All Obligations using auto.
Grab Existential Variables. 
auto. auto.
Qed.

Example example2:
    TypeOf TT
           (λ X (tU tStr tNat)
              (If (Nat? ($ X))
                  (Add1 ($ X))
                  (StrLen ($ X))))
           (tλ X
               (tU tStr tNat) tNat
               TT
               None)
           TT
           None.
Proof.
  bamcis.
Grab Existential Variables.
auto. auto. auto.  
Qed.

Example example3:
    TypeOf
      ((var Y) ::= tTop)
      (Let X (Nat? ($ Y))
          (If ($ X)
              ($ Y)
              (# 0)))
      tNat
      TT
      None.
Proof with bamcis.
  bamcis.
Grab Existential Variables.
auto. auto.
Qed.

Example example4:
    TypeOf (((var X) ::= tTop) 
              && ((var F) ::= (tλ X (tU tStr tNat) tNat TT None)))
           (If (OR (Nat? ($ X)) (Str? ($ X)))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof with bamcis.
  eapply (T_Subsume tNat tNat).
  eapply T_If... crush.
  eapply T_App...
  apply T_Var...
  bamcis.

  bamcis.
Admitted.

Example example5:
    TypeOf (((var X) ::= tTop) && ((var Y) ::= tTop))
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (# 0))
           tNat
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example7:
  forall X y,
    TypeOf (((var X) ::= tTop) && ((var y) ::= tTop))
           (If (If (Nat? ($ X)) (Str? ($ y)) #f)
               (Plus ($ X) (StrLen ($ y)))
               (# 0))
           tNat
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example8:
    TypeOf TT
           (λ X tTop
              (OR (Str? ($ X)) (Nat? ($ X))))
           (tλ X
               tTop (tU tStr tNat)
               ((var X) ::= (tU tStr tNat))
               None)
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example9:
    TypeOf (((var X) ::= tTop)
              && ((var F) ::= (tλ X (tU tStr tNat) tNat TT None)))
           (If (Let TMP (Nat? ($ X))
                    (If ($ TMP) ($ TMP) (Str? ($ X))))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example10:
let p := (Id 23) in
    TypeOf ((var p) ::= (tCons tTop tTop))
           (If (Nat? (Car ($ p)))
               (Add1 (Car ($ p)))
               (# 7))
           tNat
           TT
           None.
Proof. 
  bamcis.

Example example11:
let p := (Id 23) in
    TypeOf ((var p) ::= (tCons tTop tTop)
            && ((var G) ::= (tλ X (tU tNat tNat) tNat TT None)))
           (If (AND (Nat? (Car ($ p))) (Nat? (Cdr ($ p))))
               (Apply ($ G) ($ p))
               (# 42))
           tNat
           TT
           None.
Proof.
  bamcis.
Admitted.

Example example12:
    TypeOf TT
           (λ X (tCons tTop tTop)
              (Nat? (Car ($ X))))
           (tλ Y
               (tCons tTop tTop) (tCons tTop tTop)
               ((var Y) ::= (tCons tNat tTop))
               None)
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example13:
    TypeOf (((var X) ::= tTop) && ((var Y) ::= (tU tNat tStr)))
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (If (Nat? ($ X))
                   (Plus ($ X) ($ Y))
                   (# 42)))
           tNat
           TT
           None.
Proof. 
  bamcis.
Admitted.

Example example14:
  forall X y,
    TypeOf (((var X) ::= tTop) && ((var y) ::= (tCons tTop (tU tNat tStr))))
           (If (AND (Nat? ($ X)) (Str? (Cdr ($ y))))
               (Plus ($ X) (StrLen ($ y)))
               (If (Nat? ($ X))
                   (Plus ($ X) (Cdr ($ y)))
                   (# 42)))
           tNat
           TT
           None.
Proof. 
  bamcis.
Admitted.

Abort All.
End LTR.
