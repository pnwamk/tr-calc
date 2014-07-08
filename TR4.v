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
| tCons : type
| tU    : type -> type -> type
| tPair : type -> type -> type
| tλ    : id -> type -> type -> prop -> opt object -> type

with prop : Set :=
| Atom : fact -> prop
| And  : prop -> prop -> prop
| Or   : prop -> prop -> prop
| Imp  : prop -> prop -> prop
| TT   : prop
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
    | FF => TT
    | TT => FF
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
          ((var x) ::= (tPair tTop tTop))
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
    | tPair t1 t2 =>
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
    | tPair t1 t2 => tPair (subst_t' b t1 opto x)
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

Fixpoint is_tPair (t:type) : opt (type * type) :=
  match t with
    | tPair t1 t2 => Some (t1,t2)
    | _ => None
  end.

Lemma is_tPair_eq : forall t t1 t2,
Some (t1,t2) = is_tPair t
-> t = tPair t1 t2.
Proof.
  intros.
  destruct t; crush.
Qed.


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

Fixpoint rem (p:prop) (l:list prop) : list prop :=
  match l with
    | nil => nil
    | p' :: ps =>
      if prop_eqdec p p' 
      then ps
      else p' :: (rem p ps)
  end.


Inductive Proves : (list prop * prop) -> Prop :=
| P_Axiom :
    forall f Γ,
      In (Atom f) Γ
    -> Proves (Γ, (Atom f))
| P_Contradiction :
    forall o t1 t2 Γ P,
      In (o ::= t1) Γ
      -> In (o ::= t2) Γ
      -> (~CommonSubtype (t1, t2))
      -> Proves (Γ, P)
| P_UnionElim :
    forall P t1 t2 o Γ,
      In (o ::= (tU t1 t2)) Γ
      -> Proves (((o ::= t1)::(rem (o ::= (tU t1 t2)) Γ)), P)
      -> Proves (((o ::= t2)::(rem (o ::= (tU t1 t2)) Γ)), P)
      -> Proves (Γ, P)
| P_PairElim :
    forall t1 t2 x π Γ P,
      In ((obj π x) ::= (tPair t1 t2)) Γ
      -> Proves ((((obj π x) ::= tCons)
                    ::((obj (π ++ [car]) x) ::= t1)
                    ::((obj (π ++ [cdr]) x) ::= t2)
                    ::(rem ((obj π x) ::= (tPair t1 t2)) Γ)), P)
      -> Proves (Γ, P)
| P_Top :
  forall t o Γ,
    In (o ::= t) Γ
    -> Proves (Γ, (o ::= tTop))
| P_Union_lhs :
    forall t1 t2 o Γ,
      Proves (Γ, (o ::= t1))
      -> Proves (Γ, (o ::= (tU t1 t2)))
| P_Union_rhs :
    forall t1 t2 o Γ,
      Proves (Γ, (o ::= t2))
      -> Proves (Γ, (o ::= (tU t1 t2)))
| P_Pair :
    forall t1 t2 x π Γ,
      Proves (Γ, ((obj (π ++ [car]) x) ::= t1))
      -> Proves (Γ, ((obj (π ++ [cdr]) x) ::= t2))
      -> Proves (Γ, ((obj π x) ::= tCons))
      -> Proves (Γ, ((obj π x) ::= (tPair t1 t2)))
| P_Fun :
    forall x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 Γ ox,
      In (ox ::= (tλ x1 t1a t1r p1 o1)) Γ
      -> Proves ([(ox ::= (subst_t t1r (Some (var x2)) x1))], (ox ::= t2r))
      -> Proves ([(ox ::= t2a)], (ox ::= (subst_t t1a (Some (var x2)) x1)))
      -> Proves ([(subst_p p1 (Some (var x2)) x1)], p2)
      -> SubObj (subst_o o1 (Some (var x2)) x1) o2
      -> Proves (Γ, (ox ::= (tλ x2 t2a t2r p2 o2)))
| P_Bot :
    forall Γ P o,
      In (o ::= tBot) Γ
      -> Proves (Γ, P)
| P_True :
    forall Γ,
      Proves (Γ,TT)
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
       -> Proves (Γ, (P --> Q)).

Fixpoint type_weight (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      2 + (plus (type_weight t1) (type_weight t2))
    | tλ x t1 t2 p _ => 1 + (type_weight t1) 
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
    | TT => 1
    | FF => 1
    | Unk => 1
  end.
Hint Unfold type_weight prop_weight.

Fixpoint env_weight (l:list prop) : nat :=
  match l with
    | nil => 0
    | p :: ps => (prop_weight p) + (env_weight ps)
  end.
Hint Unfold env_weight.

Definition proof_weight (p:(list prop) * prop) : nat :=
plus (env_weight (fst p)) (prop_weight (snd p)).
Hint Unfold proof_weight.

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

Lemma rem_Imp_lhs_weight : forall P P1 P2 L,
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

Lemma rem_Imp_rhs_weight : forall P P1 P2 L,
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
Qed.

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
Qed.  

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
Qed.

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
Qed.  

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
Qed.  

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
Qed.

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
Qed.


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
Qed.

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
Qed.

Lemma rem_Union_lhs_weight : forall P o t1 t2 L,
In (o ::= (tU t1 t2)) L 
-> proof_weight (((o ::= t1)::(rem (o ::= (tU t1 t2)) L)), P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (o ::= (tU t1 t2)) (o ::= (tU t1 t2))).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (o ::= (tU t1 t2)) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.

Lemma rem_Union_rhs_weight : forall P o t1 t2 L,
In (o ::= (tU t1 t2)) L 
-> proof_weight (((o ::= t2)::(rem (o ::= (tU t1 t2)) L)), P) < proof_weight (L, P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec (o ::= (tU t1 t2)) (o ::= (tU t1 t2))).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec (o ::= (tU t1 t2)) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.

Lemma rem_Pair_weight : forall P π x t1 t2 L,
In ((obj π x) ::= (tPair t1 t2)) L
-> proof_weight ((((obj π x) ::= tCons)
                     ::((obj (π ++ [car]) x) ::= t1)
                     ::((obj (π ++ [cdr]) x) ::= t2)
                     ::(rem ((obj π x) ::= (tPair t1 t2)) L)), P)
<
proof_weight (L,P).
Proof.
  intros.
  induction L. crush.
  destruct H. subst.
  unfold proof_weight in *. unfold rem.
  destruct (prop_eqdec ((obj π x) ::= (tPair t1 t2)) ((obj π x) ::= (tPair t1 t2))).
  crush. crush.
  unfold proof_weight. unfold rem.
  destruct (prop_eqdec ((obj π x) ::= (tPair t1 t2)) a). crush.
  apply IHL in H. fold rem. unfold proof_weight in *. crush.
Qed.

(* BOOKMARK *)
Lemma subst_t_weight : forall t y x, 
type_weight (subst_t t (Some (var y)) x) = type_weight t.
Proof.
  intros t y x.
  induction t; crush.
  fold subst_t. rewrite IHt1. rewrite IHt2. crush.
  unfold subst_t. unfold subst_t'.
  destruct (id_eqdec x i). crush.
  crush. 
Qed.

Lemma subst_p_weight : forall p y x, 
prop_weight (subst_p p (Some (var y)) x) <= prop_weight p.
Proof.
  intros p y x.
  induction p; crush.
  destruct f. crush.
  destruct o as [π z].
  unfold subst_p. unfold subst_p'.
  destruct (id_eqdec x z). simpl.
  fold subst_t'. fold subst_t.
  rewrite subst_t_weight. omega.
  destruct (set_mem id_eqdec z (fv_set_t t)).
  destruct t; crush. simpl. omega.
  fold subst_p. omega.
  fold subst_p. omega.
Qed.

Lemma rem_λ_weight1 : forall L x0 σ τ ψ o'' y τ' σ' o,
In (Atom (istype o (tλ x0 σ τ ψ o''))) L
-> type_weight (subst_t τ (Some (var y)) x0) + 0 + type_weight τ' <
   env_weight L + S (type_weight σ' + type_weight τ').
Proof.
  intros.
  induction L. crush.
  destruct a; crush. 
  rewrite subst_t_weight. crush.
Qed.

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
  rewrite subst_t_weight. crush.
  crush. 
  unfold proof_weight in *. simpl in *.
  destruct a as [[o'' t''] |P1 P2|P1 P2|P1 P2| | |]; crush.
  destruct t''; crush.
Qed.

Lemma rem_λ_weight3 : forall L x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 o o',
In (Atom (istype o (tλ x1 t1a t1r p1 o1))) L
-> proof_weight ([subst_p p1 (Some (var x2)) x1], p2) <
   proof_weight (L, Atom (istype o' (tλ x2 t2a t2r p2 o2))).
Proof.
  intros.
  induction L. crush.
  unfold proof_weight in *. simpl in *.
  destruct H. subst.
  unfold prop_weight at 3. unfold fact_weight. unfold type_weight.
  fold type_weight.
  crush.
  assert (prop_weight (subst_p p1 (Some (var x2)) x1) <= prop_weight p1).
    apply subst_p_weight. omega.
  rewrite subst_p_weight.
  rewrite subst_t_weight. crush.
  crush. 
  unfold proof_weight in *. simpl in *.
  destruct a as [[o'' t''] |P1 P2|P1 P2|P1 P2| |]; crush.
  destruct t''; crush.
Qed.

Lemma conj_dec : forall P Q,
{P} + {~P}
-> {Q} + {~Q}
-> {P /\ Q} + {~(P /\ Q)}.
Proof. crush. Qed.

Lemma disj_dec : forall P Q,
{P} + {~P}
-> {Q} + {~Q}
-> {P \/ Q} + {~(P \/ Q)}.
Proof. crush. Qed.


Lemma Proves_dec : forall (goal:(list prop * prop)), {Proves goal} + {~Proves goal}.
Proof.
  (* Proves_dec *)
  induction goal as ((Γ, P),IH) using
    (well_founded_induction
      (well_founded_ltof _ proof_weight)).
  (* P_Contra *)
  remember (contains_contradiction Γ) as contra.
  symmetry in Heqcontra.
  destruct contra as [[[o t1] t2]|].
  apply contains_contradiction_Some in Heqcontra.
  left; apply (P_Contradiction o t1 t2); crush.
  (* No contradictions *)
  assert (forall o t1 t2, 
            In (o ::= t1) Γ 
            -> In (o ::= t2) Γ
            -> CommonSubtype (t1, t2)) as HNoContra.
  apply contains_contradiction_None; crush. clear Heqcontra. 
  (* iterative solving function *)
  destruct (
    find_In_witness _ (fun a =>
      match a with
        (* P_False *)
        | FF => True
        (* P_Simpl *)
        | P1 && P2 => Proves ((P1::P2::(rem (P1 && P2) Γ)), P)
        (* P_DisjElim *)
        | P1 || P2 => Proves ((P1::(rem (P1 || P2) Γ)), P) 
                      /\ Proves ((P2::(rem (P1 || P2) Γ)), P)
        (* P_MP *)
        | P1 --> P2 =>  (Proves ((rem (P1 --> P2) Γ), P1))
                        /\ (Proves ((P1::P2::(rem (P1 --> P2) Γ)), P))
        (* P_UnionElim *)
        | Atom (istype o (tU t1 t2)) => 
          (Proves (((o ::= t1)::(rem (o ::= (tU t1 t2)) Γ)), P))
          /\ (Proves (((o ::= t2)::(rem (o ::= (tU t1 t2)) Γ)), P))
        (* P_PairElim *)
        | Atom (istype (obj π x) (tPair t1 t2)) => 
          Proves ((((obj π x) ::= tCons)
                     ::((obj (π ++ [car]) x) ::= t1)
                     ::((obj (π ++ [cdr]) x) ::= t2)
                     ::(rem ((obj π x) ::= (tPair t1 t2)) Γ)), P)
        (* P_Bot *)
        | Atom (istype o tBot) => True
        | _ => False
      end
    ) Γ) as [(a,(HaA,HaB))|antecedent_nonexist].
- intros a HIn.
  destruct a as [[[x π] t]|P1 P2|P1 P2|P1 P2| |]; try (solve[auto]).
  + destruct t as [ | | | | | |t1 t2|t1 t2| | ]; try (solve[auto]).
    * apply conj_dec. apply IH. unfold ltof. unfold proof_weight. simpl. 
      apply rem_Union_lhs_weight. auto.
      apply IH. unfold ltof. unfold proof_weight. simpl. 
      apply rem_Union_rhs_weight. auto.
    * apply IH. unfold ltof. unfold proof_weight. simpl. 
      apply rem_Pair_weight. auto.
  + apply IH. apply (rem_And_weight P). auto. 
  + apply conj_dec.
    apply IH. apply rem_Or_lhs_weight. auto.
    apply IH. apply rem_Or_rhs_weight. auto.
  + apply conj_dec.
    apply IH. apply rem_Imp_lhs_weight. auto.
    apply IH. apply rem_Imp_rhs_weight. auto.
- left. destruct a as [[[π x] t] |P1 P2|P1 P2|P1 P2| |]; crush.
  + destruct t as [ | | | | | |t1 t2|t1 t2| | ]; try (solve[crush]).
    eapply P_Bot; eauto.
    eapply (P_UnionElim P t1 t2); crush. exact HaA. auto. auto.
    eapply (P_PairElim t1 t2); crush. exact HaA. auto. 
  + apply (P_Simpl _ P1 P2); crush.
  + apply (P_DisjElim _ P1 P2); crush.
  + apply (P_MP _ P1 P2); crush.
  + apply P_False; auto.
- assert (succedent_dec:
  {(match P with
      (* P_Conj *)
      | PA && PB  => Proves (Γ, PA) /\ Proves (Γ, PB)
      (* P_Add_[lhs/rhs] *)
      | PA || PB  => Proves (Γ, PA) \/ Proves (Γ, PB)
      (* P_CP *)
      | PA --> PB => Proves (PA::Γ, PB)
      (* P_Top *)
      | (Atom (istype o tTop)) => types_in o Γ <> nil
      (* P_UnionElim *)
      | (Atom (istype o (tU t1 t2))) =>
        Proves (Γ, (o ::= t1)) \/ Proves (Γ, (o ::= t2))
      (* P_PairElim *)
      | (Atom (istype (obj π x) (tPair t1 t2))) =>
        Proves (Γ, ((obj (π ++ [car]) x) ::= t1))
        /\ Proves (Γ, ((obj (π ++ [cdr]) x) ::= t2))
        /\ Proves (Γ, ((obj π x) ::= tCons))
      (* P_Fun *)
      | Atom (istype ox (tλ x2 t2a t2r p2 o2)) =>
        (exists t,
           match t with
             | tλ x1 t1a t1r p1 o1 =>
               In (ox ::= (tλ x1 t1a t1r p1 o1)) Γ
               /\ Proves ([(ox ::= (subst_t t1r (Some (var x2)) x1))], (ox ::= t2r))
               /\ Proves ([(ox ::= t2a)], (ox ::= (subst_t t1a (Some (var x2)) x1)))
               /\ Proves ([(subst_p p1 (Some (var x2)) x1)], p2)
               /\ SubObj (subst_o o1 (Some (var x2)) x1) o2
               /\ Proves (Γ, (ox ::= (tλ x2 t2a t2r p2 o2)))
             | _ => False
           end)
      (* P_Axiom *)
      | Atom f => In (Atom f) Γ
      | _ => False
    end)
  } + {
    ~(match P with
      (* P_Conj *)
      | PA && PB  => Proves (Γ, PA) /\ Proves (Γ, PB)
      (* P_Add_[lhs/rhs] *)
      | PA || PB  => Proves (Γ, PA) \/ Proves (Γ, PB)
      (* P_CP *)
      | PA --> PB => Proves (PA::Γ, PB)
      (* P_Top *)
      | (Atom (istype o tTop)) => types_in o Γ <> nil
      (* P_Union_[lhs/rhs] *)
      | (Atom (istype o (tU t1 t2))) =>
        Proves (Γ, (o ::= t1)) \/ Proves (Γ, (o ::= t2))
      (* P_Pair *)
      | (Atom (istype (obj π x) (tPair t1 t2))) =>
        Proves (Γ, ((obj (π ++ [car]) x) ::= t1))
        /\ Proves (Γ, ((obj (π ++ [cdr]) x) ::= t2))
        /\ Proves (Γ, ((obj π x) ::= tCons))
      (* P_Fun *)
      | Atom (istype ox (tλ x2 t2a t2r p2 o2)) =>
        (exists t,
           match t with
             | tλ x1 t1a t1r p1 o1 =>
               In (ox ::= (tλ x1 t1a t1r p1 o1)) Γ
               /\ Proves ([(ox ::= (subst_t t1r (Some (var x2)) x1))], (ox ::= t2r))
               /\ Proves ([(ox ::= t2a)], (ox ::= (subst_t t1a (Some (var x2)) x1)))
               /\ Proves ([(subst_p p1 (Some (var x2)) x1)], p2)
               /\ SubObj (subst_o o1 (Some (var x2)) x1) o2
               /\ Proves (Γ, (ox ::= (tλ x2 t2a t2r p2 o2)))
             | _ => False
           end)
      (* P_Axiom *)
      | Atom f => In (Atom f) Γ
      | _ => False
    end)}).
 destruct P as [[[π x] t] |P1 P2|P1 P2|P1 P2| |]; try (solve[auto]).
 destruct t as [ | | | | | | | | | x2 t2a t2r p2 o2 ]; 
   try (solve[auto | 
              apply (In_dec prop_eqdec (Atom (istype (obj π x) _)) Γ)]).
  + destruct (types_in (obj π x) Γ); auto. left. crush.
  + apply disj_dec. 
    apply IH. unfold ltof. unfold proof_weight. crush.
    apply IH. unfold ltof. unfold proof_weight. crush.
  + apply conj_dec. 
    apply IH. unfold ltof. unfold proof_weight. crush.
    apply conj_dec. apply IH. unfold ltof. unfold proof_weight. crush.
    apply IH. unfold ltof. unfold proof_weight. crush.
    (* BOOKMARK *)
  + remember 
      (fun p => 
         match p with
           | Atom (istype o (tλ x1 t1a t1r p1 o1)) =>
             In (o ::= (tλ x1 t1a t1r p1 o1)) Γ
             /\ Proves ([(o ::= (subst_t t1r (Some (var x2)) x1))], (o ::= t2r))
             /\ Proves ([(o ::= t2a)], (o ::= (subst_t t1a (Some (var x2)) x1)))
             /\ Proves ([(subst_p p1 (Some (var x2)) x1)], p2)
             /\ SubObj (subst_o o1 (Some (var x2)) x1) o2
             /\ Proves (Γ, (o ::= (tλ x2 t2a t2r p2 o2)))
           | _ => False
         end) as pfun.
    assert (forall p, {pfun p} + {~(pfun p)}) as pfun_dec.
      subst.
      destruct p as [[o t] |P1 P2|P1 P2|P1 P2| |]; try(solve[crush]).
      destruct t as [ | | | | | | | | | x1 t1a t1r p1 o1 ]; 
        try (solve[auto]).
      remember (In_dec prop_eqdec (Atom (istype o (tλ x1 t1a t1r p1 o1))) Γ) as HIn.
      clear HeqHIn.
      destruct HIn as [HIn | HnotIn].
      apply conj_dec. auto.
      apply conj_dec. apply IH. unfold ltof. unfold proof_weight. crush.
        eapply rem_λ_weight1. exact HIn.
      apply conj_dec. apply IH. unfold ltof. eapply rem_λ_weight2.
        exact HIn.
      apply conj_dec. apply IH. unfold ltof. 
(*
Lemma find_witness:
  forall(A:Type) (P:A->Prop) (L:list A),
    (forall a, {P a}+{~P a}) ->
    { a | In a L /\ P a } + { forall a, In a L -> ~P a }.


is_tλ
*)
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
  apply (antecedent_nonexist (Atom (istype o t'))). auto.
  apply V_subtype; auto.
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
  intros tp. 
  induction tp as ((t1, t2),IHSub) using
    (well_founded_induction
      (well_founded_ltof _ (fun tp => ((type_weight (fst tp)) 
                                       + (type_weight (snd tp)))))).
  unfold ltof in IHSub.
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
      -> TypeOf Γ (Cons e1 e2) (tPair τ1 τ2) TT None
| T_Car :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [car] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [car] x)) o x) = o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
      -> TypeOf Γ (Car e) τ1 ψ o'
| T_Cdr :
    forall τ1 τ2 o' o Γ e ψ0 ψ x,
      (subst_p ((obj [cdr] x) ::~ tF) o x) = ψ
      -> (subst_o (Some (obj [cdr] x)) o x) = o'
      -> TypeOf Γ e (tPair τ1 τ2) ψ0 o
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
  destruct (type_eqdec t1 (tPair t2_1 t2_2)); crush.
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
| tPair t1 t2, tPair t3 t4 =>
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
    TypeOf ((var p) ::= (tPair tTop tTop))
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
    TypeOf ((var p) ::= (tPair tTop tTop)
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
           (λ X (tPair tTop tTop)
              (Nat? (Car ($ X))))
           (tλ Y
               (tPair tTop tTop) (tPair tTop tTop)
               ((var Y) ::= (tPair tNat tTop))
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
    TypeOf (((var X) ::= tTop) && ((var y) ::= (tPair tTop (tU tNat tStr))))
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
