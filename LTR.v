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
Defined.


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
Defined.
  
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
Defined.

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
Defined.


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


Inductive Proves : list prop -> prop -> Prop :=
| P_Axiom :
    forall Γ f,
      In (Atom f) Γ
    -> Proves Γ (Atom f)
| P_Contradiction :
    forall Γ P t1 t2 o,
      In (o ::= t1) Γ
      -> In (o ::= t2) Γ
      -> (~CommonSubtype (t1, t2))
      -> Proves Γ P
| P_UnionElim :
    forall Γ P t1 t2 o ,
      In (o ::= (tU t1 t2)) Γ
      -> Proves ((o ::= t1)::(rem (o ::= (tU t1 t2)) Γ)) P
      -> Proves ((o ::= t2)::(rem (o ::= (tU t1 t2)) Γ)) P
      -> Proves Γ P
| P_PairElim :
    forall Γ P t1 t2 π x,
      In ((obj π x) ::= (tPair t1 t2)) Γ
      -> Proves (((obj π x) ::= tCons)
                    ::((obj (π ++ [car]) x) ::= t1)
                    ::((obj (π ++ [cdr]) x) ::= t2)
                    ::(rem ((obj π x) ::= (tPair t1 t2)) Γ)) 
                   P
      -> Proves Γ P
| P_Top :
  forall Γ t o,
    In (o ::= t) Γ
    -> Proves Γ (o ::= tTop)
| P_Union_lhs :
    forall Γ t1 t2 o,
      Proves Γ (o ::= t1)
      -> Proves Γ (o ::= (tU t1 t2))
| P_Union_rhs :
    forall Γ t1 t2 o,
      Proves Γ (o ::= t2)
      -> Proves Γ (o ::= (tU t1 t2))
| P_Pair :
    forall Γ t1 t2 π x,
      Proves Γ ((obj (π ++ [car]) x) ::= t1)
      -> Proves Γ ((obj (π ++ [cdr]) x) ::= t2)
      -> Proves Γ ((obj π x) ::= tCons)
      -> Proves Γ ((obj π x) ::= (tPair t1 t2))
| P_Fun :
    forall Γ x1 t1a t1r p1 o1 x2 t2a t2r p2 o2 ox,
      In (ox ::= (tλ x1 t1a t1r p1 o1)) Γ
      -> Proves [(ox ::= (subst_t t1r (Some (var x2)) x1))] (ox ::= t2r)
      -> Proves [(ox ::= t2a)] (ox ::= (subst_t t1a (Some (var x2)) x1))
      -> Proves [(subst_p p1 (Some (var x2)) x1)] p2
      -> SubObj (subst_o o1 (Some (var x2)) x1) o2
      -> Proves Γ (ox ::= (tλ x2 t2a t2r p2 o2))
| P_Bot :
    forall Γ P o,
      In (o ::= tBot) Γ
      -> Proves Γ P
| P_True :
    forall Γ,
      Proves Γ TT
| P_False :
    forall Γ P,
      In FF Γ
      -> Proves Γ P
| P_Simpl :
    forall Γ R P Q,
      In (P && Q) Γ
      -> Proves (P::Q::(rem (P && Q) Γ)) R
      -> Proves Γ R
| P_DisjElim :
    forall Γ R P Q,
      In (P || Q) Γ
      -> Proves (P::(rem (P || Q) Γ)) R
      -> Proves (Q::(rem (P || Q) Γ)) R
      -> Proves Γ R
| P_MP :
     forall Γ R P Q,
       In (P --> Q) Γ
       -> Proves (rem (P --> Q) Γ) P
       -> Proves (P::Q::(rem (P --> Q) Γ)) R
       -> Proves Γ R
| P_Conj :
    forall Γ P Q,
      Proves Γ P
      -> Proves Γ Q
      -> Proves Γ (P && Q)
| P_Add_lhs :
    forall Γ P Q,
      Proves Γ P
      -> Proves Γ (P || Q)
| P_Add_rhs :
    forall Γ P Q,
      Proves Γ Q
      -> Proves Γ (P || Q)
 | P_CP :
     forall Γ P Q,
       Proves (P::Γ) Q
       -> Proves Γ (P --> Q).

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
    | TT => 1
    | FF => 0
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
Defined.


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
  destruct (set_mem id_eqdec z (fv_set_t t')).
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
  + tryfalse. 
  + tryfalse.
  + tryfalse.
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
              tryfalse]). 
  + destruct HNoAxiom; crush.
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



Definition Subtype (t1 t2:type) := 
  Proves [((var (Id 0)) ::= t1)] ((var (Id 0)) ::= t2).

Definition Subtype_dec : forall t1 t2,
{Subtype t1 t2} + {~Subtype t1 t2}.
Proof.
  intros t1 t2.
  unfold Subtype. apply Proves_dec.
Defined.

(** ** TypeOf *)

Inductive TypeOf : list prop -> exp -> type -> prop -> opt object -> Prop :=
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
      TypeOf (((var x) ::= σ)::Γ) e τ ψ o
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
      -> TypeOf (ψ1::Γ) e2 τ ψ2 o
      -> TypeOf ((Not ψ1)::Γ) e3 τ ψ3 o
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
      -> TypeOf (((var x) ::= τ)
                   ::(((var x) ::~ tF) --> ψ0)
                   ::(((var x) ::= tF) --> (Not ψ0))
                   ::Γ) 
                e1
                σ
                ψ1
                o1
      -> TypeOf Γ (Let x e0 e1) σ' ψ1' o1'
| T_Subsume :
    forall τ' τ o' o Γ e ψ ψ',
      TypeOf Γ e τ ψ o
      -> Proves (ψ::Γ) ψ'
      -> Subtype τ τ'
      -> SubObj o o'
      -> TypeOf Γ e τ' ψ' o'.

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

(** *Typechecked Examples *)

Example example1:
    TypeOf [((var X) ::= tTop)]
           (If (Nat? ($ X))
               (Add1 ($ X))
               (#0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example2:
    TypeOf []
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
Proof. Admitted. 

Example example3:
    TypeOf
      [((var Y) ::= tTop)]
      (Let X (Nat? ($ Y))
          (If ($ X)
              ($ Y)
              (# 0)))
      tNat
      TT
      None.
Proof. Admitted. 

Example example4:
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT None))]
           (If (OR (Nat? ($ X)) (Str? ($ X)))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example5:
    TypeOf [((var X) ::= tTop); 
             ((var Y) ::= tTop)]
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example7:
  forall X y,
    TypeOf [((var X) ::= tTop); 
            ((var y) ::= tTop)]
           (If (If (Nat? ($ X)) (Str? ($ y)) #f)
               (Plus ($ X) (StrLen ($ y)))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example8:
    TypeOf []
           (λ X tTop
              (OR (Str? ($ X)) (Nat? ($ X))))
           (tλ X
               tTop (tU tStr tNat)
               ((var X) ::= (tU tStr tNat))
               None)
           TT
           None.
Proof. Admitted. 

Example example9:
    TypeOf [((var X) ::= tTop);
            ((var F) ::= (tλ X (tU tStr tNat) tNat TT None))]
           (If (Let TMP (Nat? ($ X))
                    (If ($ TMP) ($ TMP) (Str? ($ X))))
               (Apply ($ F) ($ X))
               (# 0))
           tNat
           TT
           None.
Proof. Admitted. 

Example example10:
let p := (Id 23) in
    TypeOf [((var p) ::= (tPair tTop tTop))]
           (If (Nat? (Car ($ p)))
               (Add1 (Car ($ p)))
               (# 7))
           tNat
           TT
           None.
Proof. Admitted. 

Example example11:
let p := (Id 23) in
    TypeOf [(var p) ::= (tPair tTop tTop);
            ((var G) ::= (tλ X (tU tNat tNat) tNat TT None))]
           (If (AND (Nat? (Car ($ p))) (Nat? (Cdr ($ p))))
               (Apply ($ G) ($ p))
               (# 42))
           tNat
           TT
           None.
Proof. Admitted. 

Example example12:
    TypeOf []
           (λ X (tPair tTop tTop)
              (Nat? (Car ($ X))))
           (tλ Y
               (tPair tTop tTop) (tPair tTop tTop)
               ((var Y) ::= (tPair tNat tTop))
               None)
           TT
           None.
Proof. Admitted. 

Example example13:
    TypeOf [((var X) ::= tTop) && ((var Y) ::= (tU tNat tStr))]
           (If (AND (Nat? ($ X)) (Str? ($ Y)))
               (Plus ($ X) (StrLen ($ Y)))
               (If (Nat? ($ X))
                   (Plus ($ X) ($ Y))
                   (# 42)))
           tNat
           TT
           None.
Proof. Admitted. 

Example example14:
  forall X y,
    TypeOf [((var X) ::= tTop);
            ((var y) ::= (tPair tTop (tU tNat tStr)))]
           (If (AND (Nat? ($ X)) (Str? (Cdr ($ y))))
               (Plus ($ X) (StrLen ($ y)))
               (If (Nat? ($ X))
                   (Plus ($ X) (Cdr ($ y)))
                   (# 42)))
           tNat
           TT
           None.
Proof. Admitted. 

End LTR.
