(* begin hide *)
Require Import LibTactics.
Require Import List.
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

Inductive id : Type :=
  Id : nat -> id.

Inductive step : Type := car | cdr.
Hint Constructors step.

Definition path : Type := list step.

Inductive object : Type :=
| obj : path -> id -> object.
Hint Constructors object.

Notation var := (obj []).

(** Types and propositions: *)
Inductive type : Type :=
| tTop  : type
| tBot  : type
| tNat  : type
| tStr  : type
| tT    : type
| tF    : type
| tU    : type -> type -> type
| tCons : type -> type -> type
| tλ    : id -> type -> type -> prop -> opt object -> type

with prop : Type :=
| Is    : object -> type -> prop
| IsNot : object -> type -> prop
| And   : prop -> prop -> prop
| Or    : prop -> prop -> prop
| TT    : prop
| FF    : prop
| Unk   : prop.
Hint Constructors type prop.

Fixpoint Not (p : prop) : prop :=
  match p with
    | Is o t => IsNot o t
    | IsNot o t => Is o t
    | And p q => Or (Not p) (Not q)
    | Or p q => And (Not p) (Not q)
    | TT => FF
    | FF => TT
    | Unk => Unk
  end.

Hint Resolve eq_nat_dec.

Notation tBool := (tU tT tF).

Infix "::=" := Is (at level 30, right associativity).
Infix "::~" := IsNot (at level 30, right associativity).
Notation "P '&&' Q" := (And P Q) (at level 40, left associativity).
Notation "P '||' Q" := (Or P Q) (at level 50, left associativity).
Notation "P '-->' Q" := (Or (Not P) Q) (at level 90).

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
with prop_eqdec (x y : prop) : {x=y}+{x<>y}.
Proof.
repeat  decide equality.
repeat  decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec.


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
    | o ::= t => set_union id_eqdec (fv_set_o (Some o)) (fv_set_t t)
    | o ::~ t => set_union id_eqdec (fv_set_o (Some o)) (fv_set_t t)
    | p && q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p || q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | _ => nil
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
Fixpoint subst_p
         (p:prop)
         (opto:opt object)
         (x:id) : prop :=
  match p with
    | (obj pth1 z) ::= t =>
      match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
        | left _, _ =>
          match opto with
            | None => TT
            | Some (obj pth2 y) =>
              Is (obj (pth1 ++ pth2) y) (subst_t t opto x)
          end
        | right _, false => p
        | right _, true => TT
      end
    | (obj pth1 z) ::~ t =>
      match id_eqdec x z , set_mem id_eqdec z (fv_set_t t) with
        | left _, _ =>
          match opto with
            | None => TT
            | Some (obj pth2 y) =>
              IsNot (obj (pth1 ++ pth2) y) (subst_t t opto x)
          end
        | right _, false => p
        | right _, true => TT
      end
    | P || Q => (subst_p P opto x) || (subst_p Q opto x)
    | P && Q => (subst_p P opto x) && (subst_p Q opto x)
    | _ => p
  end

with subst_t
             (t:type)
             (opto:opt object)
             (x:id) : type :=
  match t with
    | tU lhs rhs => tU (subst_t lhs opto x) (subst_t rhs opto x)
    | tλ y t1 t2 p1 opto2 =>
      if id_eqdec x y
      then t
      else tλ y
                (subst_t t1 opto x)
                 (subst_t t2 opto x)
                (subst_p p1 opto x)
                (subst_o opto2 opto x)
    | tCons t1 t2 => tCons (subst_t t1 opto x)
                           (subst_t t2 opto x)
    | _ => t
  end.

(** All uses of subst_p' and subst_t' "in the wild" call the positive case, from
which the negative case may then be called.  *) 

(** A few helpers to reason about subtyping: *)

Inductive isUnion : type -> Prop :=
| isU : forall t1 t2, isUnion (tU t1 t2).

Fixpoint typesize (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      S (plus (typesize t1) (typesize t2))
    | tλ x t1 t2 _ _ => S (plus (typesize t1) (typesize t2))
    | tCons t1 t2 => S (plus (typesize t1) (typesize t2))
    | _ => 1
  end.

Program Fixpoint common_subtype (type1 type2:type)
        {measure (plus (typesize type1) (typesize type2))} : bool :=
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

(* NOTE: Our lookup models an environment where every variable in scope
has some type present (even if its only tTop). *)

(** * λTR Core Relations 
   Logic, TypeOf, Subtyping, etc... *)

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** ** Proves Relation *)
(** "Proves P Q" means proposition "P implies Q" is tautilogical. *)

Inductive In : relation prop :=
| In_Refl :
    forall P,
      In P P
| In_And_lhs :
    forall P Q R,
      In P Q
      -> In P (Q && R)
| In_And_rhs :
    forall P Q R,
      In P R
      -> In P (Q && R).
Hint Constructors In.

Lemma In_dec : forall Q P,
{In P Q} + {~In P Q}.
Proof.
  intros Q.
  induction Q; intros.
  destruct (prop_eqdec P (o ::= t)); subst.
  left. auto.
  right; intros contra; inversion contra; tryfalse.
  destruct (prop_eqdec P (o ::~ t)); subst.
  left. auto. 
  right; intros contra; inversion contra; tryfalse.
  specialize (IHQ1 P). specialize (IHQ2 P).
  destruct IHQ1; destruct IHQ2.
  left; apply In_And_lhs; auto.
  left; apply In_And_lhs; auto.
  left; apply In_And_rhs; auto.
  destruct (prop_eqdec P (Q1 && Q2)); subst.
  left; auto.
  right; intros contra; inversion contra; subst.
  tryfalse. tryfalse. tryfalse.
  destruct (prop_eqdec P (Q1 || Q2)); subst.
  left. auto.
  right; intros contra; inversion contra; tryfalse.
  destruct (prop_eqdec P TT); subst.
  left. auto.
  right; intros contra; inversion contra; tryfalse.
  destruct (prop_eqdec P FF); subst.
  left. auto.
  right; intros contra; inversion contra; tryfalse.
  destruct (prop_eqdec P Unk); subst.
  left. auto.
  right; intros contra; inversion contra; tryfalse.
Qed.  
Hint Resolve In_dec.

(* TODO *)
Inductive Proves : relation prop :=
| P_Atom :
    forall P Q,
      In Q P
      -> Proves P Q
| P_True :
    forall P,
      Proves P TT
| P_False :
    forall P,
      Proves FF P
| P_Contra :
    forall P Q,
      Proves (P && (Not P)) Q
| P_Conjr :
    forall P Q R,
      Proves P Q 
      -> Proves P R 
      -> Proves P (Q && R)
| P_Add_lhs :
    forall P Q R,
      Proves P Q
      -> Proves P (Q || R)
| P_Add_rhs :
    forall P Q R,
      Proves P R
      -> Proves P (Q || R)
| P_DisjElim :
    forall P Q R,
      Proves P R
      -> Proves Q R
      -> Proves (P || Q) R
| P_Conjl_lhs :
    forall P Q R,
      Proves P R
      -> Proves (P && Q) R
| P_Conjl_rhs :
    forall P Q R,
      Proves Q R
      -> Proves (P && Q) R
| P_DisjSyl :
    forall P Q,
      Proves ((Not P) && (P || Q)) Q
| P_HypSyl :
    forall P Q R,
      Proves P Q
      -> Proves Q R
      -> Proves P R
| P_Sub :
    forall τ σ ox P,
      Proves P (ox ::= τ)
      -> SubType τ σ
      -> Proves P (ox ::= σ)
| P_SubNot :
    forall P τ σ ox,
      Proves P (ox ::~ σ)
      -> SubType τ σ
      -> Proves P (ox ::~ τ)
| P_RestrictBot :
    forall P ox τ σ,
      Proves P (ox ::= τ)
      -> Proves P (ox ::= σ)
      -> common_subtype τ σ = false
      -> Proves P (ox ::= tBot)
| P_RemoveBot :
    forall P τ σ ox,
      Proves P (ox ::= τ)
      -> Proves P (ox ::~ σ)
      -> SubType τ σ
      -> Proves P (ox ::= tBot)
| P_Bot : 
    forall P Q ox,
      Proves P (ox ::= tBot) 
      -> Proves P Q
| P_PairUpdate :
    forall P π x τ σ,
    Proves P ((obj (π ++ [car]) x) ::= τ)
    -> Proves P ((obj (π ++ [cdr]) x) ::= σ)
    -> Proves P ((obj π x) ::= (tCons τ σ))
| P_UnionNeg_lhs :
    forall P o τ τ',
      Proves P (o ::~ τ')
      -> Proves P (o ::= (tU τ τ'))
      -> Proves P (o ::= τ)
| P_UnionNeg_rhs :
    forall P o τ τ',
      Proves P (o ::~ τ')
      -> Proves P (o ::= (tU τ' τ))
      -> Proves P (o ::= τ)

(** SubType *)

with SubType : relation type :=
| S_Refl : 
    forall τ, SubType τ τ
| S_Top : 
    forall τ, SubType τ tTop
| S_Bot : 
    forall τ, SubType tBot τ
| S_UnionSuper_lhs :
    forall τ σ1 σ2,
      SubType τ σ1
      -> SubType τ (tU σ1 σ2)
| S_UnionSuper_rhs :
    forall τ σ1 σ2,
      SubType τ σ2
      -> SubType τ (tU σ1 σ2)
| S_UnionSub :
    forall τ1 τ2 σ,
      SubType τ1 σ
      -> SubType τ2 σ
      -> SubType (tU τ1 τ2) σ
| S_Abs :
    forall x y τ τ' σ σ' ψ ψ' o o',
      SubType (subst_t τ (Some (var y)) x) τ'
      -> SubType σ' (subst_t σ (Some (var y)) x) 
      -> Proves (subst_p ψ (Some (var y)) x) ψ'
      -> SubObj (subst_o o (Some (var y)) x) o'
      -> SubType (tλ x σ τ ψ o)
                 (tλ y σ' τ' ψ' o')
| S_Cons :
    forall τ1 σ1 τ2 σ2,
      SubType τ1 τ2
      -> SubType σ1 σ2
      -> SubType (tCons τ1 σ1) (tCons τ2 σ2).

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

Lemma And_comm : forall P Q R,
Proves P (Q && R)
-> Proves P (R && Q).
Proof with crush.
  intros P Q R H.
  apply P_Conjr.
  apply P_Simpl_rhs in H...
  apply P_Simpl_lhs in H...
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


Fixpoint in_type (t U : type) : bool :=
if type_eqdec t U then true else
match U with
  | tU t1 t2 => orb (in_type t t1) (in_type t t2)
  | _ => false
end.

Lemma in_type_Subtype : forall t2 t1,
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


Lemma T_If' :
    forall τ τ1 τ2 τ3 o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf (Γ && ψ1) e2 τ2 ψ2 o
      -> TypeOf (Γ && (Not ψ1)) e3 τ3 ψ3 o
      -> τ = join τ2 τ3
      -> TypeOf Γ (If e1 e2 e3) τ ((ψ1 && ψ2) || ((Not ψ1) && ψ3)) o.
Proof with crush.
  intros.
  forwards*: (join_super_lhs τ1 τ2).
  forwards*: (join_super_rhs τ1 τ2).
  eapply T_If... eassumption. 
  eapply (T_Subsume _ τ2)... eassumption. crush.
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
          first [solve[eapply T_If' with (o := None); bamcis' False] |
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
exact X.
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
  Admitted.

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
  bamcis. Admitted.

Example bamcis_OR1:
  TypeOf ((var X) ::= tTop)
         (OR (Nat? ($ X)) (Str? ($ X)))
         tBool
         ((var X) ::= (tU tNat tStr))
         None.
Proof.
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
Grab Existential Variables.
exact X. exact X.
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
exact X. exact X. exact X.
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
exact TT. exact X.
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
  eapply T_If...
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
