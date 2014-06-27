(* begin hide *)
Require Import LibTactics.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.
Require Import Coq.Program.Wf.
Require Import String.
Require Import Classical.

Import ListNotations.
Open Scope list_scope.
(* end hide *)

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
| Atom : fact -> prop
| Not  : prop -> prop
| And  : prop -> prop -> prop
| Or   : prop -> prop -> prop
| Imp  : prop -> prop -> prop
| TT   : prop
| FF   : prop
| Unk  : prop

with fact : Type :=
| istype   : object -> type -> fact.
Hint Constructors type prop fact.

Fixpoint typesize (t:type) : nat :=
  match t with
    | tU t1 t2 =>
      S (plus (typesize t1) (typesize t2))
    | tλ x t1 t2 _ _ => S (plus (typesize t1) (typesize t2))
    | tCons t1 t2 => S (plus (typesize t1) (typesize t2))
    | _ => 1
  end.

Fixpoint factsize (f:fact) : nat :=
  match f with
    | istype o t => typesize t
  end.

Hint Resolve eq_nat_dec.

Notation tBool := (tU tT tF).

Infix "::=" := (fun o t => Atom (istype o t)) 
                 (at level 30, right associativity).
Notation "! P" := (Not P) (at level 20, right associativity).
Infix "::~" := (fun o t => Not (Atom (istype o t)))
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
with prop_eqdec (x y : prop) : {x=y}+{x<>y}
with fact_eqdec (x y : fact) : {x=y}+{x<>y}.
Proof.
repeat decide equality.
repeat decide equality.
repeat decide equality.
Defined.
Hint Resolve type_eqdec prop_eqdec fact_eqdec.


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
    | ! q => fv_set_p q
    | p && q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p || q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
    | p --> q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
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

Definition truth (b:bool) : prop :=
if b then TT else FF.

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
    | Not P  => subst_p' (negb b) P opto x
    | P || Q => (subst_p' b P opto x) || (subst_p' b Q opto x)
    | P && Q => (subst_p' b P opto x) && (subst_p' b Q opto x)
    | P --> Q => (subst_p' (negb b) P opto x) --> (subst_p' b Q opto x)
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

(** A few helpers to reason about subtyping: *)

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

Hypothesis Unknown : nat -> Prop.
Hypothesis IsType  : object -> type -> Prop. 

Program Fixpoint fact_denote (f:fact) 
        {measure (factsize f)}: Prop :=
match f with
| istype o (tU t1 t2) =>
  fact_denote (istype o t1) \/ fact_denote (istype o t2)
| istype o tBot => False
| istype o t => IsType o t
end.
Solve Obligations using crush.

Fixpoint prop_denote' (P:prop) (n:nat) : (prod Prop nat) :=
match P with
| Atom f => ((fact_denote f), n)
| Not p    => let (p', n') := (prop_denote' p n) in
              (~ p', n')
| And p q  => let (lhs, ln) := (prop_denote' p n) in
              let (rhs, rn) := (prop_denote' q ln) in
              (lhs /\ rhs, rn)
| Or  p q  => let (lhs, ln) := (prop_denote' p n) in
              let (rhs, rn) := (prop_denote' q ln) in
              (lhs \/ rhs, rn)
| Imp p q  => let (lhs, ln) := (prop_denote' p n) in
              let (rhs, rn) := (prop_denote' q ln) in
              (lhs -> rhs, rn)
| TT       => (True, n)
| FF       => (False, n)
| Unk      => ((Unknown n), (S n))
end.

Definition Holds := fun p => fst (prop_denote' p 0).

(** ** Sub-Object Relation*)
Inductive SubObj : relation (opt object) :=
| SO_Refl : forall x, SubObj x x
| SO_Top : forall x, SubObj x None.

(** SubType *)
Inductive SubType : relation type :=
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
      -> Holds ((subst_p ψ (Some (var y)) x) --> ψ')
      -> SubObj (subst_o o (Some (var y)) x) o'
      -> SubType (tλ x σ τ ψ o)
                 (tλ y σ' τ' ψ' o')
| S_Cons :
    forall τ1 σ1 τ2 σ2,
      SubType τ1 τ2
      -> SubType σ1 σ2
      -> SubType (tCons τ1 σ1) (tCons τ2 σ2).

Axiom P_Sub : 
  forall o τ σ,
    Holds (o ::= τ)
    -> SubType τ σ
    -> Holds (o ::= σ).

Axiom P_SubNot : 
  forall o τ σ,
    Holds (o ::~ σ)
    -> SubType τ σ
    -> Holds (o ::~ τ).

Axiom P_Restrict : 
  forall o τ σ,
    Holds (o ::= τ)
    -> Holds (o ::= σ)
    -> common_subtype τ σ = false
    -> False.

Axiom P_Remove : 
  forall o τ σ,
    Holds (o ::= τ)
    -> Holds (o ::~ σ)
    -> SubType τ σ
    -> False.
                
Axiom P_ConsUpdate :
    forall π x τ σ,
    Holds ((obj (π ++ [car]) x) ::= τ)
    -> Holds ((obj (π ++ [cdr]) x) ::= σ)
    -> Holds ((obj π x) ::= (tCons τ σ)).


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
      Holds (Γ --> ((var x) ::= τ))
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
      TypeOf Γ e (tλ x σ τ fψ fo) ψ o
      -> TypeOf Γ e' σ ψ' o'
      -> (subst_t τ o' x) = τ''
      -> (subst_p fψ o' x) = ψf''
      -> (subst_o fo o' x) = o''
      -> TypeOf Γ (Apply e e') τ'' ψf'' o''
| T_If :
    forall τ τ1 o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ1 ψ1 o1
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
    forall σ' τ σ o o0 o1 Γ e0 ψ0 e1 ψ1 x ψ1',
      TypeOf Γ e0 τ ψ0 o0
      -> TypeOf (Γ && ((var x) ::= τ)
                   && (((var x) ::~ tF) --> ψ0)
                   && (((var x) ::= tF) --> (Not ψ0))) 
                e1
                σ
                ψ1
                o1
      -> (subst_t σ o0 x) = σ'
      -> (subst_p ψ1 o0 x) = ψ1'
      -> (subst_o o1 o0 x) = o
      -> TypeOf Γ (Let x e0 e1) σ' ψ1' o
| T_SuperType :
    forall τ' τ o Γ e ψ,
      TypeOf Γ e τ ψ o
      -> SubType τ τ'
      -> TypeOf Γ e τ' ψ o
| T_SuperObj :
    forall o' o τ Γ e ψ,
      TypeOf Γ e τ ψ o
      -> SubObj o o'
      -> TypeOf Γ e τ ψ o'
| T_Implied :
    forall ψ' ψ τ o Γ e,
      TypeOf Γ e τ ψ o
      -> Holds ((Γ && ψ) --> ψ')
      -> TypeOf Γ e τ ψ' o.

(** * Proof Helpers *)

(** * Proof Helpers/Lemmas and Automation *)


(** Universally valid tactics (if these go wrong, we're already in a bad
    proof state is the idea) *)
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

Lemma subst_tBool : forall opto x,
subst_t tBool opto x = tBool.
Proof. crush. Qed.
  Hint Rewrite subst_tBool.


Definition is_tλ (t:type) : bool :=
  match t with
    | tλ _ _ _ _ _ => true
    | _ => false
  end.

Lemma subst_p_Atom_istype : forall x y opto t,
x <> y
-> is_tλ t = false
-> set_mem id_eqdec x (fv_set_t t) = false
-> subst_p (Atom (istype (var x) t)) opto y 
   = Atom (istype (var x) t).
Proof.
  intros. unfold subst_p.
  destruct t; crush; destruct (id_eqdec y x); crush.
Qed.

Lemma T_Implied_andΓ : forall Γ τ ψ o e,
TypeOf Γ e τ ψ o
-> Holds ((Γ && ψ) --> (Γ && ψ))
-> TypeOf Γ e τ (Γ && ψ) o.
Proof.
  intros.
  eapply T_Implied. eassumption. auto.
Qed.

Fixpoint find_types P o : list type := 
  match P with
    | Atom (istype o' t) => if obj_eqdec o o' then [t] else nil
    | (P1 && P2) =>  
      (find_types P1 o) ++ (find_types P2 o)
      | _ => nil
  end.
Hint Unfold find_types.


Fixpoint remove_unknowns (p:prop) : prop :=
  match p with
    | P && Q => 
      if (prop_eqdec P Unk)
      then remove_unknowns Q
      else if (prop_eqdec Q Unk)
      then remove_unknowns P
      else (remove_unknowns P) && (remove_unknowns Q)
    | P || Q => (remove_unknowns P) || (remove_unknowns Q)
    | _ => p
  end.


Ltac var_guess Γ o types k_tac :=
  match types with
    | ?t :: ?ts =>
      solve[(eapply (T_Implied ((remove_unknowns Γ) && (o ::~ tF)) (o ::~ tF) t None Γ _);
              eapply (T_Var Γ);
              k_tac) |
             (eapply (T_Implied ((remove_unknowns Γ) && (o ::~ tF)) (o ::~ tF) t (Some _) Γ _);
              eapply (T_Var Γ);
              k_tac) |
             var_guess o ts k_tac]

    | nil => fail
  end.



Lemma T_If_TypeOpts :
    forall τ τ1 τ2 τ3 o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3,
      TypeOf Γ e1 τ1 ψ1 o1
      -> TypeOf (Γ && ψ1) e2 τ2 ψ2 o
      -> TypeOf (Γ && (Not ψ1)) e3 τ3 ψ3 o
      -> ((τ2 = τ3 /\ τ = τ2) 
          \/ (SubType τ2 τ3 /\ τ = τ3) 
          \/ (SubType τ3 τ2 /\ τ = τ2)
          \/ (τ = (tU τ2 τ3)))
      -> TypeOf Γ (If e1 e2 e3) τ ((ψ1 && ψ2) || ((Not ψ1) && ψ3)) o.
Proof.
  intros τ τ1 τ2 τ3 o o1 Γ e1 ψ1 e2 ψ2 e3 ψ3 HTe1 HTe2 HTe3 Hdisj.
  destruct Hdisj as [[H23eq Hteq] | [[Hsub Heq] | Heq]]; crush.
  eapply T_If. eassumption. auto. auto.
  eapply T_If. eassumption. apply (T_SuperType τ3 τ2); auto. auto.
  eapply T_If. eassumption. auto. apply (T_SuperType τ2 τ3); auto.
  eapply T_If. eassumption.
  apply (T_SuperType (tU τ2 τ3) τ2); auto.
  apply (T_SuperType (tU τ2 τ3) τ3); auto.
Qed.
(** Individual TypeOf cases err on the side of
    including Γ in their proposition. *)
Ltac bamcis' subsuming :=
  crush;
     (match goal with
        | [ |- ?lhs = ?rhs] => 
          solve [reflexivity |
                crush |
                compute; crush]
        | [ |- Holds _] => compute; tauto
          (* T_Nat - Γ instead of TT *)
        | |- TypeOf ?Γ (# ?n) _ _ _ => 
          (eapply (T_Implied (remove_unknowns Γ) TT tNat None Γ (# n));
           eapply T_Nat;
           bamcis' False)
          (* T_Str - Γ instead of TT *)
        | |- TypeOf ?Γ (Str ?s) _ _ _ => 
          (eapply (T_Implied (remove_unknowns Γ) TT tStr None Γ (Str s));
           eapply T_Str;
           bamcis' False)
          (* T_Const - Γ instead of TT *)
        | |- TypeOf Γ (eOp ?c) _ _ _ => 
          (eapply (T_Implied (remove_unknowns Γ) TT _ None Γ (eOp c));
           eapply T_Const;
           bamcis' False)
          (* T_True - Γ instead of TT *)
        | |- TypeOf ?Γ #t _ _ _ => 
          (eapply (T_Implied (remove_unknowns Γ) TT tTrue None Γ #t);
           eapply T_True;
           bamcis' False)
          (* T_False - !Γ instead of FF *)
        | |- TypeOf ?Γ #f _ _ _ => 
          (eapply (T_Implied ((! (remove_unknowns Γ))) FF tFalse None Γ #f);
           eapply T_False;
           bamcis' False)
          (* T_Var *)
        | |- TypeOf ?Γ ($ ?X) _ _ _ =>
          solve [(let types_exp := constr:(find_types Γ (var X)) in
                  let types := eval simpl in types_exp in
                    (var_guess Γ (var X) types ltac:(bamcis' False))) |
                 eapply T_Var; bamcis' False]
          (* T_Abs - Γ instead of TT *)
        | |- TypeOf ?Γ (λ ?x ?σ _) _ _ _ => 
          (eapply (T_Implied (remove_unknowns Γ) TT (tλ x σ _ _ _) None Γ _);
           eapply T_Abs;
           bamcis' False)
          (* T_App *)
        | |- TypeOf ?Γ (Apply ?e ?e') ?τ ?ψ _ =>
          (eapply (T_Implied ((remove_unknowns Γ) && ψ) ψ τ None Γ _);
           eapply T_App;
           bamcis' False)
        (* T_If *)
        | |- TypeOf ?Γ (If _ _ _) ?τ ?ψ _ => (* T_If_Opts *)
          (eapply (T_Implied ((remove_unknowns Γ) && ψ) ψ τ None Γ _);
           eapply T_If_TypeOpts;
           bamcis' False)
        | |- TypeOf _ (Let _ _ _) _ _ _ =>
          solve [(eapply T_Let with (o := None); bamcis' False) | 
                 (eapply T_Let; bamcis' False)]
        | |- TypeOf _ _ ?t _ _ =>
          match subsuming with
          | True => fail
          | False => 
            solve[(eapply T_SuperObj; bamcis' True) |
                  (eapply T_SuperType; bamcis' True) |
                  (eapply T_Implied_andΓ; bamcis' True) |
                  (eapply T_SuperObj; eapply T_SuperType; bamcis' True) |
                  (eapply T_Implied_andΓ; eapply T_SuperObj; bamcis' True) |
                  (eapply T_SuperType; eapply T_Implied_andΓ; bamcis' True) |
                  (eapply T_SuperType; eapply T_Implied_andΓ; 
                   eapply T_Implied; bamcis' True) |
                  (eapply T_SuperObj; eapply T_Implied; bamcis' True) |
                  (eapply T_SuperType; eapply T_Implied; bamcis' True) |
                  (eapply T_SuperType; eapply T_Implied; 
                   eapply T_SuperObj; bamcis' True)]
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
Holds (((((var X) ::= tNat) || ((var X) ::= tStr)) 
          && TT 
          && (! ((var X) ::= tNat)) 
          && TT) -->
       ((var X) ::= tStr)).
Proof. bamcis. Qed.

(* Disjunctive Syllogism Test *)
Example bamcis_disjsyl2 : 
Holds (((((var X) ::= tNat) || ((var X) ::= tTop)) 
          && (((var X) ::= tNat) || ((var X) ::= tStr))
          && ((var X) ::~ tNat) 
          && TT) -->
       ((var X) ::= tStr)).
Proof. bamcis. Qed. 

(* Disjunctive Syllogism Test *)
Example bamcis_disjsyl3 : 
Holds (((((var X) ::= tNat) || ((var X) ::= tStr))  
          && (((var X) ::= tNat) || ((var X) ::= tTop))
          && ((var X) ::~ tNat) 
          && TT) -->
       ((var X) ::= tStr)).
Proof. bamcis. Qed.

(* Union not-rhs Test *)
Example bamcis_unionnot1 : 
Holds ((((var X) ::= (tU tStr tNat)) 
          && TT 
          && ((var X) ::~ tNat) 
          && TT) -->
       ((var X) ::= tStr)).
Proof. bamcis. Qed.

(* Union not-lhs Test *)
Example bamcis_unionnot2 : 
  Holds ((((var X) ::= (tU tNat tStr)) 
            && TT 
            && ((var X) ::~ tNat) 
            && TT)
           -->
           ((var X) ::= tStr)).
Proof. bamcis. Qed. 

(* Union not-lhs Test w/ other type value present*)
Example bamcis_unionnot3 : 
  Holds ((((var X) ::= tTop) 
            && ((var X) ::= (tU tNat tStr)) 
            && TT 
            && ((var X) ::~ tNat))
         -->
         ((var X) ::= tStr)).
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

Example bamcis_If:
TypeOf
     (Atom (istype (var X) tTop) 
      && (Atom (istype (var TMP) tBool))
      && (!Atom (istype (var TMP) tF) --> Atom (istype (var X) tNat)) 
      && (Atom (istype (var TMP) tF) --> !Atom (istype (var X) tNat)))
     (If ($ TMP) ($ TMP) (Str? ($ X))) tBool
     (Atom (istype (var X) (tU tNat tStr))) None.
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
Proof.
  eapply T_Let with (o := None).
  bamcis.
  bamcis.
  bamcis.
  bamcis.
  bamcis.
Grab Existential Variables.
auto. auto.
Qed.

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
  eapply T_Implied.
  eapply T_Let...
  bamcis.
Grab Existential Variables.
auto.
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
  eapply T_SuperObj.
  eapply T_If_joinImp with (τ1 := tBool).
  eapply T_Let.
  bamcis. bamcis. bamcis. crush. compute.
  eapply (T_App tBool).
  bamcis. bamcis. crush. crush. crush.
  eapply T_If_joinImp.
  crush. bamcis.  crush.
  eapply (T_SuperObj None).
  bamcis. crush.
  bamcis.
  bamcis.
  bamcis.
  bamcis.
  bamcis.
  (* BOOKMARK *)
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
