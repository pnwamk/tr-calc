
(* Formalization of the core calculi found in
   "Logical Types for Untyped Languages" 

   -Andrew Kent *)

Set Implicit Arguments.

Require Import LibTactics.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Relations.
Require Import Bool.

Import ListNotations.

Open Scope list_scope.


Section LTR.

Inductive id : Type :=
  Id : nat -> id.

Hint Resolve eq_nat_dec.

Theorem id_eq_dec : forall (x y : id),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eq_dec.

Definition id_eq (x y : id) : bool :=
if id_eq_dec x y then true else false.

Definition X : id := (Id 0).

(* Path Elements (accessors) *)
Inductive acc : Type := car | cdr.

Theorem acc_eq_dec : forall (x y: acc),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve acc_eq_dec.

Definition acc_eq (x y : acc) : bool :=
if acc_eq_dec x y then true else false.

Definition π := list acc.

Hint Resolve list_eq_dec.
Theorem π_eq_dec : forall (x y: π),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve π_eq_dec.

Definition π_eq (x y : π) : bool :=
if π_eq_dec x y then true else false.

(* Objects *)
Inductive object : Type :=
| obj_nil : object
| obj_p   : π -> id -> object. 

Theorem obj_eq_dec : forall (x y: object),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eq_dec. 

Definition obj_eq (x y : object) : bool :=
if obj_eq_dec x y then true else false.

(* Types *)
Inductive τ : Type :=
| τT    : τ    (* Top *)
| τN    : τ    (* Numbers *)
| τt    : τ (* True *)
| τf    : τ  (* False *)
| τU    : list τ -> τ (* union *)
| τλ    : id -> τ -> ψ -> ψ -> object -> τ -> τ (* function *)
| τcons : τ -> τ -> τ (* cons *)

(* Propositions *) (* just use T and add a bool, or take a bool/type pair *)
with ψ : Type :=
| ψτ    : bool -> τ -> π -> id -> ψ
| ψimp  : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψF    : ψ
| ψT    : ψ.

Hint Constructors τ ψ.

Scheme τ_mut_ind := Induction for τ Sort Prop
with ψ_mut_ind := Induction for ψ Sort Prop.

Scheme τ_mut_rec := Induction for τ Sort Set
with ψ_mut_rec := Induction for ψ Sort Set.


(* Common Type Abbreviations *)
Notation τB := (τU [τt ; τf]).
Notation τ_ := (τU nil).

Fixpoint τ_eq_dec (x y : τ) : {x = y} + {x <> y}
with ψ_eq_dec (x y : ψ) : {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
  apply bool_dec.
Defined.
<<<<<<< HEAD
Hint Resolve τ_eq_dec.
Hint Resolve ψ_eq_dec.

Definition τ_eq (x y : τ) : bool :=
if τ_eq_dec x y then true else false.
=======
Hint Resolve type_eq_dec.
Hint Resolve prop_eq_dec.

Definition type_eq (x y : type) : bool :=
if type_eq_dec x y then true else false.
>>>>>>> FETCH_HEAD

Definition ψ_eq (x y : ψ) : bool :=
if ψ_eq_dec x y then true else false.

(* Constant Operations *)
Inductive c_op : Type :=
| op_add1   : c_op
| op_iszero : c_op
| op_isnum  : c_op
| op_isbool : c_op
| op_isproc : c_op
| op_iscons : c_op.

Theorem c_op_eq_dec : forall (x y : c_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve c_op_eq_dec.

Definition c_op_eq (x y : c_op) : bool :=
if c_op_eq_dec x y then true else false.

(* Polymorphic Operations *)
Inductive p_op : Type :=
| op_car : p_op
| op_cdr : p_op.

Theorem p_op_eq_dec : forall (x y : p_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve p_op_eq_dec.

Definition p_op_eq (x y : p_op) : bool :=
if p_op_eq_dec x y then true else false.

(* Primitive Operations *)
Inductive primop : Type := 
| prim_c : c_op -> primop
| prim_p : p_op -> primop.

Theorem primop_eq_dec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eq_dec.

Definition primop_eq (x y : primop) : bool :=
if primop_eq_dec x y then true else false.

(* Expressions *)
Inductive e : Type :=
| e_var    : id -> e
| e_app    : e -> e -> e
| e_abs    : id -> τ -> e -> e
| e_if     : e -> e -> e -> e
| e_primop : primop -> e
| e_true   : e
| e_false  : e
| e_num    : nat -> e
| e_cons   : e -> e -> e
| e_let    : id -> e -> e -> e.

Notation car' := (e_primop (prim_p op_car)).
Notation cdr' := (e_primop (prim_p op_cdr)).
Notation add1' := (e_primop (prim_c op_add1)).
Notation iszero' := (e_primop (prim_c op_iszero)).
Notation isnum' := (e_primop (prim_c op_isnum)).
Notation isbool' := (e_primop (prim_c op_isbool)).
Notation isproc' := (e_primop (prim_c op_isproc)).
Notation iscons' := (e_primop (prim_c op_iscons)).

Theorem e_eq_dec : forall (x y : e),
{x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition e_eq (x y : e) : bool :=
if e_eq_dec x y then true else false.

(* TODO: Do we need Integers to represent numbers? Reals? *)

(* Environments *)
Definition Γ := list ψ.


Definition Γ_eq (x y : Γ) : bool :=
if list_eq_dec ψ_eq_dec x y then true else false.
(* Bookmark *)
Definition c_op_type (c : c_op) : τ :=
match c with
| op_isnum => 
  (τλ X 
         τT 
         (ψτ true τN [] X) 
         (ψτ false τN [] X) 
         obj_nil 
         τB)
| op_isproc =>
  (τλ X 
         τT 
         (ψτ true (τλ X τ_ ψT ψF obj_nil τT) [] X) 
         (ψτ false (τλ X τ_ ψT ψF obj_nil τT) [] X) 
         obj_nil 
         τB)
| op_isbool =>
  (τλ X
         τT
         (ψτ true τB [] X)
         (ψτ false τB [] X)
         obj_nil
         τB)
| op_iscons =>
  (τλ X
         τT
         (ψτ true (τcons τT τT) [] X)
         (ψτ false (τcons τT τT) [] X)
         obj_nil
         τB)
| op_add1 =>
  (τλ X
         τN
         ψT
         ψT
         obj_nil
         τN)
| op_iszero =>
  (τλ X
         τN
         ψT
         ψT
         obj_nil
         τB)
end.

Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y}) 
                       (l:list (set X)) : set X :=
match l with
| nil => nil
| x :: xs => set_union dec x (setU dec xs)
end. 

(* free variables in objects *)
Definition fv_set_o (o : object) : set id :=
match o with
| obj_nil => nil
| obj_p _ x => [x]
end.

(* free variables in types *)
Fixpoint fv_set_t (t : τ) : set id :=
match t with
| τU l =>
  fold_left (fun ids next => 
               set_union id_eq_dec 
                         ids 
                         (fv_set_t next))
            l
            nil
| τλ x t1 p1 p2 o t2 =>
  setU id_eq_dec
       [[x];
        (fv_set_t t1);
        (fv_set_p p1);
        (fv_set_p p2);
        (fv_set_o o);
        (fv_set_t t2)]
| τcons t1 t2 => 
  set_union id_eq_dec
            (fv_set_t t1) 
            (fv_set_t t2)
| _ => nil
end

(* free variables in propositions *)
with fv_set_p (p: ψ) : set id :=
match p with
| ψτ b t pth x => set_union id_eq_dec [x] (fv_set_t t)
| ψimp p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| ψor p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| ψand p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| _ => nil
end.

(* TODO fv tests *)

Definition subst_o (obj:object) (o:object) (x:id) : object :=
match obj with
| obj_nil => obj_nil
| obj_p pth1 z =>
  match id_eq x z, o with
  | true, obj_nil => obj_nil
  | true, obj_p pth2 y => obj_p (pth1 ++ pth2) y
  | false, _ => obj
  end
end.

Inductive sign : Type := pos | neg.

Definition sign_truth (p:sign) : ψ :=
match p with
| pos => ψT
| neg => ψF
end.

Definition sign_flip (p:sign) : sign :=
match p with
| pos => neg
| neg => pos
end.

(* subst+ and - for properties*)
Fixpoint subst_p (s : sign) 
                 (p:ψ) 
                 (o:object) 
                 (x:id) : ψ :=
match p with
| ψτ b t pth1 z =>
  match id_eq x z , set_mem id_eq_dec z (fv_set_t t) with
  | true, _ => 
    match o with
    | obj_nil => (sign_truth s)
    | obj_p pth2 y =>
      ψτ b (subst_t s t o x) (pth1 ++ pth2) y
    end
  | false, false => p
  | false, true => (sign_truth s)
  end
| ψimp P Q => ψimp (subst_p (sign_flip s) P o x) 
                   (subst_p s Q o x)
| ψor P Q => ψor (subst_p s P o x) (subst_p s Q o x)
| ψand P Q => ψand (subst_p s P o x) (subst_p s Q o x)
| _ => p
end

(* type substitution *)
with subst_t (s:sign) 
             (t:τ) 
             (o:object) 
             (x:id) : τ :=
match t with
| τU l => τU (map (fun t' => subst_t s t' o x) l)
| τλ y t1 p1 p2 o2 t2 =>
  if id_eq x y
  then t
  else τλ y
             (subst_t s t1 o x)
             (subst_p s p1 o x)
             (subst_p s p2 o x)
             (subst_o o2 o x)
             (subst_t s t2 o x)
| τcons t1 t2 => τcons (subst_t s t1 o x) 
                         (subst_t s t2 o x)
| _ => t
end.

Inductive SubObj : relation object :=
| SO_Refl : forall x, SubObj x x
| SO_Top  : forall x, SubObj x obj_nil.
Hint Constructors SubObj.

Theorem sub_obj : forall x y,
{SubObj x y} + {~ SubObj x y}.
Proof.
  intros x y.
  destruct (obj_eq_dec x y) as [Heq | Hneq].
  left; crush.
  destruct y. auto.
  right; intro contra.
  inversion contra; crush.
Defined.

(*
Fixpoint contains_bottom (E:Γ) : bool :=
match E with
| nil => false
| p :: ps => 
  match p with
  | T t pth y => if (type_eq t τ_)
                 then true
                 else contains_bottom ps
  | _ => contains_bottom ps
  end
end.

Definition in_Γ (p:prop) (E:Γ) := in_dec prop_eq_dec p E.
Definition ext_Γ (p:prop) (E:Γ) := set_add prop_eq_dec p E.

(* Creates a set of all properties which imply Q in the environment. *)
Fixpoint implicators (E:Γ) (Q:prop) : set prop :=
match E with
| nil => []
| p :: ps => 
  match p with
  | ψimp P Q' => if prop_eq Q Q' 
                 then ext_Γ P (implicators ps Q)
                 else implicators ps Q
  | _ => implicators ps Q
  end
end.


Program Fixpoint proves (E:Γ) (p:prop) {measure (prop_depth p)} : bool :=
(* L-ATOM *)
if in_Γ p E then true else
(* L-τt *)
if prop_eq τt p then true else
(* L-τf *)
if in_Γ τf E then true else
(* L-BOT *)
if contains_bottom E then true else
(* L-IMPE *)
if prove_any (implicators E p) then true else
(* L-ORE *)
if disj_proves 
(* L-ANDE *)

(* 
   OrE
   check all disjuctions, test if adding either side to E proves the prop,
   if both prove the prop, then it's proven because that disjunction is in there

   AndE
   check all conjuctions, test if adding either side to E proves the prop,
   if either prove the prop, then it's proven because that conjunction is in there

*)

with disj_proves (E:Γ) (p:prop) : bool :=
match E with
| nil => false
| q :: qs
  match q with
  | OR r s => if (andb (proves (r :: qs)) (proves (s :: qs)))
              then true
              else disj

with prove_any (E:Γ) (s:set prop) : bool :=
match s with
| nil => false
| p :: ps => if proves E p 
             then true
             else proves_any E ps
end

with subtype (x y: type) : bool := false

with update (x: type) (s:sign) (y:type) (p:path) : type := τ_

with restrict (x y: type) : type := τ_

with remove (x y: type) : type := τ_.
*)

Definition isU (t:τ) : bool :=
match t with
| τU _ => true
| _ => false
end.

Definition share_types (t1 t2:τ) : bool := true.

Inductive Proves : Γ -> ψ -> Prop :=
| L_Atom : 
    forall E p, 
      In p E -> Proves E p
| L_True :
    forall E, 
      Proves E ψT
| L_False :
    forall E p, 
      Proves E ψF ->
      Proves E p
| L_AndI :
    forall E p q, 
      Proves E p ->
      Proves E q ->
      Proves E (ψand p q)
| L_AndE_l :
    forall E p q r,
      (Proves (p :: E) r) ->
      Proves ((ψand p q) :: E) r
| L_AndE_r :
    forall E p q r,
      (Proves (q :: E) r) ->
      Proves ((ψand p q) :: E) r
| L_ImpI :
    forall E p q,
      Proves (p :: E) q ->
      Proves E (ψimp p q)
| L_ImpE :
    forall E p q,
      Proves E p ->
      Proves E (ψimp p q) ->
      Proves E q
| L_OrI_l :
    forall E p q,
      (Proves E p) ->
      Proves E (ψor p q)
| L_OrI_r :
    forall E p q,
      (Proves E q) ->
      Proves E (ψor p q)

| L_OrE :
    forall E p q r,
      Proves (p :: E) r ->
      Proves (q :: E) r ->
      Proves ((ψor p q) :: E) r
| L_Sub :
    forall E t t' x,
      Proves E (ψτ true t [] x) ->
      SubType t t' ->
      Proves E (ψτ true t' [] x)
| L_SubNot :
    forall E t t' x,
      Proves E (ψτ false t' [] x) ->
      SubType t t' ->
      Proves E (ψτ false t [] x)
| L_Bot :
    forall E x p,
      Proves E (ψτ true τ_ [] x) ->
      Proves E p
| L_Update_T :
    forall E t x t' pth pth' t_update,
      Proves E (ψτ true t pth' x) ->
      Proves E (ψτ true t' (pth ++ pth') x) ->
      Update t (true, t') pth t_update ->
      Proves E (ψτ true t_update pth' x)
| L_Update_NT :
    forall E t x t' pth pth' t_update,
      Proves E (ψτ true t pth' x) ->
      Proves E (ψτ false t' (pth ++ pth') x) ->
      Update t (false, t') pth t_update ->
      Proves E (ψτ true t_update pth' x)

(* SubType *)
with SubType : relation τ :=
| S_Refl : forall x, SubType x x
| S_Top : forall x, SubType x τT
| S_UnionSuper : 
    forall t s,
      (exists t', set_In t' s /\ SubType t t') ->
      SubType t (τU s)
| S_UnionSub :
    forall t s,
      (forall t', set_In t' s -> SubType t' t) ->
      SubType (τU s) t
| S_Fun : 
    forall x t1 t2 p1 p2 o t1' t2' p1' p2' o',
      SubType t1   t1' ->
      SubType t2   t2' ->
      Proves  [p1] p1' ->
      Proves  [p2] p2' ->
      SubObj  o    o'  ->
      SubType (τλ x t1 p1 p2 o t2) 
              (τλ x t1' p1' p2' o' t2')
| S_Pair :
    forall t1 t2 t1' t2',
      SubType t1 t1' ->
      SubType t2 t2' ->
      SubType (τcons t1 t2) (τcons t1' t2')

with Update : τ -> (bool * τ) -> π -> τ -> Prop :=
| UP_Car : 
    forall τ1 v pth σ1 updated,
      Update τ1 v pth updated ->
      Update (τcons τ1 σ1) v (pth ++ [car]) (τcons updated σ1)
| UP_Cdr :
    forall t1 b t2 pth t3 σ,
      Update σ ( b , t2 ) pth t3 ->
      Update (τcons t1 σ) (b, t2) (pth ++ [car]) (τcons t3 σ)

| UP_T :
    forall τ σ ε r,
      Restrict τ σ r ->
      Update τ (true, σ) ε r
| UP_NT :
    forall τ σ ε r,
      Remove τ σ r ->
      Update τ (false, σ) ε r

<<<<<<< HEAD

with Restrict : τ -> τ -> τ -> Prop :=
| RES_Bot : 
      forall τ1 σ1,
        share_types τ1 σ1 = false ->
(*    forall τ1 ψ1 ψ1' o1 σ1 ψ2 ψ2' o2,
      ~(exists v, (and (TypeOf [] v τ1 ψ1 ψ1' o1) 
                       (TypeOf [] v σ1 ψ2 ψ2' o2))) -> 
  This is a non positive usage of TypeOf.... *)

      Restrict τ1 σ1 τ_
| RES_U_nil :
    forall σ1,
      Restrict τ_ σ1 τ_
| RES_U_cons :
    forall τ1 τs σ1 r rs,
      Restrict (τU τs) σ1 (τU rs) ->
      Restrict τ1 σ1 r ->
      Restrict (τU (τ1 :: τs)) σ1 (τU (r :: rs))
| RES_Tsub :
    forall τ1 σ1,
      SubType τ1 σ1 ->
      Restrict τ1 σ1 τ1
| RES_other :
    forall τ1 ψ1 ψ1' o1 σ1 ψ2 ψ2' o2,
      share_types t1 σ1 = true ->
      ~SubType τ1 σ1 ->
      isU τ1 = false ->
      Restrict τ1 σ1 σ1
with Remove : τ -> τ -> τ -> Prop :=
| REM_Bot :
    forall τ1 σ1,
      SubType τ1 σ1 ->
      Remove τ1 σ1 τ_
| REM_U_nil :
    forall σ1,
      Remove τ_ σ1 τ_
| REM_U_cons :
    forall τ1 τs σ1 r rs,
      Remove (τU τs) σ1 (τU rs) ->
      Remove τ1 σ1 r ->
      Remove (τU (τ1 :: τs)) σ1 (τU (r :: rs))
| REM_other :
    forall σ1 τ1,
      ~SubType τ1 σ1 ->
      isU τ1 = false ->
      Remove τ1 σ1 τ1
=======
with Restrict : type -> type -> type -> Prop :=
| RES_Bot : 
    forall τ σ v ψ1 ψ1' ψ2 ψ2',
      ~(exists v, (TypeOf [] v τ ψ1 ψ1' o1) /\ 
                   TypeOf [] v σ ψ2 ψ2' o2) ->
      Restrict τ σ t_bottom. 
       
(*

Deep embedding
All of the details (save minimal stuff) are implemented for
the new language

shallow embedding
reusing features of metalanguage in language, i.e. just directly turning
functions into Coq/Racket functions or something

Could try props just directly go into Coq props instead of having a separate
prop system defined.

OTT - turns semantics into Coq code

*)
      Restrict τ σ t_bottom
| RES_U
| RES_Tsub
| RES_Tnsub

with Remove : type -> type -> type -> Prop :=
| rem_triv : forall t1 t2 t3, Remove t1 t2 t3.

Scheme proves_mut := Induction for Proves Sort Prop
with subtype_mut := Induction for SubType Sort Prop.

Theorem false_dec : forall E,
{Proves E FALSE} + {~Proves E FALSE}.
Proof.
  intros E; induction E.
  right; intros contra.
  inversion contra; subst. tryfalse.


Fixpoint proves_dec (E: env) (p : prop) : {Proves E p} + {~Proves E p}
with subtype_dec (x y: type) : {SubType x y} + {~SubType x y}.
Proof.
decide equality.
Defined.


Theorem proves : forall E p,
{Proves E p} + {~Proves E p}.
Proof.
  intros E. induction E as [| q E'].
  intro p. destruct p.

  (* (T t p i) *)
  left. apply L_False.
  right; intros contra. inversion contra; subst.
  tryfalse. 

  Lemma proves_nil_false_false :
    ~ Proves [] FALSE.
    Proof.
      intros contra.
      inversion contra; crush.

inversion H; subst. tryfalse.

  right. intros contra. inversion contra; subst. tryfalse.
  right; intros contra.
  inversion contra; subst. tryfalse.
  inversion H. subst. tryfalse. subst.
 inversion contra; crush.
  eauto.


>>>>>>> FETCH_HEAD

(* Typing Rules *)
with TypeOf : 
  Γ -> e -> τ -> ψ -> ψ -> object -> Prop :=
| Τ_Num : 
    forall E n, 
      TypeOf E (e_num n) τN ψT ψF obj_nil
| T_Const : 
    forall E c,
      TypeOf E 
             (e_primop (prim_c c)) 
             (c_op_type c) 
             ψT 
             ψF 
             obj_nil
| T_True :
    forall E,
      TypeOf E e_true τt ψT ψF obj_nil
| T_False :
    forall E,
      TypeOf E e_false τf ψF ψT obj_nil
| T_Var :
    forall E x t,
      In (ψτ true t [] x) E ->
      TypeOf E 
             (e_var x) 
             t
             (ψτ false τf [] x)
             (ψτ true τf [] x)
             (obj_p [] x)
| T_Abs :
   forall E s x e t pT pF o,
     TypeOf ((ψτ true s [] x) :: E) e t pT pF o ->
     TypeOf E 
            (e_abs x s e) 
            (τλ x s pT pF o t) 
            ψT 
            ψF 
            obj_nil
| T_App :
   forall E e x s pTf pFf t pT pF of o e' pT' pF' o',
     TypeOf E e (τλ x s pTf pFf of t) pT pF o ->
     TypeOf E e' s pT' pF' o' ->
     TypeOf E (e_app e e') 
            (subst_t pos t o' x) 
            (subst_p pos pTf o' x) 
            (subst_p pos pFf o' x) 
            (subst_o of o' x)
| T_If :
   forall E e1 t1 pT1 pF1 o1 e2 t pT2 pF2 o e3 pT3 pF3,
     TypeOf E e1 t1 pT1 pF1 o1 ->
     TypeOf (pT1 :: E) e2 t pT2 pF2 o ->
     TypeOf (pF1 :: E) e3 t pT3 pF3 o ->
     TypeOf E (e_if e1 e2 e3) t (ψor pT2 pT3) (ψor pF2 pF3) o 
| T_Subsume :
   forall E e t pT pF o pT' pF' t' o',
     TypeOf E e t pT pF o ->
     Proves (pT :: E) pT' ->
     Proves (pF :: E) pF' ->
     SubType t t' ->
     SubObj o o' ->
     TypeOf E e t' pT' pF' o'
| T_Cons :
   forall E e1 t1 p1 p1' o1 e2 t2 p2 p2' o2,
     TypeOf E e1 t1 p1 p1' o1 ->
     TypeOf E e2 t2 p2 p2' o2 ->
     TypeOf E (e_cons e1 e2) (τcons t1 t2) ψT ψF obj_nil
| T_Car :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [car] x) o x) ->
     p' = (subst_p pos (ψτ true τf [car] x) o x) ->
     o' = subst_o (obj_p [car] x) o x ->
     TypeOf E (e_app car' e) t1 p p' o'
| T_Cdr :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (τcons t1 t2) p0 p0' o ->
     p = (subst_p pos (ψτ false τf [cdr] x) o x) ->
     p' = (subst_p pos (ψτ true τf [cdr] x) o x) ->
     o' = subst_o (obj_p [cdr] x) o x ->
     TypeOf E (e_app cdr' e) t2 p p' o'
| T_Let :
   forall E e0 t p0 p0' o0 e1 t' p1 p1' o1 x,
   TypeOf E e0 t p0 p0' o0 ->
   TypeOf ((ψτ true t [] x) ::
           (ψimp (ψτ false τf [] x) p0) ::
           (ψimp (ψτ true τf [] x) p0') :: 
           E)
          e1 
          t' 
          p1 
          p1' 
          o1 ->
   TypeOf E 
          (e_let x e0 e1) 
          (subst_t pos t' o0 x)
          (subst_p pos p1 o0 x)
          (subst_p pos p1' o0 x)
          (subst_o o1 o0 x).


Scheme proves_mut := Induction for Proves Sort Prop
with subtype_mut := Induction for SubType Sort Prop.

Theorem false_dec : forall E,
{Proves E τf} + {~Proves E τf}.
Proof.
  intros E; induction E.
  right; intros contra.
  inversion contra; subst. tryfalse.


Fixpoint proves_dec (E: Γ) (p : prop) : {Proves E p} + {~Proves E p}
with subtype_dec (x y: type) : {SubType x y} + {~SubType x y}.
Proof.
  clear provse_d
  eauto.
  
  Check proves_mut.
  eapply proves_mut.
  generalize dependent E.
  
  apply proves_mut.
  induction p; crush.
  generalize dependent y.
  induction x; crush.
Defined.


Theorem proves : forall E p,
{Proves E p} + {~Proves E p}.
Proof.
  intros E. induction E as [| q E'].
  intro p. destruct p.

  (* (T t p i) *)
  left. apply L_False.
  right; intros contra. inversion contra; subst.
  tryfalse. 

  Lemma proves_nil_false_false :
    ~ Proves [] τf.
    Proof.
      intros contra.
      inversion contra; crush.

inversion H; subst. tryfalse.

  right. intros contra. inversion contra; subst. tryfalse.
  right; intros contra.
  inversion contra; subst. tryfalse.
  inversion H. subst. tryfalse. subst.
 inversion contra; crush.
  eauto.





End LTR.