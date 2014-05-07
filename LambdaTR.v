
(* Formalization of the core calculi found in
   "Logical Types for Untyped Languages" 

   -Andrew Kent *)

Require Import TRLogic.

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

Theorem id_eqdec : forall (x y : id),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve id_eqdec.

Definition id_eq (x y : id) : bool :=
if id_eqdec x y then true else false.

Definition X : id := (Id 0).

(* Path Elements (accessors) *)
Inductive acc : Type := car | cdr.

Theorem acc_eqdec : forall (x y: acc),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve acc_eqdec.

Definition acc_eq (x y : acc) : bool :=
if acc_eqdec x y then true else false.

Definition π := list acc.

Hint Resolve list_eq_dec.
Theorem π_eqdec : forall (x y: π),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve π_eqdec.

Definition π_eq (x y : π) : bool :=
if π_eqdec x y then true else false.

(* Objects *)
Inductive obj : Type :=
| objnil : obj
| objπ   : π -> id -> obj.

Theorem obj_eqdec : forall (x y: obj),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eqdec. 

Definition obj_eq (x y : obj) : bool :=
if obj_eqdec x y then true else false.

(* Types *)
Inductive τ : Type :=
| τT    : τ    (* Top *)
| τN    : τ    (* Numbers *)
| τt    : τ (* True *)
| τf    : τ  (* False *)
| τU    : list τ -> τ (* union *)
| τλ    : id -> τ -> ψ -> ψ -> obj -> τ -> τ (* function *)
| τcons : τ -> τ -> τ (* cons *)

with ψ : Type :=
| ψfact : fact -> ψ
| ψimpl : ψ -> ψ -> ψ
| ψor   : ψ -> ψ -> ψ
| ψand  : ψ -> ψ -> ψ
| ψff   : ψ
| ψtt   : ψ

with fact : Type :=
| fτ  : bool -> τ -> obj -> fact.

Hint Resolve bool_dec.

Fixpoint τ_eqdec (x y : τ) : {x=y}+{x<>y}
with ψ_eqdec (x y : ψ) : {x=y}+{x<>y}
with fact_eqdec (x y : fact) : {x=y}+{x<>y}.
Proof.
  decide equality.
  decide equality.
  decide equality.
Defined.

Hint Constructors τ ψ fact.
Hint Resolve τ_eqdec ψ_eqdec fact_eqdec.

(* Common Type Abbreviations *)
Notation τB := (τU [τt ; τf]).
Notation τ_ := (τU nil).

Hint Resolve ψ_eqdec.

Hint Resolve bool_dec.

Definition τ_eq (x y : τ) : bool :=
if τ_eqdec x y then true else false.

Definition fact_eq (x y : τ) : bool :=
if τ_eqdec x y then true else false.

Definition ψ_eq (x y : ψ) : bool :=
if ψ_eqdec x y then true else false.

Inductive θ : Type :=
| θfact : fact -> θ
| θor   : θ -> θ -> θ
| θand  : θ -> θ -> θ
| θff   : θ
| θtt   : θ.

Definition negate_fact (f:fact) : fact :=
match f with
| fτ b t o => fτ (negb b) t o
end.

Fixpoint ψtoθ (prop:ψ) : θ :=
match prop with
| ψfact f   => θfact f
| ψimpl p q => θor (notψtoθ p) (ψtoθ q)
| ψor   p q => θor (ψtoθ p) (ψtoθ q)
| ψand  p q => θand (ψtoθ p) (ψtoθ q)
| ψff       => θff
| ψtt       => θtt
end

with notψtoθ (prop:ψ) : θ :=
match prop with
| ψfact f   => θfact (negate_fact f)
| ψimpl p q => θand (ψtoθ p) (notψtoθ q)
| ψor   p q => θand (notψtoθ p) (notψtoθ q)
| ψand  p q => θor (notψtoθ p) (notψtoθ q)
| ψff       => θtt
| ψtt       => θff
end.

Definition ψstoθs (ps:list ψ) : list θ :=
map ψtoθ ps.

Inductive Γ : Type :=
| Γempty : Γ
| Γfalse : Γ -> Γ
| Γfact  : fact -> Γ -> Γ
| Γor    : Γ -> Γ -> Γ.

Fixpoint Γapp (Γ1 Γ2:Γ) : Γ :=
match Γ1 with
| Γempty => Γ2
| Γfalse rest => Γfalse (Γapp rest Γ2)
| Γfact f rest => Γfact f (Γapp rest Γ2)
| Γor lhs rhs => Γor (Γapp lhs Γ2) (Γapp rhs Γ2)
end.

Fixpoint θtoΓ (prop:θ) : Γ :=
match prop with
| θfact f  => Γfact f Γempty
| θor p q  => Γor (θtoΓ p) (θtoΓ q)
| θand p q => Γapp (θtoΓ p) (θtoΓ q)
| θff      => Γfalse Γempty
| θtt      => Γempty
end.

Fixpoint buildΓ' (props:list θ) : Γ :=
match props with
| nil => Γempty
| p :: ps => Γapp (θtoΓ p) (buildΓ' ps)
end.

Definition buildΓ (ps:list ψ) := buildΓ' (ψstoθs ps).

Inductive Proves : Γ -> fact -> Prop :=
| P_Atom :
    forall f E,
      Proves (Γfact f E) f
| P_False :
    forall f E,
      Proves (Γfalse E) f
| P_Rest : 
    forall f f' E,
      Proves E f' ->
      Proves (Γfact f E) f'
| P_Or :
    forall E1 E2 f,
      Proves E1 f ->
      Proves E2 f ->
      Proves (Γor E1 E2) f.
Hint Constructors Proves.

Theorem Proves_dec : forall E f,
{Proves E f} + {~Proves E f}.
Proof.
  induction E.
  intros f. right.
  intros contra; inversion contra.

  intros f. left. apply P_False.

  intros f'.
  destruct (fact_eqdec f f'); subst.
  left. apply P_Atom.
  destruct (IHE f') as [Htrue | Hfalse].
  left. apply P_Rest. assumption.
  right. intros contra. inversion contra; subst. tryfalse. 
  tryfalse. 

  intros f.
  destruct (IHE1 f); destruct (IHE2 f).
  left. apply P_Or; auto.
  right. intros contra; inversion contra; subst. tryfalse.
  right. intros contra; inversion contra; subst. tryfalse.
  right. intros contra; inversion contra; subst. tryfalse.
Qed.

(* 
Proves Note!

Although negation is included in this logic in some sense - deriving
contradictions via the negation of facts is not.

This behavior can be specifically included in expandΓ if desired.

*)

(* Option used so None can represent a false environment (i.e. ff is proven) *)
Definition fact_in (f : fact) (fs : option (list fact)) : bool := 
match fs with
| None => true
| Some facts =>
  if in_dec fact_eqdec f facts then true else false
end.

Fixpoint expProves' (f:fact) (facts:list fact) (E:Γ) 
         (expΓ: list fact -> option (list fact)) : bool :=
match E with
| Γempty => fact_in f (expΓ facts)
| Γfalse rest => true
| Γfact f rest => expProves' f (f :: facts) rest expΓ
| Γor lhs rhs => andb (expProves' f facts lhs expΓ) (expProves' f facts rhs expΓ)
end.

Definition expProves (f:fact) (E:Γ) 
           (expΓ: list fact -> option (list fact)): bool :=
expProves' f nil E expΓ.


(* Constant Operations *)
Inductive c_op : Type :=
| op_add1   : c_op
| op_iszero : c_op
| op_isnum  : c_op
| op_isbool : c_op
| op_isproc : c_op
| op_iscons : c_op.

Theorem c_op_eqdec : forall (x y : c_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve c_op_eqdec.

Definition c_op_eq (x y : c_op) : bool :=
if c_op_eqdec x y then true else false.

(* Polymorphic Operations *)
Inductive p_op : Type :=
| op_car : p_op
| op_cdr : p_op.

Theorem p_op_eqdec : forall (x y : p_op),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve p_op_eqdec.

Definition p_op_eq (x y : p_op) : bool :=
if p_op_eqdec x y then true else false.

(* Primitive Operations *)
Inductive primop : Type := 
| prim_c : c_op -> primop
| prim_p : p_op -> primop.

Theorem primop_eqdec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eqdec.

Definition primop_eq (x y : primop) : bool :=
if primop_eqdec x y then true else false.

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

Theorem e_eqdec : forall (x y : e),
{x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition e_eq (x y : e) : bool :=
if e_eqdec x y then true else false.

(* TODO: Do we need Integers to represent numbers? Reals? *)

(* Environments *)
Definition env := list ψ.

Theorem env_eqdec : forall (x y : env),
{x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

Definition env_eq (x y : env) : bool :=
if env_eqdec x y then true else false.

Definition c_op_type (c : c_op) : τ :=
match c with
| op_isnum => 
  (τλ X 
         τT 
         (ψfact (fτ true τN (objπ [] X))) 
         (ψfact (fτ false τN (objπ [] X))) 
         objnil 
         τB)
| op_isproc =>
  (τλ X 
         τT 
         (ψfact (fτ true (τλ X τ_ ψtt ψff objnil τT) (objπ [] X))) 
         (ψfact (fτ false (τλ X τ_ ψtt ψff objnil τT) (objπ [] X))) 
         objnil 
         τB)
| op_isbool =>
  (τλ X
         τT
         (ψfact (fτ true τB (objπ [] X)))
         (ψfact (fτ false τB (objπ [] X)))
         objnil
         τB)
| op_iscons =>
  (τλ X
         τT
         (ψfact (fτ true (τcons τT τT) (objπ [] X)))
         (ψfact (fτ false (τcons τT τT) (objπ [] X)))
         objnil
         τB)
| op_add1 =>
  (τλ X
      τN
      ψtt
      ψtt
      objnil
      τN)
| op_iszero =>
  (τλ X
      τN
      ψtt
      ψtt
      objnil
      τB)
end.

Fixpoint setU {X:Type} (dec : forall x y : X, {x=y} + {x<>y}) 
                       (l:list (set X)) : set X :=
match l with
| nil => nil
| x :: xs => set_union dec x (setU dec xs)
end. 

(* free variables in objects *)
Definition fv_set_o (o : obj) : set id :=
match o with
| objnil => nil
| objπ _ x => [x]
end.

(* free variables in types *)

Fixpoint fv_set_t (t : τ) : set id :=
match t with
| τU l =>
  fold_left (fun ids next => 
               set_union id_eqdec 
                         ids 
                         (fv_set_t next))
            l
            nil
| τλ x t1 p1 p2 o t2 =>
  setU id_eqdec
       [[x];
        (fv_set_t t1);
        (fv_set_p p1);
        (fv_set_p p2);
        (fv_set_o o);
        (fv_set_t t2)]
| τcons t1 t2 => 
  set_union id_eqdec
            (fv_set_t t1) 
            (fv_set_t t2)
| _ => nil
end

(* free variables in propositions *)
with fv_set_p (p: ψ) : set id :=
let fv_set_fact := ((fix fv_set_fact (f:fact) : set id:= 
     match f with
     | fτ b t o  => 
       set_union id_eqdec (fv_set_o o) (fv_set_t t)
     end)) in
match p with
| ψfact f => (fv_set_fact f)
| ψimpl p q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
| ψor p q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
| ψand p q => set_union id_eqdec (fv_set_p p) (fv_set_p q)
| _ => nil
end.


Definition subst_o (o1 o2:obj) (x:id) : obj :=
match o1 with
| objnil => objnil
| objπ pth1 z =>
  match id_eq x z, o2 with
  | true, objnil => objnil
  | true, objπ pth2 y => objπ (pth1 ++ pth2) y
  | false, _ => o1
  end
end.

Inductive sign : Type := pos | neg.

Definition sign_truth (p:sign) : ψ :=
match p with
| pos => ψtt
| neg => ψff
end.

Definition sign_flip (p:sign) : sign :=
match p with
| pos => neg
| neg => pos
end.

(* subst+ and - for properties*)
Fixpoint subst_p (s : sign) 
                 (p:ψ) 
                 (o:obj) 
                 (x:id) : ψ :=
match p with
| ψfact (fτ b t (objπ pth1 z)) =>
  match id_eq x z , set_mem id_eqdec z (fv_set_t t) with
  | true, _ => 
    match o with
    | objnil => (sign_truth s)
    | objπ pth2 y =>
      ψfact (fτ b (subst_t s t o x) (objπ (pth1 ++ pth2) y))
    end
  | false, false => p
  | false, true => (sign_truth s)
  end
| ψimpl P Q => ψimpl (subst_p (sign_flip s) P o x) 
                   (subst_p s Q o x)
| ψor P Q => ψor (subst_p s P o x) (subst_p s Q o x)
| ψand P Q => ψand (subst_p s P o x) (subst_p s Q o x)
| _ => p
end

(* type substitution *)
with subst_t (s:sign) 
             (t:τ) 
             (o:obj) 
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

Inductive SubObj : relation obj :=
| SO_Refl : forall x, SubObj x x
| SO_Top  : forall x, SubObj x objnil.
Hint Constructors SubObj.

Theorem sub_obj : forall x y,
{SubObj x y} + {~ SubObj x y}.
Proof.
  intros x y.
  destruct (obj_eqdec x y) as [Heq | Hneq].
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

Definition in_Γ (p:prop) (E:Γ) := in_dec prop_eqdec p E.
Definition ext_Γ (p:prop) (E:Γ) := set_add prop_eqdec p E.

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

(* BOOKMARK

  I've merged the logic and lambda calc up till this point, just about
  to look at how the SubType relation works with the above new defs.
 *)

(* SubType *)
Inductive SubType : relation τ :=
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


(* Typing Rules *)
with TypeOf : 
  Γ -> e -> τ -> ψ -> ψ -> obj -> Prop :=
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