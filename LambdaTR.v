
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

(* Path Elements *)
Inductive pe : Type := car | cdr.

Theorem pe_eq_dec : forall (x y: pe),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve pe_eq_dec.

Definition pe_eq (x y : pe) : bool :=
if pe_eq_dec x y then true else false.

Definition path := list pe.

Hint Resolve list_eq_dec.
Theorem path_eq_dec : forall (x y: path),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_eq_dec.

Definition path_eq (x y : path) : bool :=
if path_eq_dec x y then true else false.

(* Objects *)
Inductive object : Type :=
| obj_nil  : object
| obj_path : path -> id -> object. 

Theorem obj_eq_dec : forall (x y: object),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_eq_dec. 
Definition obj_var (v:id) : object := (obj_path nil v).

Definition obj_eq (x y : object) : bool :=
if obj_eq_dec x y then true else false.

(* Types *)
Inductive type : Type :=
| t_top : type
| t_num   : type
| t_true  : type
| t_false : type 
| t_union : list type -> type
| t_fun   : id -> type -> prop -> prop -> object -> type -> type
| t_cons  : type -> type -> type 

(* Propositions *) (* just use T and add a bool, or take a bool/type pair *)
with prop : Type :=
| TYPE     : bool -> type -> path -> id -> prop
| IMPL     : prop -> prop -> prop
| OR       : prop -> prop -> prop
| AND      : prop -> prop -> prop
| FALSE    : prop
| TRUE     : prop.

Hint Constructors type prop.

Notation " (t_U) " := (t_union nil).
Notation " (t_U x ) " := (t_union [x]).
Notation " (t_U x , .. , y ) " := (t_union (cons x .. (cons y nil) ..)).


Scheme type_mut_ind := Induction for type Sort Prop
with prop_mut_ind := Induction for prop Sort Prop.

Check type_mut_ind.

Scheme type_mut_rec := Induction for type Sort Set
with prop_mut_rec := Induction for prop Sort Set.


(* Common Type Abbreviations *)
Notation t_bool := (t_U t_true , t_false).
Notation t_bottom := (t_U).

Fixpoint type_eq_dec (x y : type) : {x = y} + {x <> y}
with prop_eq_dec (x y : prop) : {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
  apply bool_dec.
Defined.
Hint Resolve type_eq_dec.
Hint Resolve prop_eq_dec.

Print type_eq_dec.

Definition type_eq (x y : type) : bool :=
if type_eq_dec x y then true else false.

Definition prop_eq (x y : prop) : bool :=
if prop_eq_dec x y then true else false.

Fixpoint prop_depth (p:prop) : nat :=
match p with
| IMPL P Q => 1 + (prop_depth P) + (prop_depth Q)
| OR P Q => 1 + (prop_depth P) + (prop_depth Q)
| AND P Q => 1 + (prop_depth P) + (prop_depth Q)
| _ => 1
end.

(* Constant Operations *)
Inductive constop : Type :=
| op_add1   : constop
| op_iszero : constop
| op_isnum  : constop
| op_isbool : constop
| op_isproc : constop
| op_iscons : constop.

Theorem constop_eq_dec : forall (x y : constop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve constop_eq_dec.

Definition constop_eq (x y : constop) : bool :=
if constop_eq_dec x y then true else false.

(* Polymorphic Operations *)
Inductive polyop : Type :=
| op_car    : polyop
| op_cdr    : polyop.

Theorem polyop_eq_dec : forall (x y : polyop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve polyop_eq_dec.

Definition polyop_eq (x y : polyop) : bool :=
if polyop_eq_dec x y then true else false.

(* Primitive Operations *)
Inductive primop : Type := 
| prim_c : constop -> primop
| prim_p : polyop -> primop.

Theorem primop_eq_dec : forall (x y : primop),
{x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve primop_eq_dec.

Definition primop_eq (x y : primop) : bool :=
if primop_eq_dec x y then true else false.

(* Expressions *)
Inductive expr : Type :=
| e_var    : id -> expr
| e_app    : expr -> expr -> expr
| e_abs    : id -> type -> expr -> expr
| e_if     : expr -> expr -> expr -> expr
| e_primop : primop -> expr
| e_true   : expr
| e_false  : expr
| e_num    : nat -> expr
| e_cons   : expr -> expr -> expr
| e_let    : id -> expr -> expr -> expr.

Notation car' := (e_primop (prim_p op_car)).
Notation cdr' := (e_primop (prim_p op_cdr)).
Notation add1' := (e_primop (prim_c op_add1)).
Notation iszero' := (e_primop (prim_c op_iszero)).
Notation isnum' := (e_primop (prim_c op_isnum)).
Notation isbool' := (e_primop (prim_c op_isbool)).
Notation isproc' := (e_primop (prim_c op_isproc)).
Notation iscons' := (e_primop (prim_c op_iscons)).

Theorem expr_eq_dec : forall (x y : expr),
{x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition expr_eq (x y : expr) : bool :=
if expr_eq_dec x y then true else false.

(* TODO: Do we need Integers to represent numbers? Reals? *)

(* Environments *)
Definition env := list prop.

Definition env_eq (x y : env) : bool :=
if list_eq_dec prop_eq_dec x y then true else false.

Definition constop_type (c : constop) : type :=
match c with
| op_isnum => 
  (t_fun X 
         t_top 
         (TYPE true t_num [] X) 
         (TYPE false t_num [] X) 
         obj_nil 
         t_bool)
| op_isproc =>
  (t_fun X 
         t_top 
         (TYPE true (t_fun X t_bottom TRUE FALSE obj_nil t_top) [] X) 
         (TYPE false (t_fun X t_bottom TRUE FALSE obj_nil t_top) [] X) 
         obj_nil 
         t_bool)
| op_isbool =>
  (t_fun X
         t_top
         (TYPE true t_bool [] X)
         (TYPE false t_bool [] X)
         obj_nil
         t_bool)
| op_iscons =>
  (t_fun X
         t_top
         (TYPE true (t_cons t_top t_top) [] X)
         (TYPE false (t_cons t_top t_top) [] X)
         obj_nil
         t_bool)
| op_add1 =>
  (t_fun X
         t_num
         TRUE
         TRUE
         obj_nil
         t_num)
| op_iszero =>
  (t_fun X
         t_num
         TRUE
         TRUE
         obj_nil
         t_bool)
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
| obj_path _ x => [x]
end.

(* free variables in types *)
Fixpoint fv_set_t (t : type) : set id :=
match t with
| t_union l =>
  fold_left (fun ids next => 
               set_union id_eq_dec 
                         ids 
                         (fv_set_t next))
            l
            nil
| t_fun x t1 p1 p2 o t2 =>
  setU id_eq_dec
       [[x];
        (fv_set_t t1);
        (fv_set_p p1);
        (fv_set_p p2);
        (fv_set_o o);
        (fv_set_t t2)]
| t_cons t1 t2 => 
  set_union id_eq_dec
            (fv_set_t t1) 
            (fv_set_t t2)
| _ => nil
end

(* free variables in propositions *)
with fv_set_p (p: prop) : set id :=
match p with
| TYPE b t pth x => set_union id_eq_dec [x] (fv_set_t t)
| IMPL p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| OR p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| AND p q => set_union id_eq_dec (fv_set_p p) (fv_set_p q)
| _ => nil
end.

(* TODO fv tests *)

Definition subst_o (obj:object) (o:object) (x:id) : object :=
match obj with
| obj_nil => obj_nil
| obj_path pth1 z =>
  match id_eq x z, o with
  | true, obj_nil => obj_nil
  | true, obj_path pth2 y => obj_path (pth1 ++ pth2) y
  | false, _ => obj
  end
end.

Inductive sign : Type := pos | neg.

Definition sign_truth (p:sign) : prop :=
match p with
| pos => TRUE
| neg => FALSE
end.

Definition sign_flip (p:sign) : sign :=
match p with
| pos => neg
| neg => pos
end.

(* subst+ and - for properties*)
Fixpoint subst_p (s : sign) 
                 (p:prop) 
                 (o:object) 
                 (x:id) : prop :=
match p with
| TYPE b t pth1 z =>
  match id_eq x z , set_mem id_eq_dec z (fv_set_t t) with
  | true, _ => 
    match o with
    | obj_nil => (sign_truth s)
    | obj_path pth2 y =>
      TYPE b (subst_t s t o x) (pth1 ++ pth2) y
    end
  | false, false => p
  | false, true => (sign_truth s)
  end
| IMPL P Q => IMPL (subst_p (sign_flip s) P o x) 
                   (subst_p s Q o x)
| OR P Q => OR (subst_p s P o x) (subst_p s Q o x)
| AND P Q => AND (subst_p s P o x) (subst_p s Q o x)
| FALSE => FALSE
| TRUE => TRUE
end

(* type substitution *)
with subst_t (s:sign) 
             (t:type) 
             (o:object) 
             (x:id) : type :=
match t with
| t_union l => t_union (map (fun t' => subst_t s t' o x) l)
| t_fun y t1 p1 p2 o2 t2 =>
  if id_eq x y
  then t
  else t_fun y
             (subst_t s t1 o x)
             (subst_p s p1 o x)
             (subst_p s p2 o x)
             (subst_o o2 o x)
             (subst_t s t2 o x)
| t_cons t1 t2 => t_cons (subst_t s t1 o x) 
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
Fixpoint contains_bottom (E:env) : bool :=
match E with
| nil => false
| p :: ps => 
  match p with
  | T t pth y => if (type_eq t t_bottom)
                 then true
                 else contains_bottom ps
  | _ => contains_bottom ps
  end
end.

Definition in_env (p:prop) (E:env) := in_dec prop_eq_dec p E.
Definition ext_env (p:prop) (E:env) := set_add prop_eq_dec p E.

(* Creates a set of all properties which imply Q in the environment. *)
Fixpoint implicators (E:env) (Q:prop) : set prop :=
match E with
| nil => []
| p :: ps => 
  match p with
  | IMPL P Q' => if prop_eq Q Q' 
                 then ext_env P (implicators ps Q)
                 else implicators ps Q
  | _ => implicators ps Q
  end
end.


Program Fixpoint proves (E:env) (p:prop) {measure (prop_depth p)} : bool :=
(* L-ATOM *)
if in_env p E then true else
(* L-TRUE *)
if prop_eq TRUE p then true else
(* L-FALSE *)
if in_env FALSE E then true else
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

with disj_proves (E:env) (p:prop) : bool :=
match E with
| nil => false
| q :: qs
  match q with
  | OR r s => if (andb (proves (r :: qs)) (proves (s :: qs)))
              then true
              else disj

with prove_any (E:env) (s:set prop) : bool :=
match s with
| nil => false
| p :: ps => if proves E p 
             then true
             else proves_any E ps
end

with subtype (x y: type) : bool := false

with update (x: type) (s:sign) (y:type) (p:path) : type := t_bottom

with restrict (x y: type) : type := t_bottom

with remove (x y: type) : type := t_bottom.
*)


Inductive Proves : env -> prop -> Prop :=
| L_Atom : 
    forall E p, 
      In p E -> Proves E p
| L_True :
    forall E, 
      Proves E TRUE
| L_False :
    forall E p, 
      Proves E FALSE ->
      Proves E p
| L_AndI :
    forall E p q, 
      Proves E p ->
      Proves E q ->
      Proves E (AND p q)
| L_AndE_l :
    forall E p q r,
      (Proves (p :: E) r) ->
      Proves ((AND p q) :: E) r
| L_AndE_r :
    forall E p q r,
      (Proves (q :: E) r) ->
      Proves ((AND p q) :: E) r
| L_ImpI :
    forall E p q,
      Proves (p :: E) q ->
      Proves E (IMPL p q)
| L_ImpE :
    forall E p q,
      Proves E p ->
      Proves E (IMPL p q) ->
      Proves E q
| L_OrI_l :
    forall E p q,
      (Proves E p) ->
      Proves E (OR p q)
| L_OrI_r :
    forall E p q,
      (Proves E q) ->
      Proves E (OR p q)

| L_OrE :
    forall E p q r,
      Proves (p :: E) r ->
      Proves (q :: E) r ->
      Proves ((OR p q) :: E) r
| L_Sub :
    forall E t t' x,
      Proves E (TYPE true t [] x) ->
      SubType t t' ->
      Proves E (TYPE true t' [] x)
| L_SubNot :
    forall E t t' x,
      Proves E (TYPE false t' [] x) ->
      SubType t t' ->
      Proves E (TYPE false t [] x)
| L_Bot :
    forall E x p,
      Proves E (TYPE true t_bottom [] x) ->
      Proves E p
| L_Update_T :
    forall E t x t' pth pth' t_update,
      Proves E (TYPE true t pth' x) ->
      Proves E (TYPE true t' (pth ++ pth') x) ->
      Update t (true, t') pth t_update ->
      Proves E (TYPE true t_update pth' x)
| L_Update_NT :
    forall E t x t' pth pth' t_update,
      Proves E (TYPE true t pth' x) ->
      Proves E (TYPE false t' (pth ++ pth') x) ->
      Update t (false, t') pth t_update ->
      Proves E (TYPE true t_update pth' x)

(* SubType *)
with SubType : relation type :=
| S_Refl : forall x, SubType x x
| S_Top : forall x, SubType x t_top
| S_UnionSuper : 
    forall t s,
      (exists t', set_In t' s /\ SubType t t') ->
      SubType t (t_union s)
| S_UnionSub :
    forall t s,
      (forall t', set_In t' s -> SubType t' t) ->
      SubType (t_union s) t
| S_Fun : 
    forall x t1 t2 p1 p2 o t1' t2' p1' p2' o',
      SubType t1   t1' ->
      SubType t2   t2' ->
      Proves  [p1] p1' ->
      Proves  [p2] p2' ->
      SubObj  o    o'  ->
      SubType (t_fun x t1 p1 p2 o t2) 
              (t_fun x t1' p1' p2' o' t2')
| S_Pair :
    forall t1 t2 t1' t2',
      SubType t1 t1' ->
      SubType t2 t2' ->
      SubType (t_cons t1 t2) (t_cons t1' t2')

with Update : type -> (bool * type) -> path -> type -> Prop :=
| UP_Car : 
    forall τ ν pth σ updated,
      Update τ ν pth updated ->
      Update (t_cons τ σ) ν (pth ++ [car]) (t_cons updated σ)
| UP_Cdr :
    forall t1 b t2 pth t3 σ,
      Update σ ( b , t2 ) pth t3 ->
      Update (t_cons t1 σ) (b, t2) (pth ++ [car]) (t_cons t3 σ)

| UP_T :
    forall τ σ ε restricted,
      Restrict τ σ restricted ->
      Update τ (true, σ) ε restricted
| UP_NT :
    forall τ σ ε restricted,
      Remove τ σ restricted ->
      Update τ (false, σ) ε restricted


with Restrict : type -> type -> type -> Prop :=
| res_triv : forall t1 t2 t3, Restrict t1 t2 t3

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



(* Typing Rules *)
Inductive TypeOf : 
  env -> expr -> type -> prop -> prop -> object -> Prop :=
| T_Num : 
    forall E n, 
      TypeOf E (e_num n) t_num TRUE FALSE obj_nil
| T_Const : 
    forall E c,
      TypeOf E 
             (e_primop (prim_c c)) 
             (constop_type c) 
             TRUE 
             FALSE 
             obj_nil
| T_True :
    forall E,
      TypeOf E e_true t_true TRUE FALSE obj_nil
| T_False :
    forall E,
      TypeOf E e_false t_false FALSE TRUE obj_nil
| T_Var :
    forall E x t,
      In (T t [] x) E ->
      TypeOf E 
             (e_var x) 
             t 
             (NT t_false [] x) 
             (T t_false [] x) 
             (obj_var x)
| T_Abs :
   forall E s x e t pT pF o,
     TypeOf ((T s [] x) :: E) e t pT pF o ->
     TypeOf E 
            (e_abs x s e) 
            (t_fun x s pT pF o t) 
            TRUE 
            FALSE 
            obj_nil
| T_App :
   forall E e x s pTf pFf t pT pF of o e' pT' pF' o',
     TypeOf E e (t_fun x s pTf pFf of t) pT pF o ->
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
     TypeOf E (e_if e1 e2 e3) t (OR pT2 pT3) (OR pF2 pF3) o 
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
     TypeOf E (e_cons e1 e2) (t_cons t1 t2) TRUE FALSE obj_nil
| T_Car :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (t_cons t1 t2) p0 p0' o ->
     p = (subst_p pos (NT t_false [car] x) o x) ->
     p' = (subst_p pos (T t_false [car] x) o x) ->
     o' = subst_o (obj_path [car] x) o x ->
     TypeOf E (e_app car' e) t1 p p' o'
| T_Cdr :
   forall E e t1 t2 p0 p0' o o' p p' x,
     TypeOf E e (t_cons t1 t2) p0 p0' o ->
     p = (subst_p pos (NT t_false [cdr] x) o x) ->
     p' = (subst_p pos (T t_false [cdr] x) o x) ->
     o' = subst_o (obj_path [cdr] x) o x ->
     TypeOf E (e_app cdr' e) t2 p p' o'
| T_Let :
   forall E e0 t p0 p0' o0 e1 t' p1 p1' o1 x,
   TypeOf E e0 t p0 p0' o0 ->
   TypeOf ((T t [] x) ::
           (IMPL (NT t_false [] x) p0) ::
           (IMPL (T t_false [] x) p0') :: 
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


End LTR.