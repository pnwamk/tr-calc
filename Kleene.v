
Require Import LibTactics.

Section KleeneLogic.

Inductive truth := TRUE | FALSE | UNDEF.

Definition And (p q : truth) : truth :=
  match p, q with
    | TRUE, TRUE => TRUE
    | TRUE, UNDEF => UNDEF
    | UNDEF, TRUE => UNDEF
    | UNDEF, UNDEF => UNDEF
    | FALSE, _ => FALSE
    | _, FALSE => FALSE
  end.

Definition Or (p q : truth) : truth :=
  match p, q with
    | TRUE, _ => TRUE
    | _, TRUE => TRUE
    | UNDEF, UNDEF => UNDEF
    | UNDEF, FALSE => UNDEF
    | FALSE, UNDEF => UNDEF
    | FALSE, FALSE => FALSE
  end.

Definition Not (p : truth) : truth :=
  match p with
    | TRUE => FALSE
    | UNDEF => UNDEF
    | FALSE => TRUE
  end.

Notation Imp := (fun (p q : truth) =>
Or (Not p) q).

Infix "-->" := (fun P Q => Imp P Q = TRUE) (at level 30).

Theorem P_True : forall P : truth,
P --> TRUE.
Proof. intros. destruct P; crush. Qed. 

Theorem P_False : forall P : truth,
FALSE --> P.
Proof. intros. destruct P; crush. Qed. 

Theorem P_Conjr : forall P Q R,
(P --> Q)
-> (P --> R)
-> (P --> (And Q R)).
Proof. 
  destruct P; destruct Q; destruct R; crush.
Qed.

Theorem Modus_Ponens : forall P Q,
(P --> Q)
-> P = TRUE
-> Q = TRUE.
Proof. intros. crush. 
       destruct Q; crush. 
Qed.

Theorem Modus_Tollens : forall P Q,
(P --> Q)
-> Q = FALSE
-> P = FALSE.
Proof. intros. crush. 
       destruct P; crush. 
Qed.

Theorem Modus_Tollens_Unk : forall P Q,
(P --> Q)
-> Q = UNDEF
-> (P = FALSE \/ P = UNDEF).
Proof. intros. crush. 
       destruct P; crush. 
Qed.

Theorem ConjIntro : forall P Q,
P = TRUE
-> Q = TRUE
-> (And P Q) = TRUE.
Proof.
  intros. crush.
Qed.

Theorem Simplification : forall P Q,
(And P Q) = TRUE
-> P = TRUE /\ Q = TRUE.
Proof. 
  intros. destruct P; destruct Q; crush.
Qed.

Theorem DisjElim : forall P Q R,
(P --> Q)
-> (R --> Q)
-> (Or P R) = TRUE
-> Q = TRUE.
Proof.
  intros.
  destruct P; destruct Q; destruct R; crush.
Qed.

Theorem DisjSyl : forall P Q,
(Or P Q) = TRUE
-> (Not P) = TRUE
-> Q = TRUE.
Proof.
  intros. destruct P; destruct Q; crush.
Qed.

Theorem HypotheticalSyllogism : forall P Q R,
(P --> Q)
-> (Q --> R)
-> (P --> R).
Proof.
  intros. destruct P; destruct Q; destruct R; crush.
Qed.

Theorem Meta_HypSul : forall P Q

Theorem ConstructiveDilemma : forall P Q R S,
(P --> Q)
-> (R --> S)
-> (Or P R) = TRUE
-> (Or Q S) = TRUE.
Proof.
  intros. destruct P; destruct Q; 
          destruct R; destruct S; crush.
Qed.

Theorem DestructiveDilemma : forall P Q R S,
(P --> Q)
-> (R --> S)
-> (Or (Not Q) (Not S)) = TRUE
-> (Or (Not P) (Not R)) = TRUE.
Proof.
  intros. destruct P; destruct Q; 
          destruct R; destruct S; crush.
Qed.

Theorem Absorption_Invalid : 
  ~(forall P Q, (P --> Q)
                -> (P --> (And P Q))).
Proof.
  intros.  
  intros contra.
  specialize (contra UNDEF TRUE). crush.
Qed.  
(* Absorption _assumes_ (P --> P) which is
   invalid in Kleene Logic *)

Theorem NegationIntro : forall P Q,
(And (Imp P Q) ((Imp P (Not Q)))) = TRUE
-> (Not P) = TRUE.
Proof.
  intros. destruct P; destruct Q; crush.
Qed.

Theorem NegationIntro2 : forall P Q,
(Not P) = TRUE
-> (And (Imp P Q) ((Imp P (Not Q)))) = TRUE.
Proof.
  intros. destruct P; destruct Q; crush.
Qed.

Theorem P_Conjl : forall P Q R,
((P --> R) \/ (Q --> R))
-> ((And P Q) --> R).
Proof. 
  destruct P; destruct Q; destruct R; crush.
Qed.


Theorem AndAssoc : forall P Q R,
(And P (And Q R)) = (And (And P Q) R).
Proof.
  intros. destruct P; destruct Q; destruct R; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem OrAssoc : forall P Q R,
(Or P (Or Q R)) = (Or (Or P Q) R).
Proof.
  intros. destruct P; destruct Q; destruct R; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem AndComm : forall P Q,
(And P Q) = (And Q P).
Proof.
  intros. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem OrComm : forall P Q,
(Or P Q) = (Or Q P).
Proof.
  intros. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem DoubleNeg : forall P,
(Not (Not P)) = P.
Proof.
  intros; destruct P; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem DeMorgan_And : forall P Q,
(Not (And P Q)) = (Or (Not P) (Not Q)).
Proof.
  intros. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem DeMorgan_Or : forall P Q,
(Not (Or P Q)) = (And (Not P) (Not Q)).
Proof.
  intros. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem Transposition_eq : forall P Q,
(Imp P Q) = (Imp (Not Q) (Not P)).
Proof.
  intros. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem MaterialImplication_eq : forall P Q,
(Imp P Q) = (Or (Not P) Q).
Proof.
  intros P Q. destruct P; destruct Q; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)


Theorem Exportation_eq : forall P Q R,
(Imp (And P Q) R) = (Imp P (Imp Q R)).
Proof.
  intros. destruct P; destruct Q; destruct R; crush.
Qed.
(* NOTE!!! Although these are equal in the sense
   that they produce the same values, one does not
   imply the other.

   All UNDEF will lead to UNDEF -> UNDEF, which != TRUE *)



End KleeneLogic.