#lang racket

(require redex rackunit fme)

(define-language λDTR
  [n   ::= integer]
  [b   ::= boolean]
  [x   ::= variable-not-otherwise-mentioned]
  [e   ::= x (e e) (λ (x : τ) e) (if e e e) c #t #f n]
  [c   ::= plus mult leq num? bool? proc?]
  [L   ::= n x (n * L) (L + L)]
  [o   ::= null x L]
  [φ   ::= (L <= L)]
  [Φ   ::= [LI ...]]
  [τ   ::= Any Int ([x : τ] where ψ) True False (U τ ...) (λ ([x : τ] ψ^ o) : τ)]
  [ψ   ::= (b τ x) SLI (ψ AND ψ) (ψ OR ψ) TT FF]
  [ψ^   ::= ψ UNK ERR]
  [Γ   ::= [ψ ...]])


(define-metafunction λDTR
  negb : b -> b
  [(negb #t) #f]
  [(negb #f) #t])


(define-metafunction λDTR
  NOT : ψ -> ψ
  [(NOT (b_1 τ_1 x_1)) ((negb b_1) τ_1 x_1)]
  [(NOT Φ_1) Φ_1] ; TODO
  [(NOT (ψ_1 AND ψ_2)) ((NOT ψ_1) OR (NOT ψ_2))]
  [(NOT (ψ_1 OR ψ_2)) ((NOT ψ_1) AND (NOT ψ_2))]
  [(NOT TT) FF]
<<<<<<< HEAD
  [(NOT FF) TT]
  [(NOT UNK) UNK])


(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves E p)
  ; L-Atom
  [------------------- "L-Atom"
   (proves [ψ_1 ... (b_1 τ_1 x_1) ψ_2 ...] (b_1 τ_1 x_1))]
=======
  [(NOT FF) TT])

(define-metafunction λDTR
  property : ψ^ -> ψ
  [(property ψ_1) ψ_1]
  [(property UNK) TT]
  [(property ERR) FF])

(define-metafunction λDTR
  negation : ψ^ -> ψ
  [(negation ψ_1) (NOT ψ_1)]
  [(negation UNK) TT]
  [(negation ERR) FF])

(define-judgment-form λDTR
  #:mode (not-equal I I)
  #:contract (not-equal ψ ψ)
  [------------------- "Neq"
   (not-equal e_!_1 e_!_1)])

(define-judgment-form λDTR
  #:mode (not-in I I)
  #:contract (not-in ψ Γ)
  [------------------- "Not-In-Empty"
   (not-in [ ] ψ_1)]
  [(not-equal ψ_1 ψ_2)
   (not-in [ψ_3 ...] ψ_1)
   ------------------- "Not-In-Cons"
   (not-in [ψ_2 ψ_3 ...] ψ_1)])

(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  ; L-Atom
  [------------------- "L-Atom"
   (proves [ψ_1 ... ψ_2 ψ_3 ...] ψ_2)]
  ; L-True
  [------------------- "L-True"
   (proves Γ_1 TT)]
  ; L-False
  [------------------- "L-False"
   (proves [ψ_1 ... FF ψ_2 ...] ψ_3)]
  ; L-Bot
  [------------------- "L-Bot"
   (proves [ψ_1 ... (#t (U) x_1) ψ_2 ...] ψ_3)]
  ; L-AndI
  [(proves Γ_1 ψ_1)
   (proves Γ_1 ψ_2)
   ------------------- "L-AndI"
   (proves Γ_1 (ψ_1 AND ψ_2))]
  ; L-AndE
  [(proves [ψ_1 ... ψ_2 ... ψ_3 ψ_4] ψ_5)
   ------------------- "L-AndE"
   (proves [ψ_1 ... (ψ_3 AND ψ_4) ψ_2 ...] ψ_5)]
  ; L-OrI-lhs
  [(proves Γ_1 ψ_1)
   ------------------- "L-OrI-lhs"
   (proves Γ_1 (ψ_1 OR ψ_2))]
  ; L-OrI-rhs
  [(proves Γ_1 ψ_2)
   ------------------- "L-OrI-rhs"
   (proves Γ_1 (ψ_1 OR ψ_2))]
  ; L-OrE
  [(proves [ψ_1 ... ψ_2 ... ψ_3] ψ_5)
   (proves [ψ_1 ... ψ_2 ... ψ_4] ψ_5)
   ------------------- "L-OrE"
   (proves [ψ_1 ... (ψ_3 OR ψ_4) ψ_2 ...] ψ_5)]
  ; L-Sub
  [(subtype τ_1 τ_2)
   ------------------- "L-Sub"
   (proves [ψ_1 ... (#t τ_1 x_1) ψ_2 ...] (#t τ_2 x_1))]
  ; L-SubNot
  [(subtype τ_2 τ_1)
   ------------------- "L-SubNot"
   (proves [ψ_1 ... (#f τ_1 x_1) ψ_2 ...] (#f τ_2 x_1))]
  ; L-Update-lhs
  [(not-in (#t (update τ_1 b_1 τ_2) x_1) [ψ_1 ... (#t τ_1 x_1) ψ_2 ... (b_1 τ_2 x_1) ψ_3 ...])
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (b_1 τ_1 x_1) (#t (update τ_1 b_1 τ_2) x_1)] ψ_4)
   ------------------- "L-Update-lhs"
  (proves [ψ_1 ... (#t τ_1 x_1) ψ_2 ... (b_1 τ_2 x_1) ψ_3 ...] ψ_4)]
  ; L-Update-rhs
  [(not-in (#t (update τ_1 b_1 τ_2) x_1) [ψ_1 ...  (b_1 τ_2 x_1) ψ_2 ... (#t τ_1 x_1) ψ_3 ...])
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (b_1 τ_1 x_1) (#t (update τ_1 b_1 τ_2) x_1)] ψ_4)
   ------------------- "L-Update-rhs"
  (proves [ψ_1 ...  (b_1 τ_2 x_1) ψ_2 ... (#t τ_1 x_1) ψ_3 ...] ψ_4)])


(define-judgment-form λDTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [------------------- "S-Refl"
   (subtype τ_1 τ_1)]
  [(subtype τ_1 τ_2) ...
   ------------------- "S-UnionSub"
   (subtype (U τ_1 ...) τ_2)]
  [(subtype τ_1 τ_3)
   ------------------- "S-UnionSuper"
   (subtype τ_1 (U τ_2 ... τ_3 τ_4 ...))])

(check-true (judgment-holds (subtype Int Int)))
(check-true (judgment-holds (subtype (U) Int)))
(check-true (judgment-holds (subtype Int (U Int False))))
(check-true (judgment-holds (subtype (U True False) (U Int False True))))
(check-true (judgment-holds (subtype Int Int)))


(define-metafunction λDTR
  update : τ b τ -> τ
  [(update τ_1 b_1 τ_2) τ_1]) ;TODO

; To-Do's
; 1. How do we make sure update doesn't infinite loop?
;    e.g. we don't keep updating Any_x with (~ Int_x)
;
; 2. How can we define reduced propositions?
;    e.g. (~P OR Q) AND P   ==>   P AND Q
;


