#lang racket
(require redex
         "dtr-lang.rkt"
         "dtr-scope.rkt"
         "dtr-subst.rkt"
         "dtr-subtype.rkt"
         "dtr-elim.rkt"
         "utils.rkt")

(provide (all-defined-out))

;; ----------------------------------------------------------
;; Types of primitives
(define-metafunction DTR
  δ-τ : p -> ([x : τ] → τ (ψ ∣ ψ))
  [(δ-τ int?) ([x : ⊤] → Bool ((x ~ Int) ∣ (x ¬ Int)))]
  [(δ-τ bool?) ([x : ⊤] → Bool ((x ~ Bool) ∣ (x ¬ Bool)))]
  [(δ-τ +) ([x : Int] [y : Int] → {i : Int ∣ (= i (x ⊕ y))} (tt ∣ ff))]
  [(δ-τ <=) ([x : Int] [y : Int] → Bool ((x ≤ y) ∣ (> x y)))]
  [(δ-τ [× n]) ([x : Int] → {i : Int ∣ (= i (n ⊗ x))} (tt ∣ ff))])

;; ----------------------------------------------------------
;; Well-formedness under an environment (Δ)
(define-relation DTR
  well-formed ⊆ Δ × any
  [(well-formed Δ any)
   (side-condition (subset? (term (fv any)) (term (fv Δ))))])

;; ----------------------------------------------------------
;; Well-Typed judgement (simplified -- type only, ignores propositions)
(define-judgment-form DTR
  #:mode (wt-τ I I O)
  #:contract (wt-τ Δ e τ)
  [(wt Δ e τ (ψ_+ ∣ ψ_-))
   ----------------
   (wt-τ Δ e τ)])

;; ----------------------------------------------------------
;; Well-Typed judgement
(define-judgment-form DTR
  #:mode (wt I I O O)
  #:contract (wt Δ e τ (ψ ∣ ψ))

  [(where/hidden x ,(variable-not-in (list) (x-sym)))
   ---------------- "T-Int"
   (wt Δ n {x : Int ∣ (= x n)} (tt ∣ ff))]

  [---------------- "T-True"
   (wt Δ #t ♯T (tt ∣ ff))]
  
  [---------------- "T-False"
   (wt Δ #f ♯F (ff ∣ tt))]

  [---------------- "T-Prim"
   (wt Δ p (δ-τ p) (tt ∣ ff))]

  [(where/hidden y ,(variable-not-in (term x) (y-sym)))
   (where τ (lookup x Γ))
   ---------------- "T-Var"
   (wt [Φ Γ Ψ] x {y : τ ∣ (y ⇒ x)} (tt ∣ ff))]

  [; (well-formed Δ (λ ([x : σ] ...) e)) needed? <TODO>
   (where (y ...) ,(variables-not-in (term [Φ Γ Ψ]) (term (x ...))))
   (wt [Φ (ext Γ (y : σ) ...) Ψ] e τ (ψ_+ ∣ ψ_-))
   --------------------------------------------- "T-Lambda"
   (wt [Φ Γ Ψ] (λ ([x : σ] ...) e) ([y : σ] ... → τ (ψ_+ ∣ ψ_-)) (tt ∣ ff))]
  
  [; (well-formed Δ (e_f e_a ...) <TODO>?
   ; does type-of guarantee type has fresh vars in function type? <TODO>
   (wt-τ Δ e_f ([x : σ_f] ... → τ_f (ψ_f+ ∣ ψ_f-)))
   (wt-τ Δ e_a σ) ...
   (subtype Δ σ σ_f) ...
   ;; <hidden-particulars> ∃τ, ψ_+, and  ψ_-
   (where/hidden [Φ Γ Ψ] Δ)
   (where/hidden τ   (elim-ids Φ Γ τ_f  (x ...)))
   (where/hidden ψ_+ (elim-ids Φ Γ ψ_f+ (x ...)))
   (where/hidden ψ_- (elim-ids Φ Γ ψ_f- (x ...)))
   ;; </hidden-particulars> such that
   (proves (ext Δ ψ_f+ (x ~ σ) ...) ψ_+)
   (proves (ext Δ ψ_f- (x ~ σ) ...) ψ_-)
   (subtype (ext Δ (x ~ σ) ...) τ_f τ)
   (well-formed Δ (τ (ψ_+ ∣ ψ_-)))
   ------------------------------ "T-App"
   (wt Δ (e_f e_a ...) τ (ψ_+ ∣ ψ_-))]

  [(wt Δ e_1 τ_1 (ψ_1+ ∣ ψ_1-))
   (wt (ext Δ ψ_1+) e_2 τ_2 (ψ_2+ ∣ ψ_2-))
   (wt (ext Δ ψ_1-) e_3 τ_3 (ψ_3+ ∣ ψ_3-))
   ;; <hidden-particulars> ∃τ
   (where/hidden τ (Un τ_2 τ_3))
   ;; </hidden-particulars> such that
   (subtype Δ τ_2 τ) (subtype Δ τ_3 τ)
   (where ψ_+ ((ψ_1+ ∧ ψ_2+) ∨ (ψ_1- ∧ ψ_3+)))
   (where ψ_- ((ψ_1+ ∧ ψ_2-) ∨ (ψ_1- ∧ ψ_3-)))
   --------------- "T-If"
   (wt Δ (if e_1 e_2 e_3) τ (ψ_+ ∣ ψ_-))]


  [(wt [Φ Γ Ψ] e_1 τ_1 (ψ_1+ ∣ ψ_1-))
   (where Γ_2 ((x : τ_1) · Γ))
   (where Ψ_2 ((IF (x ¬ ♯f) ψ_1+ ψ_1-) · Ψ))
   (wt [Φ Γ_2 Ψ_2] e_2 τ_2 (ψ_2+ ∣ ψ_2-))
   ;; <hidden-particulars> ∃τ, ψ_+, and  ψ_-
   (where/hidden ψ_let (IF (x ¬ ♯f) ψ_1+ ψ_1-))
   (where/hidden τ (elim-ids Φ Γ τ_2 (x)))
   (where/hidden ψ_+ (elim-ids Φ Γ (ψ_let ∧ ψ_2+) (x)))
   (where/hidden ψ_- (elim-ids Φ Γ (ψ_let ∧ ψ_2-) (x)))
   ;; </hidden-particulars> such that
   (proves [Φ Γ_2 (ψ_2+ · Ψ_2)] ψ_+)
   (proves [Φ Γ_2 (ψ_2- · Ψ_2)] ψ_-)
   (subtype [Φ Γ_2 Ψ_2] τ_2 τ)
   (well-formed [Φ Γ Ψ] (τ (ψ_+ ∣ ψ_-)))
   --------------- "T-Let"
   (wt [Φ Γ Ψ] (let (x e_1) e_2) τ (ψ_+ ∣ ψ_-))])

;; judgments for testing

;; types-at
;; tests for exactly 1 particular type
(define-judgment-form DTR
  #:mode (types-at I I)
  #:contract (types-at e τ)
  [(wt-τ mt-Δ e τ_e)
   (subtype mt-Δ τ_e τ)
   (subtype mt-Δ τ τ_e)
   ----------------
   (types-at e τ)])

;; types-at/Δ
;; tests for exactly 1 particular type under Δ
(define-judgment-form DTR
  #:mode (types-at/Δ<: I I I)
  #:contract (types-at/Δ<: Δ e τ)
  [(wt-τ Δ e τ_e)
   (subtype Δ τ_e τ)
   ----------------
   (types-at/Δ<: Δ e τ)])

;; types-under
;; checks it is <: the given type
(define-judgment-form DTR
  #:mode (types-under I I)
  #:contract (types-under e τ)
  [(wt-τ mt-Δ e τ_e)
   (subtype mt-Δ τ_e τ)
   ----------------
   (types-under e τ)])


;; testing macros
;; e is well-typed exactly at type τ
(define-syntax-rule (test*-well-typed e τ)
  (test-true (judgment-holds (types-at e τ))))

;; e is well-typed as a subtype of τ
(define-syntax-rule (test*-well-typed<: e τ)
  (test-true (judgment-holds (types-under e τ))))

;; e is well-typed as a subtype of τ
(define-syntax-rule (test*-well-typed/Δ<: Δ e τ)
  (test-true (judgment-holds (types-at/Δ<: Δ e τ))))

;; e is not ill-typed
(define-syntax-rule (test*-ill-typed e)
  (test-false (judgment-holds (wt-τ mt-Δ e τ))))



(module+ test

  ;; ints
  (test*-well-typed<: 42 Int)
  (test*-well-typed 42 {i : Int ∣ (= i 42)})

  ;; booleans
  (test*-well-typed #t ♯T)
  (test*-well-typed #f ♯F)

  ;; prims
  (test*-well-typed int? ([z : ⊤] → Bool ((z ~ Int) ∣ (z ¬ Int))))
  (test*-well-typed [× 42] ([q : Int] → {i : Int ∣ (= i (42 ⊗ q))} (tt ∣ ff)))

  ;; var
  (test*-ill-typed x)
  (test*-well-typed/Δ<: (Γ: (x : Int)) x Int)

  ;; function
  (test*-well-typed (λ () #t) (→ ♯T (tt ∣ ff)))
  (test*-well-typed (λ ([x : ⊤]) #t) ([y : ⊤] → ♯T (tt ∣ ff)))
  (test*-well-typed (λ ([x : ⊤] [y : ⊤]) #f) ([y : ⊤] [z : ⊤] → ♯F (ff ∣ tt)))
  
  )
