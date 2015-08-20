#lang racket
(require redex
         "lang.rkt"
         "alpha-eqv.rkt"
         "test-utils.rkt")

(provide (all-defined-out))

(define-metafunction DTR
  rem-id : (x ...) x ... -> (x ...)
  [(rem-id (x ... y z ...) y_0 ... y y_1 ...)
   (rem-id (x ... z ...) y_0 ... y y_1 ...)]
  [(rem-id (x ...) y ...) (x ...)])

;; --------------------------------------------------------------
;; substitution
(define-metafunction DTR
  subst : any ([x ↦ o] ...) -> any
  [(subst any ()) any]
  ;; subst variable
  [(subst y (any_1 ... [y ↦ o] any_2 ...)) o]
  ;; non-subst variable
  [(subst x (any ...)) x]
  ;; λ
  [(subst (λ ([x : τ] ...) e) (any ...))
   (λ ([z : (subst τ (any ...))] ...)
     (subst (subst-raw e [(x ↦ z) ...]) (any ...)))
   (where (z ...) (fresh-vars (e (any ...)) (x ...)))]
  ;; let
  [(subst (let (x e_x) e) (any ...))
   (let (z (subst e_x (any ...)))
     (subst (subst-raw e [(x ↦ z)]) (any ...)))
   (where z (fresh-var (e (any ...)) x))]
  ;; function type
  [(subst ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (any ...))
   ([z : (subst σ (any ...))] ...
    → (subst (subst-raw τ [(x ↦ z) ...]) (any ...))
    ((subst (subst-raw ψ_+ [(x ↦ z) ...]) (any ...))
     ∣
     (subst (subst-raw ψ_- (x ↦ z) ...) (any ...))))
   (where (z ...) (fresh-vars (τ ψ_+ ψ_- (any ...)) (x ...)))]
  ;; refinement type
  [(subst {x : τ ∣ ψ} (any ...))
   {z : (subst τ (any ...))
      ∣ (subst (subst-raw ψ ([x ↦ z])) (any ...))}
   (where z (fresh-var (ψ (any ...)) x))]
  ;; syntactic list
  [(subst (any ...) (any_subst ...))
   ((subst any (any_subst ...)) ...)]
  ;; other (ignore)
  [(subst any (any_subst ...)) any])

;; very 'raw' function, does substitution w/o respecting
;; scope.
;; Should *only* be used when ids being substituted in
;; are *guaranteed to be fresh*
(define-metafunction DTR
  subst-raw : any ((x ↦ o) ...) -> any
  [(subst-raw y (any_1 ... (y ↦ o) any_2 ...)) o]
  [(subst-raw (any_1 ...) (any ...))
   ((subst-raw any_1 (any ...)) ...)]
  [(subst-raw any_1 (any ...)) any_1])




;; *********************************************************
;; substitution tests
(module+ test
  ;; expressions
  (test*-α= (subst x ([x ↦ y])) y)
  (test*-α= (subst x ([z ↦ y])) x)
  (test*-α= (subst (x y z) ([x ↦ y])) (y y z))
  (test*-α= (subst (x y z) ([x ↦ y] [z ↦ y])) (y y y))
  (test*-α= (subst (+ x y) ([x ↦ a] [y ↦ b])) (+ a b))
  (test*-α= (subst (if x y z) ([x ↦ y])) (if y y z))
  (test*-α= (subst (let (x y) z) ([x ↦ y])) (let (q y) z))
  (test*-α= (subst (let (f x) (f z)) ([x ↦ y])) (let (g y) (g z)))
  (test*-α= (subst (λ ([g : Int]) (f g)) ([f ↦ g]))
            (λ ([x : Int]) (g x)))
  ;; types
  (test*-α= (subst ⊤ ([x ↦ y])) ⊤)
  (test*-α= (subst Int ([x ↦ y])) Int)
  (test*-α= (subst ♯t ([x ↦ y])) ♯t)
  (test*-α= (subst ♯f ([x ↦ y])) ♯f)
  (test*-α= (subst (I ∪ ♯f) ([x ↦ y])) (I ∪ ♯f))
  
  (test*-α= (subst {x : Int ∣ (x ≤ x)} ([x ↦ y]))
            {a : Int ∣ (a ≤ a)})
  (test*-α= (subst {x : Int ∣ (x ≤ y)} ([y ↦ x]))
            {a : Int ∣ (a ≤ x)})
  (test*-α= (subst {y : {a : Int ∣ (x ≤ a)} ∣ (y ≤ x)} ([x ↦ y]))
            {z : {a : Int ∣ (y ≤ a)} ∣ (z ≤ y)})

  ;; propositions
  (test*-α= (subst (x ~ Int) ([x ↦ y])) (y ~ Int))
  (test*-α= (subst (x ¬ Int) ([x ↦ y])) (y ¬ Int))

  )


;; *******************************************************************
;; fv tests
#;(module+ test
  ;; Expressions
  (test*-set-equal (fv 42) ())
  (test*-set-equal (fv int?) ())
  (test*-set-equal (fv #t) ())
  (test*-set-equal (fv x) (x))
  (test*-set-equal (fv (x a)) (x a))
  ;;;; lambdas
  (test*-set-equal (fv (λ ([a : Int]) (x a))) (x))
  (test*-set-equal (fv (λ ([y : Int])
                         (λ ([x : Int])
                           (x a))))
                   (a))
  ;;;; app
  (test*-set-equal (fv ((λ ([x : Int]) (x a))
                        z)) (z a))
  ;;;; if
  (test*-set-equal (fv (if (f x)
                        42
                        z)) (f x z))
  ;;;; let
  (test*-set-equal (fv (let (x 42)
                         (+ x x)))
                   ())
  (test*-set-equal (fv (let (x y)
                         (<= x x)))
                   (y))
  (test*-set-equal (fv (let (x x)
                         (+ x x)))
                   (x))
  (test*-set-equal (fv (let (x 42)
                         (+ x y)))
                   (y))
  ;; Types
  (test*-set-equal (fv Int) ())
  (test*-set-equal (fv ♯T) ())
  (test*-set-equal (fv ⊤) ())
  (test*-set-equal (fv ⊥) ())
  (test*-set-equal (fv (U Int ♯T)) ())
  (test*-set-equal (fv (U ♯T
                          ([x : Int]
                           → {x : Int ∣ (x ⇒ y)} (tt ∣ ff))))
                   (y))
  ;;; function types
  (test*-set-equal (fv ([x : Int] → Int (tt ∣ ff))) ())
  (test*-set-equal (fv ([x : Int] → {y : Int ∣ (x ⇒ y)} (tt ∣ ff))) ())
  (test*-set-equal (fv ([x : Int] → {x : Int ∣ (x ⇒ y)} (tt ∣ ff))) (y))
  (test*-set-equal (fv ([x : ⊤] → Bool ((x ~ Int) ∣ (x ¬ Int)))) ())
  (test*-set-equal (fv ([x : ⊤] → Bool ((y ~ Int) ∣ (x ¬ Int)))) (y))
  (test*-set-equal (fv ([x : ⊤] → Bool ((x ~ Int) ∣ (y ¬ Int)))) (y))

  ;; propositions
  (test*-set-equal (fv tt) ())
  (test*-set-equal (fv ff) ())
  (test*-set-equal (fv (x ~ Int)) (x))
  (test*-set-equal (fv (x ¬ Int)) (x))
  (test*-set-equal (fv (x ~ ([x : Int] → {x : Int ∣ (x ⇒ z)} (tt ∣ ff))))
                   (x z))
  (test*-set-equal (fv (x ¬ ([x : Int] → {x : Int ∣ (x ⇒ z)} (tt ∣ ff))))
                   (x z))
  (test*-set-equal (fv (x ⇒ y)) (x y))
  (test*-set-equal (fv ((x ~ Int) ∧ (y ~ Int))) (x y))
  (test*-set-equal (fv ((x ~ Int) ∨ (y ~ Int))) (x y))
  (test*-set-equal (fv (x ≤ y)) (x y))
  (test*-set-equal (fv (x ≤ (2 ⊗ y))) (x y))
  (test*-set-equal (fv (x ≤ (2 ⊗ (x ⊕ z)))) (x z))

  ;; environments
  (test*-set-equal (fv ([] [] []))
                   ())
  (test*-set-equal (fv ([(x ≤ y) · ()]
                        []
                        []))
                   (x y))
  (test*-set-equal (fv (((x ≤ y) · ())
                        []
                        []))
                   (x y))
  (test*-set-equal (fv ([]
                        []
                        [(x ~ Int) · ()]))
                   (x)))



(module+ test
  (test-results))