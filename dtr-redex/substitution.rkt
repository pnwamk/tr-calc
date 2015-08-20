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
  [(subst e (any ...)) (subst-e e (any ...))]
  [(subst τ (any ...)) (subst-τ τ (any ...))]
  [(subst ψ (any ...)) (subst-ψ ψ (any ...))]
  [(subst o (any ...)) (subst-o o (any ...))]
  [(subst θ (any ...)) (subst-θ θ (any ...))]
  [(subst φ (any ...)) (subst-φ φ (any ...))]
  [(subst Φ (any ...)) (subst-Φ Φ (any ...))]
  [(subst Γ (any ...)) (subst-Γ Γ (any ...))]
  [(subst Ψ (any ...)) (subst-Ψ Ψ (any ...))])


(define-metafunction DTR
  subst-e : e ([x ↦ o] ...) -> e
  [(subst-e y (any_1 ... (y ↦ o_y) any_2 ...)) o_y]
  [(subst-e x (any ...)) x]
  [(subst-e n (any ...)) n]
  [(subst-e b (any ...)) b]
  [(subst-e p (any ...)) p]
  ;; λ
  [(subst-e (λ ([x : τ] ...) e) (any ...))
   (λ ([z : (subst-τ τ (any ...))] ...)
     (subst (subst-raw e [(x ↦ z) ...]) (any ...)))
   (where (z ...) (fresh-vars (e (any ...)) (x ...)))]
  ;; if
  [(subst-e (if e_1 e_2 e_3) (any ...))
   (if (subst-e e_1 (any ...))
       (subst-e e_2 (any ...))
       (subst-e e_3 (any ...)))]
  ;; let
  [(subst-e (let (x e_x) e) (any ...))
   (let (z (subst-e e_x (any ...)))
     (subst-e (subst-raw e [(x ↦ z)]) (any ...)))
   (where z (fresh-var (e (any ...))))]
  ;; app
  [(subst-e (e ...) (any ...))
   ((subst e (any ...)) ...)])

(define-metafunction DTR
  subst-o : o ([x ↦ o] ...) -> o
  [(subst-o y (any_1 ... (y ↦ o) any_2 ...)) o]
  [(subst-o x (any ...)) x])

(define-metafunction DTR
  subst-τ : τ ([x ↦ o] ...) -> τ
  [(subst-τ ⊤ (any ...)) ⊤]
  [(subst-τ ♯T (any ...)) ♯T]
  [(subst-τ ♯F (any ...)) ♯F]
  [(subst-τ Int (any ...)) Int]
  [(subst-τ (U τ ...) (any ...))
   (U (subst-τ τ (any ...)) ...)]
  [(subst-τ ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (any ...))
   ([z : (subst-τ σ (any ...))] ...
    → (subst-τ (subst-raw τ [(x ↦ z) ...]) (any ...))
    ((subst-ψ (subst-raw ψ_+ [(x ↦ z) ...]) (any ...))
     ∣
     (subst-ψ (subst-raw ψ_- (x ↦ z) ...) (any ...))))
   (where (z ...) (fresh-vars (τ ψ_+ ψ_- (any ...)) (x ...)))]
  [(subst-τ {x : τ ∣ ψ} (any ...))
   {z : (subst-τ τ (any ...))
      ∣ (subst-ψ (subst-raw ψ (x ↦ z)) (any ...))}
   (where z (fresh-var (ψ (any ...))))])

(define-metafunction DTR
  subst-ψ : ψ ([x ↦ o] ...) -> ψ
  [(subst-ψ (y ~¬ τ) (any_1 ... (y ↦ o) any_2 ...))
   (o ~¬ (subst-τ τ (any_1 ... (y ↦ o) any_2 ...)))]
  [(subst-ψ (x -? τ) (any ...))
   (x -? (subst-τ τ (any ...)))]
  ;; x ↦ other linear expression
  [(subst-ψ (ψ_l ∨∧ ψ_r) (any ...))
   ((subst-ψ ψ_l (any ...)) ∨∧ (subst-ψ ψ_r (any ...)))]
  [(subst-ψ φ (x ↦ o) ...) (subst φ (x ↦ o) ...)])


(define-metafunction DTR
  subst-φ : φ (x ↦ o) ... -> φ
  [(subst-φ (θ_l ≤ θ_r) (x ↦ o) ...)
   ((subst-θ θ_l (x ↦ o) ...) ≤ (subst-θ θ_r (x ↦ o) ...))])

(define-metafunction DTR
  subst-θ : θ (x ↦ o) ... -> θ
  [(subst-θ n (x ↦ o) ...) n]
  [(subst-θ y (x ↦ o_x) ... (y ↦ o_y) (z ↦ o_z) ...) o_y]
  [(subst-θ x (y ↦ o) ...) x]
  [(subst-θ (n ⊗ θ) (x ↦ o) ...) (n ⊗ (subst-θ θ (x ↦ o) ...))]
  [(subst-θ (θ_l ⊕ θ_r) (x ↦ o) ...)
   ((subst-θ θ_l (x ↦ o) ...) ⊕ (subst-θ θ_r (x ↦ o) ...))])


(define-metafunction DTR
  subst-Φ : Φ (x ↦ o) ... -> Φ
  [(subst-Φ () (x ↦ o) ...) ()]
  [(subst-Φ (φ · Φ) (x ↦ o) ...)
   ((subst-φ φ (x ↦ o) ...)
    ·
    (subst-Φ Φ (x ↦ o) ...))])

(define-metafunction DTR
  subst-Γ : Γ (x ↦ o) ... -> Γ
  [(subst-Γ () (x ↦ o) ...) ()]
  [(subst-Γ ((x : τ) · Γ) (y ↦ o) ...)
   ((x : (subst-τ τ (y ↦ o) ...))
    ·
    (subst-Γ Γ (x ↦ o) ...))])

(define-metafunction DTR
  subst-Ψ : Ψ (x ↦ o) ... -> Ψ
  [(subst-Ψ () (x ↦ o) ...) ()]
  [(subst-Ψ (ψ · Ψ) (x ↦ o) ...)
   ((subst-ψ ψ (x ↦ o) ...)
    ·
    (subst-Ψ Ψ (x ↦ o) ...))])


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
  (test*-α= (subst x [x ↦ y]) y)
  (test*-α= (subst x [z ↦ y]) x)
  (test*-α= (subst (x y z) [x ↦ y]) (y y z))
  (test*-α= (subst (x y z) [x ↦ y] [z ↦ y]) (y y y))
  (test*-α= (subst (+ x y) [x ↦ 1] [y ↦ 2]) (+ 1 2))
  (test*-α= (subst (if x y z) [x ↦ y]) (if y y z))
  (test*-α= (subst (let (x y) z) [x ↦ y]) (let (q y) z))
  (test*-α= (subst (let (f x) (f z)) [x ↦ y]) (let (g y) (g z)))
  (test*-α= (subst (λ ([g : I]) (f g)) [f ↦ g])
            (λ ([x : I]) (g x)))
  ;; types
  (test*-α= (subst ⊤ [x ↦ y]) ⊤)
  (test*-α= (subst I [x ↦ y]) I)
  (test*-α= (subst ♯t [x ↦ y]) ♯t)
  (test*-α= (subst ♯f [x ↦ y]) ♯f)
  (test*-α= (subst (I ∪ ♯f) ([x ↦ y])) (I ∪ ♯f))
  
  (test*-α= (subst {x : I ∣ [(x ≤ x)]} ([x ↦ y]))
            {a : I ∣ [(a ≤ a)]})
  (test*-α= (subst {x : I ∣ [(x ≤ y)]} ([y ↦ x]))
            {a : I ∣ [(a ≤ x)]})
  (test*-α= (subst {y : {a : I ∣ [(x ≤ a)]} ∣ [(y ≤ x)]} ([x ↦ y]))
            {z : {a : I ∣ [(y ≤ a)]} ∣ [(z ≤ y)]})

  ;; propositions
  (test*-α= (subst (x ~ I) ([x ↦ y])) (y ~ I))
  (test*-α= (subst (x ¬ I) ([x ↦ y])) (y ¬ I))
  (test*-α= (subst (x ~ I) ([x ↦ 42])) tt)
  (test*-α= (subst (x ¬ I) ([x ↦ 42])) ff)

  ;; environments
  (test*-α= (subst [() ((x : I)) ()] ((x ↦ y))) [() () ((y ~ I))])
  (test*-α= (subst [() ((x : I)) ()] ((y ↦ x))) [() ((x : I)) ()])
  (test*-α= (subst [((x ≤ z)) () ()] ((x ↦ y))) [((y ≤ z)) () ()])
  (test*-α= (subst [(((2 ⊛ x) ≤ z)) () ()] ((x ↦ y))) [(((2 ⊛ y) ≤ z)) () ()])
  
  )


;; *******************************************************************
;; fv tests
(module+ test
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