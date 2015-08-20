#lang racket
(require redex
         "lang.rkt"
         "scope.rkt"
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
    ((subst (subst-raw ψ_+ ([x ↦ z] ...)) (any ...))
     ∣
     (subst (subst-raw ψ_- ([x ↦ z] ...)) (any ...))))
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
  (test*-α= (subst x ()) x)
  (test*-α= (subst x ([x ↦ y])) y)
  (test*-α= (subst 42 ([x ↦ y])) 42)
  (test*-α= (subst #t ([x ↦ y])) #t)
  (test*-α= (subst int? ([x ↦ y])) int?)
  (test*-α= (subst x ([z ↦ y])) x)
  (test*-α= (subst (x y z) ([x ↦ y])) (y y z))
  (test*-α= (subst (x y z) ([x ↦ y] [z ↦ y])) (y y y))
  (test*-α= (subst (+ x y) ([x ↦ a] [y ↦ b])) (+ a b))
  (test*-α= (subst (if x y z) ([x ↦ y])) (if y y z))
  (test*-α= (subst (if (if x y z)
                       (if x y z)
                       (if x y z))
                   ([x ↦ y]))
            (if (if y y z)
                (if y y z)
                (if y y z)))
  (test*-α= (subst (let (x y) z) ([y ↦ j])) (let (q j) z))
  (test*-α= (subst (let (x y) z) ([x ↦ y])) (let (q y) z))
  (test*-α= (subst (let (x y) z) ([z ↦ x])) (let (q y) x))
  (test*-α= (subst (let (f x) (f z)) ([x ↦ y])) (let (g y) (g z)))
  (test*-α= (subst (λ ([g : Int]) (g x)) ([x ↦ y]))
            (λ ([g : Int]) (g y)))
  (test*-α= (subst (λ ([g : Int]) (f g)) ([f ↦ g]))
            (λ ([x : Int]) (g x)))
  ;; types
  (test*-α= (subst ⊤ ([x ↦ y])) ⊤)
  (test*-α= (subst Int ([x ↦ y])) Int)
  (test*-α= (subst ♯T ([x ↦ y])) ♯T)
  (test*-α= (subst ♯F ([x ↦ y])) ♯F)
  (test*-α= (subst (U) ([x ↦ y])) (U))
  (test*-α= (subst (U Int ♯F) ([x ↦ y])) (U Int ♯F))
  (test*-α= (subst (U Int ♯F) ([x ↦ y])) (U Int ♯F))
  (test*-α= (subst {x : Int ∣ (x ≤ y)} ([y ↦ z]))
            {a : Int ∣ (a ≤ z)})
  (test*-α= (subst {x : Int ∣ (x ≤ x)} ([x ↦ y]))
            {a : Int ∣ (a ≤ a)})
  (test*-α= (subst {x : Int ∣ (x ≤ y)} ([y ↦ x]))
            {a : Int ∣ (a ≤ x)})
  (test*-α= (subst {x : {y : Int ∣ (y ≤ x)} ∣ (x ≤ y)} ([x ↦ y]))
            {a : {b : Int ∣ (b ≤ y)} ∣ (a ≤ y)})
  (test*-α= (subst (U Int {x : Int ∣ (x ≤ y)}) ([y ↦ x]))
            (U Int {a : Int ∣ (a ≤ x)}))

  (test*-α= (subst ([x : {i : Int ∣ (x ≤ y)}] → {b : Bool ∣ (x ≤ y)} ((x ≤ y) ∣ (y ≤ x)))
                   ([y ↦ z] [x ↦ a]))
            ([q : {i : Int ∣ (a ≤ z)}] → {b : Bool ∣ (q ≤ z)} ((q ≤ z) ∣ (z ≤ q))))

  ;; propositions
  (test*-α= (subst tt ([x ↦ y])) tt)
  (test*-α= (subst ff ([x ↦ y])) ff)
  (test*-α= (subst (x ~ Int) ([x ↦ y])) (y ~ Int))
  (test*-α= (subst (x ¬ Int) ([x ↦ y])) (y ¬ Int))
  (test*-α= (subst ((x ~ Int) ∧ (z ~ Int)) ([x ↦ y] [z ↦ a]))
            ((y ~ Int) ∧ (a ~ Int)))
  (test*-α= (subst ((x ~ Int) ∨ (z ~ Int)) ([x ↦ y] [z ↦ a]))
            ((y ~ Int) ∨ (a ~ Int)))
  (test*-α= (subst (x ⇒ y) ([x ↦ y])) (y ⇒ y))
  (test*-α= (subst (x ⇒ y) ([y ↦ x])) (x ⇒ x))
  (test*-α= (subst (x ⇒ y) ([y ↦ a] [x ↦ a])) (a ⇒ a))
  (test*-α= (subst (x ≤ y) ([x ↦ y])) (y ≤ y))
  (test*-α= (subst (x ≤ y) ([y ↦ x])) (x ≤ x)))


(module+ test
  (test-results))