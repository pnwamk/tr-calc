#lang racket

(require redex)
(provide (all-defined-out))

(define-language DTR
  ;; variables, as a convention
  [x ::= variable-not-otherwise-mentioned]
  [n ::= integer]
  [b ::= #t #f]
  ;; primitive operations
  [p ::= int? bool? + <= *2]
  ;; Expressions
  [e ::= n b p x (λ ([x : τ] ...) e)
     (e e ...) (if e e e) (let (x e) e)]
  ;; linear combinations
  [o ::= x]
  [θ ::= n o (n ⊗ θ) (θ ⊕ θ)]
  ;; systems of linear inequalities
  [τ σ ::= ⊤ ♯T ♯F Int (U τ ...)
     ([x : σ] ... → τ (ψ ∣ ψ)) {x : τ ∣ ψ}]
  [φ ::= (θ ≤ θ)]
  ;; propositions
  [ψ ::= (o ~ τ) (o ¬ τ) (x ⇒ o)
     (ψ ∧ ψ) (ψ ∨ ψ) tt ff φ]
  ;; linear constraint environment
  [Φ ::= () (φ · Φ)]
  ;; Type Environment
  [Γ  ::= () ((x : τ) · Γ)]
  ;; Proposition Environment
  [Ψ  ::= () (ψ · Ψ)]
  ;; Environment
  [Δ ::= [Φ Γ Ψ]])


;; --------------------------------------------------------------
;; in  (basic membership predicate/metafunction)
(define-metafunction DTR
  in : any any -> b
  [(in any_2 (any_1 ... any_2 any_3 ...)) #t]
  [(in any_1 (any_1 · any_rest)) #t]
  [(in any_1 (any_2 · (any_3 · any_rest)))
   (in any_1 (any_3 · any_rest))]
  [(in any_2 (any_1 ...)) #f])

;; --------------------------------------------------------------
;; sans
;; removes an id's entries from Γ (entirely)
(define-metafunction DTR
  sans : x Γ -> Γ
  [(sans x ()) ()]
  [(sans x ((x : τ) · Γ))
   (sans x Γ)]
  [(sans x ((y : τ) · Γ))
   ((y : τ) · (sans x Γ))])


;; --------------------------------------------------------------
;; lookup
;; lookup type of x in Γ
;; (takes an optional default argument for failure)
(define-metafunction DTR
  [(lookup x ()) #f]
  [(lookup x () σ) σ]
  [(lookup x ((x : τ) · Γ)) τ]
  [(lookup x ((x : τ) · Γ) any) τ]
  [(lookup x ((y : τ) · Γ))
   (lookup x Γ)]
  [(lookup x ((y : τ) · Γ) any)
   (lookup x Γ any)])

(define-metafunction DTR
  id-at-⊥ : Γ -> x or #f
  [(id-at-⊥ ()) #f]
  [(id-at-⊥ ((x : (U)) · Γ)) x]
  [(id-at-⊥ ((x : τ) · Γ))
   (id-at-⊥ Γ)])

(define-metafunction DTR
  id-at-refine : Γ -> x or #f
  [(id-at-refine ()) #f]
  [(id-at-refine ((x : {y : τ ∣ ψ}) · Γ)) x]
  [(id-at-refine ((x : τ) · Γ))
   (id-at-refine Γ)])

(define-metafunction DTR
  fresh-var : any x -> x
  [(fresh-var any x) ,(variable-not-in (term any) (term x))])

(define-metafunction DTR
  fresh-vars : any (x ...) -> (x ...)
  [(fresh-vars any (x ...)) ,(variables-not-in (term any) (term (x ...)))])

(define-metafunction DTR
  Un : τ ... -> τ
  [(Un τ) τ]
  [(Un σ ... ⊤ τ ...) ⊤]
  [(Un σ ... (U) τ ...)
   (Un σ ... τ ...)]
  [(Un σ ... (U τ_inner ...) τ ...)
   (Un σ ... τ_inner ... τ ...)]
  [(Un τ ...)
   (U σ ...)
   (where (σ ...) ,(sort (term (τ ...))
                         (λ (a b)
                           (<= (equal-hash-code a)
                               (equal-hash-code b)))))])

(define x? (redex-match? DTR x))
(define p? (redex-match? DTR p))
(define e? (redex-match? DTR e))
(define o? (redex-match? DTR o))
(define θ? (redex-match? DTR θ))
(define τ? (redex-match? DTR θ))
(define φ? (redex-match? DTR φ))
(define ψ? (redex-match? DTR ψ))
(define Φ? (redex-match? DTR Φ))
(define Γ? (redex-match? DTR Γ))
(define Ψ? (redex-match? DTR Ψ))
(define Δ? (redex-match? DTR Δ))
(define is? (redex-match? DTR (x ~ τ)))
(define not? (redex-match? DTR (x ¬ τ)))
(define alias? (redex-match? DTR (x ⇒ o)))
(define conj? (redex-match? DTR (ψ_l ∧ ψ_r)))
(define disj? (redex-match? DTR (ψ_l ∨ ψ_r)))
(define ff? (redex-match? DTR ff))
(define tt? (redex-match? DTR tt))


;; short-hands
(define-term Bool (Un ♯T ♯F))
(define-term ⊥ (U))
(define-term mt-Δ [() () ()])
(define-metafunction DTR
  = : θ θ -> ψ
  [(= θ_1 θ_2) ((θ_1 ≤ θ_2) ∧ (θ_2 ≤ θ_1))])

