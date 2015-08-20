#lang racket
(require redex
         "lang.rkt"
         "test-utils.rkt")

(provide
 ;; alpha equivalence functions
 α= test*-α=
 ;; free-variables
 s-db DTR+DB)

(define-extended-language DTR+DB DTR
  [e ::= .... (K nat nat) (λ (τ ...) e)
     (let (e) e)]
  [o ::= .... (K nat nat)]
  [τ ::= .... (σ ... → τ (ψ ∣ ψ)) { : τ ∣ ψ}]
  [ψ ::= .... ((K nat nat) ⇒ o)]
  (nat ::= natural))
 

;; ----------------------------------------------------------
;; DeBruijn Conversion
(define-metafunction DTR+DB
  s-db : any -> any
  [(s-db any) (s-db/a any ())])

(define-metafunction DTR+DB
  s-db/a : any ((x ...) ...) -> any
  ;; bound variable 
  [(s-db/a x ((x_1 ...) ... (x_0 ... x x_2 ...) (x_3 ...) ...))
   (K n_rib n_pos)
   (where n_rib ,(length (term ((x_1 ...) ...))))
   (where n_pos ,(length (term (x_0 ...))))
   (where #false ,(member (term x) (term (x_1 ... ...))))]
  ;; free variables
  [(s-db/a x (any ...)) x]
  ;; λ
  [(s-db/a (λ ([x : τ] ...) e) (any ...))
   (λ ((s-db/a τ (any ...)) ...)
     (s-db/a e ((x ...) any ...)))]
  ;; let
  [(s-db/a (let (x e_x) e) (any ...))
   (let ((s-db/a e_x (any ...)))
     (s-db/a e ((x) any ...)))]
  ;; function types
  [(s-db/a ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (any ...))
   ((s-db/a σ (any ...)) ...
    → (s-db/a τ ((x ...) any ...))
    ((s-db/a ψ_+ ((x ...) any ...))
     ∣
     (s-db/a ψ_- ((x ...) any ...))))]
  ;; refinement types
  [(s-db/a {x : τ ∣ ψ} (any ...))
   { : (s-db/a τ (any ...))
       ∣ (s-db/a ψ ((x) any ...))}]
  ;; syntactic lists
  [(s-db/a (any ...) (any_x ...))
   ((s-db/a any (any_x ...)) ...)]
  ;; other (ignore)
  [(s-db/a any (any_x ...)) any])


;; sd/a-e tests
(module+ test
  (test*-equal (s-db/a x ()) x)
  (test*-equal (s-db/a x ((y))) x)
  (test*-equal (s-db/a x ((x))) (K 0 0))
  (test*-equal (s-db/a x ((y) (x))) (K 1 0))
  (test*-equal (s-db/a b ((a) (b c) (d e))) (K 1 0))
  (test*-equal (s-db/a c ((a) (b c) (d e))) (K 1 1))
  (test*-equal (s-db 42) 42)
  (test*-equal (s-db #t) #t)
  (test*-equal (s-db +) +)
  (test*-equal (s-db (λ () 42)) (λ () 42))
  (test*-equal (s-db (λ ([x : Int]) x)) (λ (Int) (K 0 0)))
  (test*-equal (s-db (λ ([x : Int] [y : Int]) (+ x y)))
               (λ (Int Int) (+ (K 0 0) (K 0 1))))
  (test*-equal (s-db (λ ([x : Int] [y : Int])
                     (λ ([a : Int] [b : Int])
                       (+ (+ x a) (+ y b)))))
               (λ (Int Int)
                 (λ (Int Int)
                   (+ (+ (K 1 0) (K 0 0))
                      (+ (K 1 1) (K 0 1))))))
  (test*-equal (s-db (if (λ ([x : Int] [y : Int]) (+ x y))
                       (λ ([x : Int] [y : Int]) (+ x y))
                       (λ ([x : Int] [y : Int]) (+ x y))))
               (if (λ (Int Int) (+ (K 0 0) (K 0 1)))
                   (λ (Int Int) (+ (K 0 0) (K 0 1)))
                   (λ (Int Int) (+ (K 0 0) (K 0 1)))))
  (test*-equal (s-db (let (a (λ ([x : Int] [y : Int]) (+ x y)))
                     (a a a)))
               (let ((λ (Int Int) (+ (K 0 0) (K 0 1))))
                     ((K 0 0) (K 0 0) (K 0 0)))))

;; sd/a-τ tests
(module+ test
  (test*-equal (s-db ⊤) ⊤)
  (test*-equal (s-db ♯T) ♯T)
  (test*-equal (s-db ♯F) ♯F)
  (test*-equal (s-db Int) Int)
  (test*-equal (s-db (U Int ♯T)) (U Int ♯T))
  (test*-equal (s-db ([x : ⊤] → Bool (tt ∣ ff)))
               (⊤ → Bool (tt ∣ ff)))
  (test*-equal (s-db (→ Bool ((x ~ Int) ∣ (x ¬ Int))))
               (→ Bool ((x ~ Int) ∣ (x ¬ Int))))
  (test*-equal (s-db ([x : ⊤] → Bool ((x ~ Int) ∣ (x ¬ Int))))
               (⊤ → Bool (((K 0 0) ~ Int) ∣ ((K 0 0) ¬ Int))))
  (test*-equal (s-db ([x : ⊤] [y : ⊤] → Bool ((y ~ Int) ∣ (y ¬ Int))))
               (⊤ ⊤ → Bool (((K 0 1) ~ Int) ∣ ((K 0 1) ¬ Int))))
  (test*-equal (s-db {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                      ∣ ((y ~ Int) ∧ (x ~ Int))})
               {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))})
  (test*-equal (s-db ([x : {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                            ∣ ((y ~ Int) ∧ (x ~ Int))}]
                    → {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                            ∣ ((y ~ Int) ∧ (x ~ Int))}
                    ((y ~ Int) ∣ (y ¬ Int))))
               ({: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))}
                → {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ ((K 1 0) ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))}
                ((y ~ Int) ∣ (y ¬ Int))))
  (test*-equal (s-db (U Int {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                             ∣ ((y ~ Int) ∧ (x ~ Int))}))
               (U Int {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                         ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))})))


;; sd/a-θ tests
(module+ test
  (test*-equal (s-db/a 42 ()) 42)
  (test*-equal (s-db/a x ()) x)
  (test*-equal (s-db/a x ((x))) (K 0 0))
  (test*-equal (s-db (42 ⊗ x)) (42 ⊗ x))
  (test*-equal (s-db/a (42 ⊗ x) ((x))) (42 ⊗ (K 0 0)))
  (test*-equal (s-db/a (y ⊕ (42 ⊗ x)) ((x) (y)))
               ((K 1 0) ⊕ (42 ⊗ (K 0 0)))))

;; sd/a-φ tests
(module+ tests
  (test*-equal (s-db/a (x ≤ (y ⊕ (42 ⊗ x))) ((x) (y)))
               ((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))))

;; sd/a-ψ tests
(module+ test
  (test*-equal (s-db (x ~ ⊤)) (x ~ ⊤))
  (test*-equal (s-db (x ~ {x : ⊤ ∣ (x ~ Int)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}))
  (test*-equal (s-db (x ¬ ⊤)) (x ¬ ⊤))
  (test*-equal (s-db (x ¬ {x : ⊤ ∣ (x ¬ Int)}))
               (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)}))
  (test*-equal (s-db ((x ¬ {x : ⊤ ∣ (x ¬ Int)})
                    ∨ (x ¬ {x : ⊤ ∣ (x ¬ Int)})))
               ((x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})
                ∨ (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})))
  (test*-equal (s-db ((x ¬ {x : ⊤ ∣ (x ¬ Int)})
                    ∧ (x ¬ {x : ⊤ ∣ (x ¬ Int)})))
               ((x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})
                ∧ (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})))
  (test*-equal (s-db (x ~ {x : ⊤ ∣ (x ⇒ y)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ⇒ y)}))
  (test*-equal (s-db (x ~ {x : ⊤ ∣ (x ≤ y)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ≤ y)})))



;; sd/a-Φ tests
(module+ test
  (test*-equal (s-db ()) ())
  (test*-equal (s-db/a () ()) ())
  (test*-equal (s-db/a ((x ≤ (y ⊕ (42 ⊗ x))) · ()) ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0)))) · ()))
  (test*-equal (s-db/a ((x ≤ (y ⊕ (42 ⊗ x)))
                        · ((x ≤ (y ⊕ (42 ⊗ x)))
                           · ()))
                       ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                · (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                   · ()))))

;; sd/a-Γ tests
(module+ test
  (test*-equal (s-db/a () ()) ())
  (test*-equal (s-db/a ((y : ⊤) · ((x : ⊤) · ())) ())
               ((y : ⊤) · ((x : ⊤) · ())))
  (test*-equal (s-db/a ((y : ⊤) · ((x : {y : ⊤ ∣ (a ~ ⊤)}) · ())) ((a)))
               ((y : ⊤) · ((x : {: ⊤ ∣ ((K 1 0) ~ ⊤)}) · ()))))

;; sd/a-Ψ tests
(module+ test
  (test*-equal (s-db/a () ()) ())
  (test*-equal (s-db ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ()))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))
  (test*-equal (s-db ((x ~ {x : ⊤ ∣ (x ~ Int)})
                    · ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ())))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)})
                · ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))))


;; ----------------------------------------------------------
;; alpha-equivalence
(define-metafunction DTR
  α= : any any -> boolean
  [(α= any_1 any_2)
   ,(equal? (term any_1*) (term any_2*))
   (where any_1* (s-db any_1))
   (where any_2* (s-db any_2))])

(module+ test
  (test*-true (α= x x))
  (test*-true (α= 42 42))
  (test*-false (α= 42 x))
  (test*-true (α= (λ ([x : ⊤]) x) (λ ([y : ⊤]) y)))
  (test*-true (α= (λ ([x : ⊤] [y : ⊤])
                    (λ ([z : ⊤])
                      (x y z)))
                  (λ ([a : ⊤] [b : ⊤])
                    (λ ([c : ⊤])
                      (a b c)))))
  (test*-true (α= (let (x 42) (+ x x))
                  (let (a 42) (+ a a)))))

(define-syntax-rule (test*-α= t1 t2)
  (test-equal (term (α= t1 t2)) #t))


;; ----------------------------------------------------------
;; free variables
(define-metafunction DTR
  fv : any -> (x ...)
  [(fv any)
   ,(set->list (for/set ([a (in-list (flatten (term (s-db any))))]
                         #:when (redex-match? DTR+DB x a))
                 a))])

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