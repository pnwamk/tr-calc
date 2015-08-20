#lang racket
(require redex
         "lang.rkt"
         "test-utils.rkt")

(provide α= test*-α=)

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
  sd : any -> any
  [(sd any) (sd/a any ())])

(define-metafunction DTR+DB
  sd/a : any ((x ...) ...) -> any
  ;; bound variable 
  [(sd/a x ((x_1 ...) ... (x_0 ... x x_2 ...) (x_3 ...) ...))
   (K n_rib n_pos)
   (where n_rib ,(length (term ((x_1 ...) ...))))
   (where n_pos ,(length (term (x_0 ...))))
   (where #false ,(member (term x) (term (x_1 ... ...))))]
  ;; free variables
  [(sd/a x (any ...)) x]
  ;; λ
  [(sd/a (λ ([x : τ] ...) e) (any ...))
   (λ ((sd/a τ (any ...)) ...)
     (sd/a e ((x ...) any ...)))]
  ;; let
  [(sd/a (let (x e_x) e) (any ...))
   (let ((sd/a e_x (any ...)))
     (sd/a e ((x) any ...)))]
  ;; function types
  [(sd/a ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (any ...))
   ((sd/a σ (any ...)) ...
    → (sd/a τ ((x ...) any ...))
    ((sd/a ψ_+ ((x ...) any ...))
     ∣
     (sd/a ψ_- ((x ...) any ...))))]
  ;; refinement types
  [(sd/a {x : τ ∣ ψ} (any ...))
   { : (sd/a τ (any ...))
       ∣ (sd/a ψ ((x) any ...))}]
  ;; syntactic lists
  [(sd/a (any ...) (any_x ...))
   ((sd/a any (any_x ...)) ...)]
  ;; other (ignore)
  [(sd/a any (any_x ...)) any])


;; sd/a-e tests
(module+ test
  (test*-equal (sd/a x ()) x)
  (test*-equal (sd/a x ((y))) x)
  (test*-equal (sd/a x ((x))) (K 0 0))
  (test*-equal (sd/a x ((y) (x))) (K 1 0))
  (test*-equal (sd/a b ((a) (b c) (d e))) (K 1 0))
  (test*-equal (sd/a c ((a) (b c) (d e))) (K 1 1))
  (test*-equal (sd 42) 42)
  (test*-equal (sd #t) #t)
  (test*-equal (sd +) +)
  (test*-equal (sd (λ () 42)) (λ () 42))
  (test*-equal (sd (λ ([x : Int]) x)) (λ (Int) (K 0 0)))
  (test*-equal (sd (λ ([x : Int] [y : Int]) (+ x y)))
               (λ (Int Int) (+ (K 0 0) (K 0 1))))
  (test*-equal (sd (λ ([x : Int] [y : Int])
                     (λ ([a : Int] [b : Int])
                       (+ (+ x a) (+ y b)))))
               (λ (Int Int)
                 (λ (Int Int)
                   (+ (+ (K 1 0) (K 0 0))
                      (+ (K 1 1) (K 0 1))))))
  (test*-equal (sd (if (λ ([x : Int] [y : Int]) (+ x y))
                       (λ ([x : Int] [y : Int]) (+ x y))
                       (λ ([x : Int] [y : Int]) (+ x y))))
               (if (λ (Int Int) (+ (K 0 0) (K 0 1)))
                   (λ (Int Int) (+ (K 0 0) (K 0 1)))
                   (λ (Int Int) (+ (K 0 0) (K 0 1)))))
  (test*-equal (sd (let (a (λ ([x : Int] [y : Int]) (+ x y)))
                     (a a a)))
               (let ((λ (Int Int) (+ (K 0 0) (K 0 1))))
                     ((K 0 0) (K 0 0) (K 0 0)))))

;; sd/a-τ tests
(module+ test
  (test*-equal (sd ⊤) ⊤)
  (test*-equal (sd ♯T) ♯T)
  (test*-equal (sd ♯F) ♯F)
  (test*-equal (sd Int) Int)
  (test*-equal (sd (U Int ♯T)) (U Int ♯T))
  (test*-equal (sd ([x : ⊤] → Bool (tt ∣ ff)))
               (⊤ → Bool (tt ∣ ff)))
  (test*-equal (sd (→ Bool ((x ~ Int) ∣ (x ¬ Int))))
               (→ Bool ((x ~ Int) ∣ (x ¬ Int))))
  (test*-equal (sd ([x : ⊤] → Bool ((x ~ Int) ∣ (x ¬ Int))))
               (⊤ → Bool (((K 0 0) ~ Int) ∣ ((K 0 0) ¬ Int))))
  (test*-equal (sd ([x : ⊤] [y : ⊤] → Bool ((y ~ Int) ∣ (y ¬ Int))))
               (⊤ ⊤ → Bool (((K 0 1) ~ Int) ∣ ((K 0 1) ¬ Int))))
  (test*-equal (sd {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                      ∣ ((y ~ Int) ∧ (x ~ Int))})
               {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))})
  (test*-equal (sd ([x : {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                            ∣ ((y ~ Int) ∧ (x ~ Int))}]
                    → {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                            ∣ ((y ~ Int) ∧ (x ~ Int))}
                    ((y ~ Int) ∣ (y ¬ Int))))
               ({: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))}
                → {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ ((K 1 0) ~ Int))}
                  ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))}
                ((y ~ Int) ∣ (y ¬ Int))))
  (test*-equal (sd (U Int {x : {y : ⊤ ∣ ((y ~ Int) ∧ (x ~ Int))}
                             ∣ ((y ~ Int) ∧ (x ~ Int))}))
               (U Int {: {: ⊤ ∣ (((K 0 0) ~ Int) ∧ (x ~ Int))}
                         ∣ ((y ~ Int) ∧ ((K 0 0) ~ Int))})))


;; sd/a-θ tests
(module+ test
  (test*-equal (sd/a 42 ()) 42)
  (test*-equal (sd/a x ()) x)
  (test*-equal (sd/a x ((x))) (K 0 0))
  (test*-equal (sd (42 ⊗ x)) (42 ⊗ x))
  (test*-equal (sd/a (42 ⊗ x) ((x))) (42 ⊗ (K 0 0)))
  (test*-equal (sd/a (y ⊕ (42 ⊗ x)) ((x) (y)))
               ((K 1 0) ⊕ (42 ⊗ (K 0 0)))))

;; sd/a-φ tests
(module+ tests
  (test*-equal (sd/a (x ≤ (y ⊕ (42 ⊗ x))) ((x) (y)))
               ((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))))

;; sd/a-ψ tests
(module+ test
  (test*-equal (sd (x ~ ⊤)) (x ~ ⊤))
  (test*-equal (sd (x ~ {x : ⊤ ∣ (x ~ Int)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}))
  (test*-equal (sd (x ¬ ⊤)) (x ¬ ⊤))
  (test*-equal (sd (x ¬ {x : ⊤ ∣ (x ¬ Int)}))
               (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)}))
  (test*-equal (sd ((x ¬ {x : ⊤ ∣ (x ¬ Int)})
                    ∨ (x ¬ {x : ⊤ ∣ (x ¬ Int)})))
               ((x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})
                ∨ (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})))
  (test*-equal (sd ((x ¬ {x : ⊤ ∣ (x ¬ Int)})
                    ∧ (x ¬ {x : ⊤ ∣ (x ¬ Int)})))
               ((x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})
                ∧ (x ¬ {: ⊤ ∣ ((K 0 0) ¬ Int)})))
  (test*-equal (sd (x ~ {x : ⊤ ∣ (x ⇒ y)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ⇒ y)}))
  (test*-equal (sd (x ~ {x : ⊤ ∣ (x ≤ y)}))
               (x ~ {: ⊤ ∣ ((K 0 0) ≤ y)})))



;; sd/a-Φ tests
(module+ test
  (test*-equal (sd ()) ())
  (test*-equal (sd/a () ()) ())
  (test*-equal (sd/a ((x ≤ (y ⊕ (42 ⊗ x))) · ()) ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0)))) · ()))
  (test*-equal (sd/a ((x ≤ (y ⊕ (42 ⊗ x)))
                        · ((x ≤ (y ⊕ (42 ⊗ x)))
                           · ()))
                       ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                · (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                   · ()))))

;; sd/a-Γ tests
(module+ test
  (test*-equal (sd/a () ()) ())
  (test*-equal (sd/a ((y : ⊤) · ((x : ⊤) · ())) ())
               ((y : ⊤) · ((x : ⊤) · ())))
  (test*-equal (sd/a ((y : ⊤) · ((x : {y : ⊤ ∣ (a ~ ⊤)}) · ())) ((a)))
               ((y : ⊤) · ((x : {: ⊤ ∣ ((K 1 0) ~ ⊤)}) · ()))))

;; sd/a-Ψ tests
(module+ test
  (test*-equal (sd/a () ()) ())
  (test*-equal (sd ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ()))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))
  (test*-equal (sd ((x ~ {x : ⊤ ∣ (x ~ Int)})
                    · ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ())))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)})
                · ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))))


;; ----------------------------------------------------------
;; alpha-equivalence
(define-metafunction DTR
  α= : any any -> boolean
  [(α= any_1 any_2)
   ,(equal? (term any_1*) (term any_2*))
   (where any_1* (sd any_1))
   (where any_2* (sd any_2))])

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

(module+ test
  (test-results))