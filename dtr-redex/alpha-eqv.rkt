#lang racket
(require redex
         "lang.rkt"
         "test-utils.rkt")

(define-extended-language DTR+DB DTR
  [e ::= .... (K nat nat) (λ (τ ...) e)
     (let (e) e)]
  [o ::= .... (K nat nat)]
  [τ ::= .... (σ ... → τ (ψ ∣ ψ)) { : τ ∣ ψ}]
  [ψ ::= .... ((K nat nat) ⇒ o)]
  (nat ::= natural))
 

(define-metafunction DTR+DB
  sd : any -> any
  [(sd any) (sd/a any ())])

(define-metafunction DTR+DB
  sd/a : any ((x ...) ...) -> any
  [(sd/a e ((x ...) ...)) (sd/a-e e ((x ...) ...))]
  [(sd/a τ ((x ...) ...)) (sd/a-τ τ ((x ...) ...))]
  [(sd/a ψ ((x ...) ...)) (sd/a-ψ ψ ((x ...) ...))]
  [(sd/a o ((x ...) ...)) (sd/a-o o ((x ...) ...))]
  [(sd/a θ ((x ...) ...)) (sd/a-θ θ ((x ...) ...))]
  [(sd/a φ ((x ...) ...)) (sd/a-φ φ ((x ...) ...))]
  [(sd/a Φ ((x ...) ...)) (sd/a-Φ Φ ((x ...) ...))]
  [(sd/a Γ ((x ...) ...)) (sd/a-Γ Γ ((x ...) ...))]
  [(sd/a Ψ ((x ...) ...)) (sd/a-Ψ Ψ ((x ...) ...))])


;; ----------------------------------------------------------
;; Object DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-o : o ((x ...) ...) -> o
  [(sd/a-o x ((x_1 ...) ... (x_0 ... x x_2 ...) (x_3 ...) ...))
   ; bound variable 
   (K n_rib n_pos)
   (where n_rib ,(length (term ((x_1 ...) ...))))
   (where n_pos ,(length (term (x_0 ...))))
   (where #false ,(member (term x) (term (x_1 ... ...))))]
  [(sd/a-o o (any_rest ...)) o])

(module+ test
  (test*-equal (sd/a-o x ()) x)
  (test*-equal (sd/a-o x ((y))) x)
  (test*-equal (sd/a-o x ((x))) (K 0 0))
  (test*-equal (sd/a-o x ((y) (x))) (K 1 0)))

;; ----------------------------------------------------------
;; Expression DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-e : e ((x ...) ...) -> e
  [(sd/a-e x (any_rest ...)) (sd/a-o x (any_rest ...))]
  [(sd/a-e n (any_rest ...)) n]
  [(sd/a-e b (any_rest ...)) b]
  [(sd/a-e p (any_rest ...)) p]
  ;; λ
  [(sd/a-e (λ ([x : τ] ...) e) (any_rest ...))
   (λ ((sd/a-τ τ (any_rest ...)) ...)
     (sd/a-e e ((x ...) any_rest ...)))]
  ;; if
  [(sd/a-e (if e_1 e_2 e_3) (any_rest ...))
   (if (sd/a-e e_1 (any_rest ...))
       (sd/a-e e_2 (any_rest ...))
       (sd/a-e e_3 (any_rest ...)))]
  ;; let
  [(sd/a-e (let (x e_x) e) (any_rest ...))
   (let ((sd/a-e e_x (any_rest ...)))
     (sd/a-e e ((x) any_rest ...)))]
  ;; app
  [(sd/a-e (e ...) (any_rest ...))
   ((sd/a e (any_rest ...)) ...)])

;; sd/a-e tests
(module+ test
  (test*-equal (sd x) x)
  (test*-equal (sd/a-e x ((x))) (K 0 0))
  (test*-equal (sd/a-e b ((a) (b c) (d e))) (K 1 0))
  (test*-equal (sd/a-e c ((a) (b c) (d e))) (K 1 1))
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

;; ----------------------------------------------------------
;; Type DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-τ : τ ((x ...) ...) -> τ
  [(sd/a-τ ⊤ (any_rest ...) ...) ⊤]
  [(sd/a-τ ♯T (any_rest ...)) ♯T]
  [(sd/a-τ ♯F (any_rest ...)) ♯F]
  [(sd/a-τ Int (any_rest ...)) Int]
  [(sd/a-τ (U τ ...) (any_rest ...))
   (U (sd/a-τ τ (any_rest ...)) ...)]
  [(sd/a-τ ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (any_rest ...))
   ((sd/a-τ σ (any_rest ...)) ...
    → (sd/a-τ τ ((x ...) any_rest ...))
    ((sd/a-ψ ψ_+ ((x ...) any_rest ...))
     ∣
     (sd/a-ψ ψ_- ((x ...) any_rest ...))))]
  [(sd/a-τ {x : τ ∣ ψ} (any_rest ...))
   { : (sd/a-τ τ (any_rest ...))
       ∣ (sd/a-ψ ψ ((x) any_rest ...))}])


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


;; ----------------------------------------------------------
;; Linear Expressions DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-θ : θ ((x ...) ...) -> θ
  [(sd/a-θ n (any_rest ...)) n]
  [(sd/a-θ x (any_rest ...))
   (sd/a-o x (any_rest ...))]
  [(sd/a-θ (n ⊗ θ) (any_rest ...))
   (n ⊗ (sd/a-θ θ (any_rest ...)))]
  [(sd/a-θ (θ_l ⊕ θ_r) (any_rest ...))
   ((sd/a-θ θ_l (any_rest ...))
    ⊕
    (sd/a-θ θ_r (any_rest ...)))])

;; sd/a-θ tests
(module+ test
  (test*-equal (sd/a-θ 42 ()) 42)
  (test*-equal (sd/a-θ x ()) x)
  (test*-equal (sd/a-θ x ((x))) (K 0 0))
  (test*-equal (sd (42 ⊗ x)) (42 ⊗ x))
  (test*-equal (sd/a-θ (42 ⊗ x) ((x))) (42 ⊗ (K 0 0)))
  (test*-equal (sd/a-θ (y ⊕ (42 ⊗ x)) ((x) (y)))
               ((K 1 0) ⊕ (42 ⊗ (K 0 0)))))

;; ----------------------------------------------------------
;; Inequality DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-φ : φ ((x ...) ...) -> φ
  [(sd/a-φ (θ_l ≤ θ_r) (any_rest ...))
   ((sd/a-θ θ_l (any_rest ...)) ≤ (sd/a-θ θ_r (any_rest ...)))])

;; sd/a-φ tests
(module+ tests
  (test*-equal (sd/a-θ (x ≤ (y ⊕ (42 ⊗ x))) ((x) (y)))
               ((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))))

;; ----------------------------------------------------------
;; Proposition DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-ψ : ψ ((x ...) ...) -> ψ
  [(sd/a-ψ tt (any_rest ...)) tt]
  [(sd/a-ψ ff (any_rest ...)) ff]
  [(sd/a-ψ (o ~ τ) (any_rest ...))
   ((sd/a-o o (any_rest ...)) ~ (sd/a-τ τ (any_rest ...)))]
  [(sd/a-ψ (o ¬ τ) (any_rest ...))
   ((sd/a-o o (any_rest ...)) ¬ (sd/a-τ τ (any_rest ...)))]
  ;; x ↦ other linear expression
  [(sd/a-ψ (ψ_l ∨ ψ_r) (any_rest ...))
   ((sd/a-ψ ψ_l (any_rest ...))
    ∨
    (sd/a-ψ ψ_r (any_rest ...)))]
  [(sd/a-ψ (ψ_l ∧ ψ_r) (any_rest ...))
   ((sd/a-ψ ψ_l (any_rest ...))
    ∧
    (sd/a-ψ ψ_r (any_rest ...)))]
  
  [(sd/a-ψ (x ⇒ o) (any_rest ...))
   ((sd/a-o x (any_rest ...))
    ⇒
    (sd/a-o o (any_rest ...)))]
  [(sd/a-ψ φ (any_rest ...))
   (sd/a-φ φ (any_rest ...))])

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


;; ----------------------------------------------------------
;; Inequality Env DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-Φ : Φ ((x ...) ...) -> Φ
  [(sd/a-Φ () (any_rest ...)) ()]
  [(sd/a-Φ (φ · Φ) (any_rest ...))
   ((sd/a-φ φ (any_rest ...))
    ·
    (sd/a-Φ Φ (any_rest ...)))])


;; sd/a-Φ tests
(module+ test
  (test*-equal (sd ()) ())
  (test*-equal (sd/a-Φ () ()) ())
  (test*-equal (sd/a-Φ ((x ≤ (y ⊕ (42 ⊗ x))) · ()) ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0)))) · ()))
  (test*-equal (sd/a-Φ ((x ≤ (y ⊕ (42 ⊗ x)))
                        · ((x ≤ (y ⊕ (42 ⊗ x)))
                           · ()))
                       ((x) (y)))
               (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                · (((K 0 0) ≤ ((K 1 0) ⊕ (42 ⊗ (K 0 0))))
                   · ()))))

;; ----------------------------------------------------------
;; Type Env DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-Γ : Γ ((x ...) ...) -> Γ
  [(sd/a-Γ () (any_rest ...)) ()]
  [(sd/a-Γ ((x : τ) · Γ) (any_rest ...))
   ((x : (sd/a-τ τ (any_rest ...)))
    ·
    (sd/a-Γ Γ (any_rest ...)))])

;; sd/a-Γ tests
(module+ test
  (test*-equal (sd/a-Γ () ()) ())
  (test*-equal (sd/a-Γ ((y : ⊤) · ((x : ⊤) · ())) ())
               ((y : ⊤) · ((x : ⊤) · ())))
  (test*-equal (sd/a-Γ ((y : ⊤) · ((x : {y : ⊤ ∣ (a ~ ⊤)}) · ())) ((a)))
               ((y : ⊤) · ((x : {: ⊤ ∣ ((K 1 0) ~ ⊤)}) · ()))))

;; ----------------------------------------------------------
;; Proposition Env DeBruijn-ification
(define-metafunction DTR+DB
  sd/a-Ψ : Ψ ((x ...) ...) -> Ψ
  [(sd/a-Ψ () (any_rest ...)) ()]
  [(sd/a-Ψ (ψ · Ψ) (any_rest ...))
   ((sd/a-ψ ψ (any_rest ...))
    ·
    (sd/a-Ψ Ψ (any_rest ...)))])


;; sd/a-Ψ tests
(module+ test
  (test*-equal (sd/a-Ψ () ()) ())
  (test*-equal (sd ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ()))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))
  (test*-equal (sd ((x ~ {x : ⊤ ∣ (x ~ Int)})
                    · ((x ~ {x : ⊤ ∣ (x ~ Int)}) · ())))
               ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)})
                · ((x ~ {: ⊤ ∣ ((K 0 0) ~ Int)}) · ()))))


(module+ test
  (test-results))