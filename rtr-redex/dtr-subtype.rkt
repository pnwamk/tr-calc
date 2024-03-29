#lang racket
(require redex
         "dtr-lang.rkt"
         "dtr-subst.rkt"
         "dtr-fme.rkt"
         "utils.rkt")

(provide (all-defined-out))

(define (simple-Δ? Δ)
  (simple-Ψ? (third Δ)))

(define (simple-Ψ? Ψ)
  (match Ψ
    [(list) #t]
    [`(,(? not?) · ,rst)
     (simple-Ψ? rst)]
    [_ #f]))

(define (atomic-ψ? a)
  (or (redex-match? DTR (o ~ τ) a)
      (redex-match? DTR (o ¬ τ) a)))

(module+ test
  (test-true (simple-Ψ? (term ((x ¬ Int) · ()))))
  (test-true (simple-Ψ? (term ((x ¬ Int) · ((x ¬ Int) · ())))))
  (test-false (simple-Ψ? (term ((x ¬ Int) · (ff · ())))))
  (test-false (simple-Ψ? (term (ff · ())))))

;; --------------------------------------------------------------
;; whether or not two types potentially overlap
(define-judgment-form DTR
  #:mode (overlap I I)
  #:contract (overlap τ τ)
  [---------------------- "O-Refl"
   (overlap τ τ)]
  [---------------------- "O-TopRhs"
   (overlap τ ⊤)]
  [---------------------- "O-TopLhs"
   (overlap ⊤ τ)]
  [---------------------- "O-Abs"
   (overlap ([x_1 : σ_1] ..._n → τ_1 (ψ_1+ ∣ ψ_1-))
            ([x_2 : σ_2] ..._n → τ_2 (ψ_2+ ∣ ψ_2-)))]
  [(overlap σ_1 τ)
   ---------------------- "O-UnionL"
   (overlap (U σ_0 ... σ_1 σ_2 ...) τ)]
  [(overlap σ τ_1)
   ---------------------- "O-UnionR"
   (overlap σ (U τ_0 ... τ_1 τ_2 ...))]
  [(overlap σ τ)
   ---------------------- "O-RefineL"
   (overlap {x : σ ∣ ψ} τ)]
  [(overlap σ τ)
   ---------------------- "O-RefineR"
   (overlap σ {x : τ ∣ ψ})])


;; *********************************************************
;; overlap tests
(module+ test
  (test*-true (overlap Int Int))
  (test*-true (overlap Int ⊤))
  (test*-true (overlap ⊤ Int))
  (test*-false (overlap Int ♯T))
  (test*-true (overlap Int (U Int ♯T)))
  (test*-true (overlap (U Int ♯T) Int))
  (test*-false (overlap Bool Int))
  (test*-false (overlap Int Bool))
  (test*-true (overlap Int {i : Int ∣ tt}))
  (test*-true (overlap {i : Int ∣ tt} Int))
  (test*-true (overlap ([x : Bool] → Bool (ff ∣ tt))
                       ([y : Int] → Int (tt ∣ ff)))))

(define-metafunction DTR
  Δ: : ψ ... -> Δ
  [(Δ: ψ ...) (() () ,(list->dot-list (term (ψ ...))))])

(define-metafunction DTR
  Γ: : (x : τ) ... -> Δ
  [(Γ: (x : τ) ...) (() ,(list->dot-list (term ((x : τ) ...))) ())])

(define-metafunction DTR
  Δ* : ψ ... -> Δ
  [(Δ* ψ ...)
   (() () ,(list->dot-list (shuffle (term ((,(gensym) ~ Int)
                                           (,(gensym) ~ Bool)
                                           (,(gensym) ¬ Int)
                                           (,(gensym) ¬ Bool)
                                           ((,(gensym) ~ Bool)
                                            ∨ (,(gensym) ~ Int))
                                           ((,(gensym) ~ Bool)
                                            ∧ (,(gensym) ~ Int))
                                           (,(gensym) ⇒ ,(gensym))
                                           (,(gensym) ≤ ,(gensym))
                                           tt tt tt tt ψ ...)))))])


;; TODO replace ext w/ ext-Δ
;; and ext-Γ
(define-metafunction DTR
  ext-Δ : Δ ψ ... -> Δ
  [(ext-Δ [Φ Γ Ψ]) [Φ Γ Ψ]]
  [(ext-Δ [Φ Γ Ψ] ψ ψ_rst ...)
   (ext-Δ [Φ Γ (ψ · Ψ)] ψ_rst ...)])

(define-metafunction DTR
  ext-Γ : Γ (x : τ) ... -> Γ
  [(ext-Γ Γ) Γ]
  [(ext-Γ Γ (x : τ) any_rst ...)
   (ext-Γ ((x : τ) · Γ) any_rst ...)])


(define-judgment-form DTR
  #:mode (subtype I I I)
  #:contract (subtype Δ τ τ)
  [--------------------- "S-Refl"
   (subtype Δ τ τ)]

  [--------------------- "S-Top"
   (subtype Δ τ ⊤)]

  [(subtype Δ σ τ) ...
   --------------------- "S-UnionSub"
   (subtype Δ (U σ ...) τ)]
  
  [(subtype Δ σ τ)
   --------------------- "S-UnionSuper"
   (subtype Δ σ (U τ_l ... τ τ_r ...))]

  [(subtype Δ σ τ)
   --------------------- "S-RefineWeaken"
   (subtype Δ {x : σ ∣ ψ} τ)]
  
  [(where/hidden #f (subtype [Φ Γ Ψ] σ τ))
   (where y (fresh-var [Φ Γ Ψ] x))
   (proves [Φ ((y : σ) · Γ) ((subst ψ ([x ↦ y])) · Ψ)]
           (y ~ τ))
   --------------------- "S-RefineSub"
   (subtype [Φ Γ Ψ] {x : σ ∣ ψ} τ)]

  [(where y (fresh-var [Φ Γ Ψ] x))
   (where Γ_y ((y : σ) · Γ))
   (proves [Φ Γ_y Ψ] (y ~ τ))
   (proves [Φ Γ_y Ψ] (subst ψ ([x ↦ y])))
   --------------------- "S-RefineSuper"
   (subtype [Φ Γ Ψ] σ {x : τ ∣ ψ})]

  [(subtype [Φ Γ Ψ] σ_2 σ_1) ...
   (where (y ...) (fresh-vars [Φ Γ Ψ] (x_1 ...)))
   (where Γ_σ (ext-Γ Γ (y : σ_2) ...))
   (subtype [Φ Γ_σ Ψ]
            (subst τ_1 ([x_1 ↦ y] ...))
            (subst τ_2 ([x_2 ↦ y] ...)))
   (proves [Φ Γ_σ ((subst ψ_1+ ([x_1 ↦ y] ...)) · Ψ)]
           (subst ψ_2+ ([x_2 ↦ y] ...)))
   (proves [Φ Γ_σ ((subst ψ_1- ([x_1 ↦ y] ...)) · Ψ)]
           (subst ψ_2- ([x_2 ↦ y] ...)))
   --------------------- "S-Fun"
   (subtype [Φ Γ Ψ]
            ([x_1 : σ_1] ..._n → τ_1 (ψ_1+ ∣ ψ_1-))
            ([x_2 : σ_2] ..._n → τ_2 (ψ_2+ ∣ ψ_2-)))])


;; **************************************************************
;; subtyping tests (basic (i.e. no 'proves' usage)
(module+ test
  ;; simple subtype tests
  (test*-true (subtype mt-Δ ⊥ ⊤))
  (test*-false (subtype mt-Δ ⊤ ⊥))
  (test*-true (subtype mt-Δ ⊥ Int))
  (test*-true (subtype mt-Δ Int Int))
  (test*-false (subtype mt-Δ Int ⊥))
  (test*-true (subtype mt-Δ Int ⊤))
  (test*-true (subtype mt-Δ Int ⊤))
  (test*-true (subtype mt-Δ Int (U Int Bool)))
  (test*-false (subtype mt-Δ (U Int Bool) Int))
  (test*-false (subtype mt-Δ (U Int Bool) ♯F))
  (test*-true (subtype mt-Δ ♯F (U Int Bool)))

  ;; function subtyping
  ;;; reflexivity
  (test*-true (subtype mt-Δ
                       (→ Int (tt ∣ ff))
                       (→ Int (tt ∣ ff))))
  (test*-true (subtype mt-Δ
                       ([x : ⊤] → {b : Bool ∣ (x ~ ⊤)} ((x ~ Int) ∣ (x ¬ Int)))
                       ([y : ⊤] → {a : Bool ∣ (y ~ ⊤)} ((y ~ Int) ∣ (y ¬ Int)))))
  
  ;;; contravariant on domain
  (test*-true (subtype mt-Δ
                       ([x : ⊤] → ⊤ (ff ∣ ff))
                       ([x : ⊥] → ⊤ (tt ∣ tt))))
  (test*-false (subtype mt-Δ
                        ([x : Int] → Int (tt ∣ ff))
                        ([x : ⊤] → Int (tt ∣ ff))))
  (test*-true (subtype mt-Δ
                       ([a : ⊤] [b : (U Int Bool)] → Int (tt ∣ ff))
                       ([x : Int] [y : Int] → Int (tt ∣ ff))))
  (test*-false (subtype mt-Δ
                        ([a : ⊤] [b : Bool] → Int (tt ∣ ff))
                        ([x : Int] [y : Int] → Int (tt ∣ ff))))

  ;;; covariant on range
  (test*-true (subtype mt-Δ
                       (→ Int (tt ∣ ff))
                       (→ (U Int Bool) (tt ∣ ff))))
  (test*-false (subtype mt-Δ
                        (→ (U Int Bool) (tt ∣ ff))
                        (→ Int (tt ∣ ff))))
  (test*-true (subtype mt-Δ
                       ([x : Int] → Int (tt ∣ ff))
                       ([y : Int] → (U Int Bool) (tt ∣ ff))))
  (test*-false (subtype mt-Δ
                        ([x : Int] → (U Int Bool) (tt ∣ ff))
                        ([y : Int] → Int (tt ∣ ff))))

  ;;; matching number of args
  (test*-false (subtype mt-Δ
                        (→ Int (tt ∣ ff))
                        ([x : ⊤] → Int (tt ∣ ff))))
  (test*-false (subtype mt-Δ
                        ([x : ⊥] → Int (tt ∣ ff))
                        (→ Int (tt ∣ ff))))

  ;; subtyping w/ populated Δ
  )



;;-------------------------------------------------------------
;; restrict
;; computes τ ∩ σ more or less
(define-metafunction DTR
  restrict : Δ τ σ -> τ
  [(restrict Δ τ σ) ⊥
   (where #false (overlap τ σ))]
  [(restrict Δ (U τ ...) σ) (Un (restrict Δ τ σ) ...)]
  [(restrict Δ τ σ) τ
   (judgment-holds (subtype Δ τ σ))]
  [(restrict Δ τ σ) σ])

;;-------------------------------------------------------------
;; remove
;; computes τ - σ more or less
(define-metafunction DTR
  remove : Δ τ σ -> τ
  [(remove Δ τ σ) ⊥
   (judgment-holds (subtype Δ τ σ))]
  [(remove Δ (U τ ...) σ) (Un (remove Δ τ σ) ...)]
  [(remove Δ τ σ) τ])

;; **************************************************************
;; restrict, remove, update tests
(module+ test
  (test*-equal (restrict mt-Δ Int ⊤) Int)
  (test*-equal (restrict mt-Δ Int ⊥) ⊥)
  (test*-equal (restrict mt-Δ ⊤ Int) Int)
  (test*-equal (restrict mt-Δ Int Bool) ⊥)
  (test*-equal (restrict mt-Δ Bool Int) ⊥)
  (test*-equal (restrict mt-Δ Bool (U Int ⊥)) ⊥)
  (test*-equal (restrict mt-Δ Bool (U Int ♯T)) ♯T)
  (test*-equal (restrict mt-Δ (U Int ♯T) Bool) ♯T)
  (test*-equal (restrict mt-Δ (U Int Bool) Int) Int)
  (test*-equal (restrict mt-Δ Int (U Int Bool)) Int)

  (test*-equal (remove mt-Δ Int ⊤) ⊥)
  (test*-equal (remove mt-Δ ⊤ Int) ⊤)
  (test*-equal (remove mt-Δ ⊥ Int) ⊥)
  (test*-equal (remove mt-Δ Int Bool) Int)
  (test*-equal (remove mt-Δ Bool Int) Bool)
  (test*-equal (remove mt-Δ Bool (U Int ⊥)) Bool)
  (test*-equal (remove mt-Δ Bool (U Int ♯T)) ♯F)
  (test*-equal (remove mt-Δ (U Int ♯T) Bool) Int)
  (test*-equal (remove mt-Δ (U Int Bool) Int) Bool)
  (test*-equal (remove mt-Δ Int (U Int Bool)) ⊥))



;; --------------------------------------------------------------
;; fme-unsat
;; Is a linear system unsatisfiable?
(define-judgment-form DTR
  #:mode (fme-unsat I)
  #:contract (fme-unsat Φ)
  [(where #f ,(satisfiable-Φ? (term Φ)))
   --------------
   (fme-unsat Φ)])

;; --------------------------------------------------------------
;; fme-implies
;; Does assuming one linear system imply an inequality?
(define-judgment-form DTR
  #:mode (fme-implies I I)
  #:contract (fme-implies Φ φ)
  [(where #t ,(Φ-implies-φ? (term Φ) (term φ)))
   --------------
   (fme-implies Φ φ)])

;; placeholder function
;; never generates output,
;; but is a placeholder for the math
(define-judgment-form DTR
  #:mode (permutation I O)
  #:contract (permutation Ψ Ψ)
  [(where Ψ_out ,(permute (term Ψ_in)))
   ------------------
   (permutation Ψ_in Ψ_out)])


(define-judgment-form DTR
  #:mode (proves  I I)
  #:contract (proves  Δ ψ)

  [(permutation Ψ Ψ_*)
   (proves [Φ Γ Ψ_*] ψ)
   ---------------------- "L-Perm"
   (proves  [Φ Γ Ψ] ψ)]
  
  [(where/hidden () Ψ)
   (where σ (lookup x Γ))
   (subtype [Φ (sans x Γ) Ψ] σ τ)
   --------------------- "L-Subtype"
   (proves  [Φ Γ Ψ] (x ~ τ))]

  [(where/hidden #t ,(simple-Ψ? (term Ψ)))
   (subtype [Φ Γ Ψ] τ σ)
   --------------------- "L-SubtypeNot"
   (proves  [Φ Γ ((x ¬ σ) · Ψ)] (x ¬ τ))]

  [(where/hidden () Ψ)
   (where σ (lookup x Γ))
   (where #false (overlap σ τ))
   --------------------- "L-NoOverlap"
   (proves  [Φ Γ Ψ] (x ¬ τ))]

  [--------------------- "L-True"
   (proves  Δ tt)]

  [--------------------- "L-False"
   (proves  [Φ Γ (ff · Ψ)] ψ)]

  [(where/hidden () Ψ)
   (where x (id-at-⊥ Γ))
   --------------------- "L-Bot"
   (proves  [Φ Γ Ψ] ψ)]

  [(where/hidden () Ψ)
   (fme-unsat Φ)
   --------------------- "L-Unsat"
   (proves  [Φ Γ Ψ] ψ)]
  
  [(proves [Φ Γ (ψ_l · Ψ)] ψ)
   (proves [Φ Γ (ψ_r · Ψ)] ψ)
   --------------------- "L-OrE"
   (proves  [Φ Γ ((ψ_l ∨ ψ_r) · Ψ)] ψ)]
  
  [(where/hidden #t ,(simple-Δ? (term Δ)))
   (proves Δ ψ_l)
   --------------------- "L-OrI-L"
   (proves  Δ (ψ_l ∨ ψ_r))]

  [(where/hidden #t ,(simple-Δ? (term Δ)))
   (proves Δ ψ_r)
   --------------------- "L-OrI-R"
   (proves  Δ (ψ_l ∨ ψ_r))]

  [(proves [Φ Γ (ψ_l · (ψ_r · Ψ))] ψ)
   --------------------- "L-AndE"
   (proves  [Φ Γ ((ψ_l ∧ ψ_r) · Ψ)] ψ)]

  [(where/hidden #t ,(simple-Δ? (term Δ)))
   (proves Δ ψ_l) (proves Δ ψ_r)
   --------------------- "L-AndI"
   (proves  Δ (ψ_l ∧ ψ_r))]

  [(proves [(φ · Φ) Γ Ψ] ψ)
   --------------------- "L-IneqE"
   (proves  [Φ Γ (φ · Ψ)] ψ)]

  [(where/hidden () Ψ)
   (fme-implies Φ φ)
   --------------------- "L-IneqI"
   (proves  [Φ Γ Ψ] φ)]

  [(where τ (lookup x Γ ⊤))
   (proves (subst [Φ (sans x Γ) ((o ~ τ) · Ψ)] ([x ↦ o]))
           (subst ψ ([x ↦ o])))
   --------------------- "L-Alias"
   (proves  [Φ Γ ((x ⇒ o) · Ψ)] ψ)]

  [--------------------- "L-Identity"
   (proves  Δ (x ⇒ x))]

  [(where/hidden #t ,(simple-Ψ? (term Ψ)))
   (where/hidden x (id-at-refine Γ))
   (where {y : τ ∣ ψ_y} (lookup x Γ))
   (proves [Φ ((x : τ) · Γ) ((subst ψ_y ([y ↦ x])) · Ψ)] ψ) 
   ---------------------------------- "L-RefineIsE"
   (proves  [Φ Γ Ψ] ψ)]
  
  [(where ψ_y- (negate (subst ψ_y ([y ↦ x]))))
   (proves [Φ Γ (((x ¬ τ) ∨ ψ_y-) · Ψ)] ψ)
   ---------------------------------- "L-RefineNotE"
   (proves  [Φ Γ ((x ¬ {y : τ ∣ ψ_y}) · Ψ)] ψ)]
  
  [(where/hidden #t ,(simple-Δ? (term Δ)))
   (proves Δ (x ~ τ))
   (proves Δ (subst ψ_y ([x ↦ y])))
   ---------------------------------- "L-RefineIsI"
   (proves  Δ (x ~ {y : τ ∣ ψ_y}))]
  
  [(where/hidden #t ,(simple-Δ? (term Δ)))
   (where ψ_y- (negate (subst ψ_y ([x ↦ y]))))
   (proves Δ ((x ¬ τ) ∨ ψ_y-))
   ---------------------------------- "L-RefineNotI"
   (proves  Δ (x ¬ {y : τ ∣ ψ_y}))]

  [(where σ (restrict [Φ Γ Ψ] (lookup x Γ ⊤) τ))
   (proves [Φ ((x : σ) · Γ) Ψ] ψ)
   --------------------- "L-Restrict"
   (proves  [Φ Γ ((x ~ τ) · Ψ)] ψ)]

  [(where/hidden #t ,(simple-Ψ? (term Ψ)))
   (where σ (remove [Φ Γ Ψ] (lookup x Γ ⊤) τ))
   (proves [Φ ((x : σ) · Γ) Ψ] ψ)
   --------------------- "L-Remove"
   (proves  [Φ Γ ((x ¬ τ) · Ψ)] ψ)])


;; white box logic tests
(module+ test
  
  ;; L-Subtype
  (test*-true (proves [() ((x : ♯T) · ()) ()] (x ~ Bool)))
  (test*-true (proves (Δ* (x ~ ♯T)) (x ~ Bool)))

  ;; L-SubtypeNot
  (test*-true (proves (Δ: (x ¬ Bool)) (x ¬ ♯T)))
  (test*-true (proves (Δ* (x ¬ Bool)) (x ¬ ♯T)))
  
  ;;L-NoOverlap
  (test*-true (proves [() ((x : Int) · ()) ()] (x ¬ Bool)))
  (test*-true (proves (Δ* (x ~ Int)) (x ¬ Bool)))
  
  ;;L-True
  (test*-true (proves (Δ:) tt))
  (test*-true (proves (Δ*) tt))

  ;;L-False
  (test*-true (proves (Δ: ff) ff))
  (test*-true (proves (Δ* ff) ff))
  
  ;;L-Bot
  (test*-true (proves [() ((x : ⊥) · ()) ()] ff))
  (test*-true (proves (Δ* (x ~ ⊥)) ff))
  
  ;;L-Unsat
  (test*-false (proves (Δ: (x ≤ y) (x ≤ z)) ff))
  (test*-true (proves (Δ: (x ≤ y) ((1 ⊕ y) ≤ x)) ff))
  (test*-true (proves (Δ* (x ≤ y) ((1 ⊕ y) ≤ x)) ff))
  
  ;;L-OrE
  (test*-true (proves (Δ: ((x ~ Int) ∨ (x ~ Bool))) (x ~ (U Int Bool))))
  (test*-true (proves (Δ: ((x ~ Int) ∨ ff)) (x ~ (U Int Bool))))
  (test*-true (proves (Δ: (x ¬ Int) ((x ~ Int) ∨ ff)) (x ~ (U Int Bool))))
  (test*-true (proves (Δ: tt ((x ~ Int) ∨ ff) (x ¬ Int)) (x ~ (U Int Bool))))
  (test*-true (proves (Δ: (y ~ Int) (((x ~ ⊤) ∧ (y ¬ Int)) ∨ (x ~ ♯T)))
                      (x ~ (U Int Bool))))
  
  ;;L-OrI-L && L-OrI-R
  (test*-true (proves (Δ: (x ~ Int)) ((x ~ Int) ∨ (x ¬ Bool))))
  (test*-true (proves (Δ: (x ~ Int)) ((x ~ Int) ∨ ff)))
  (test*-false (proves (Δ: (x ~ Int)) ((x ~ Bool) ∨ ff)))
  (test*-true (proves (Δ: (x ~ Int)) ((ff ∨ (x ¬ Bool)) ∨ ff)))
  (test*-true (proves (Δ: (x ~ Int)) (tt ∨ ((x ~ Bool) ∨ (x ~ ⊥)))))

  ;;L-AndE
  (test*-true (proves (Δ: ((x ~ (U Int ♯T)) ∧ (x ~ (U Int ♯F)))) (x ~ Int)))
  (test*-true (proves (Δ: ((x ~ (U Int Bool)) ∧ (x ¬ Bool))) (x ~ Int)))
  (test*-true (proves (Δ: (tt ∧ ((x ~ (U Int Bool)) ∧ (x ¬ Bool))) tt) (x ~ Int)))
  (test*-true (proves (Δ: (((ff ∧ tt) ∧ (x ¬ Bool)) ∧ tt) tt) (x ~ ⊥)))

  ;;L-AndI
  (test*-true (proves (Δ: (x ~ Int)) ((x ~ Int) ∧ (x ¬ Bool))))
  (test*-true (proves (Δ: (x ~ Int)) (((x ~ Int) ∧ (x ¬ Bool)) ∧ tt)))
  (test*-false (proves (Δ: (x ~ Int)) (((x ~ Int) ∧ (x ¬ Bool)) ∧ ff)))

  ;;L-IneqE
  (test*-true (proves (Δ: (x ≤ y) (y ≤ z)) (x ≤ z)))
  (test*-true (proves (Δ* (x ≤ y) (y ≤ z)) (x ≤ z)))
  (test*-false (proves (Δ* (x ≤ y) (y ≤ z)) (z ≤ x)))
  
  
  ;;L-IneqI
  (test*-true (proves (Δ: (6 ≤ (2 ⊗ x)) (x ≤ y)) (2 ≤ y)))
  (test*-true (proves (Δ* (6 ≤ (2 ⊗ x)) (x ≤ y)) (3 ≤ y)))
  (test*-false (proves (Δ: (6 ≤ (2 ⊗ x)) (x ≤ y)) (4 ≤ y)))
  (test*-false (proves (Δ* (6 ≤ (2 ⊗ x)) (x ≤ y)) (4 ≤ y)))
  
  ;;L-Alias
  (test*-true (proves (Δ: (x ~ Int) (x ⇒ y)) (x ~ Int)))
  (test*-true (proves (Δ* (x ~ Int) (x ⇒ y)) (x ~ Int)))
  (test*-true (proves (Δ: (x ~ Int) (x ⇒ y)) (y ~ Int)))
  (test*-true (proves (Δ* (x ~ Int) (x ⇒ y)) (y ~ Int)))
  (test*-true (proves (Δ: (x ~ (U Bool Int)) (x ⇒ y) (x ~ ♯T) (y ~ ♯F))
                      (y ~ Int)))
  
  ;;L-Identity
  (test*-true (proves (Δ:) (x ⇒ x)))
  (test*-true (proves (Δ*) (x ⇒ x)))
  (test*-false (proves (Δ:) (x ⇒ y)))
  (test*-false (proves (Δ*) (x ⇒ y)))
  
  ;;L-RefineIsE
  (test*-true (proves (Δ: (z ~ (x : Int ∣ ((x ≤ 42) ∧ (42 ≤ x)))))
                      (z ~ {i : Int ∣ (= i 42)})))
  (test*-true (proves (Δ: (x ¬ Int)
                          (x ~ (U Int {y : Bool ∣ (q ~ Int)})))
                      (q ~ Int)))
  (test*-true (proves (Δ* (x ~ (U Int {y : Bool ∣ (q ~ Int)}))
                          (x ¬ Int))
                      (q ~ Int)))
  
  ;;L-RefineNotE
  (test*-true (proves (Δ: (x ¬ {y : Int ∣ (q ~ Int)}))
                      ((x ¬ Int) ∨ (q ¬ Int))))
  (test*-true (proves (Δ* (x ¬ {y : Int ∣ (q ~ Int)}))
                      ((x ¬ Int) ∨ (q ¬ Int))))
  
  ;;L-RefineIsI
  (test*-true (proves (Δ: (x ~ Int) (q ~ Int))
                      (x ~ {y : Int ∣ (q ~ Int)})))
  (test*-true (proves (Δ* (x ~ Int) (q ~ Int))
                      (x ~ {y : Int ∣ (q ~ Int)})))
  ;;L-RefineNotI
  (test*-true (proves (Δ: ((x ¬ Int) ∨ (q ¬ Int)))
                      (x ¬ {y : Int ∣ (q ~ Int)})))
  (test*-true (proves (Δ* ((x ¬ Int) ∨ (q ¬ Int)))
                      (x ¬ {y : Int ∣ (q ~ Int)})))

  
  ;;L-Restrict
  (test*-true (proves (Δ: (x ~ ⊤) (x ~ (U Int ♯T)) (x ~ (U Int ♯F))) (x ~ Int)))
  (test*-false (proves (Δ: (x ~ (U Int ♯T)) (x ~ (U Int ♯F))) (x ~ ♯T)))
  (test*-true (proves (Δ: (y ~ ⊤) (z ¬ ⊥) (x ~ ⊤) tt (x ~ (U Int ♯T)) (x ~ (U Int ♯F)) (z ~ ⊤))
                      (x ~ Int)))
  ;;L-Remove
  (test*-true (proves (Δ: (x ~ (U Int Bool)) (x ¬ Bool)) (x ~ Int)))
  (test*-true (proves (Δ: (y ~ ⊤) (z ¬ ⊥) (x ~ (U Int Bool)) tt (x ¬ ♯T) tt (x ¬ ♯F))
                      (x ~ Int)))
  
  )

;; Logic tests (black box)
(module+ test
  ;; sound
  (test*-false (proves mt-Δ (x ~ ⊤)))
  (test*-false (proves mt-Δ ff))
  (test*-false (proves (Δ:) (tt ∧ ff)))
  (test*-false (proves (Δ:) (ff ∧ tt)))
  (test*-false (proves (Δ:) (ff ∨ ff)))
  ;; simple logic tests
  ;; ex falso, bot 
  (test*-true (proves (Δ: ff) (x ~ Int)))
  (test*-true (proves (Δ* ff) (x ~ Int)))
  (test*-true (proves (Δ* ff) ff))
  (test*-true (proves (Δ* (x ~ ⊥)) ff))
  ;; trivial tautologies
  (test*-true (proves mt-Δ tt))
  (test*-true (proves (Δ*) tt))
  (test*-true (proves (Δ*) (tt ∧ tt)))
  (test*-true (proves (Δ*) (tt ∨ ff)))
  (test*-true (proves (Δ*) (ff ∨ tt)))
  ;; P -> P  (more or less)
  (test*-true (proves (Δ* (x ~ Int)) (x ~ Int)))
  (test*-true (proves (Δ* (x ¬ Int)) (x ¬ Int)))
  
  )



;; complex subtyping (i.e. needs logic)
(module+ test

  ;; refinement subtype
  (test*-true (subtype mt-Δ {a : Int ∣ tt} Int))
  (test*-false (subtype mt-Δ {a : Bool ∣ tt} Int))
  (test*-true (subtype mt-Δ {a : ⊤ ∣ (a ~ Int)} Int))
  (test*-true (subtype mt-Δ {a : (U Int Bool) ∣ (a ¬ Bool)} Int))
  (test*-true (subtype mt-Δ {a : (U Int Bool) ∣ ff} ⊥))
  
  ;; refinement supertype
  (test*-true (subtype mt-Δ Int {a : Int ∣ tt}))
  (test*-false (subtype mt-Δ Int {a : Bool ∣ tt}))
  (test*-true (subtype mt-Δ Int {a : ⊤ ∣ (a ~ Int)}))
  (test*-false (subtype mt-Δ Int {a : Int ∣ ff}))
  
  ;; refinement/refinement subtyping
  (test*-true (subtype mt-Δ {a : Int ∣ tt} {a : Int ∣ tt}))
  (test*-true (subtype mt-Δ {a : Int ∣ (x ~ Int)} {a : Int ∣ (x ~ Int)}))
  (test*-true (subtype mt-Δ
                       {a : Int ∣ ((y ~ Int) ∧ (x ~ Int))}
                       {a : Int ∣ (x ~ Int)}))
  (test*-true (subtype mt-Δ
                       (x : Int ∣ ((x ≤ 42) ∧ (42 ≤ x)))
                       {i : Int ∣ (= i 42)}))
  (test*-false (subtype mt-Δ
                       {a : Int ∣ (x ~ Int)}
                       {a : Int ∣ ((y ~ Int) ∧ (x ~ Int))}))

  ;; functions w/ complex props
  (test*-false (subtype mt-Δ
                        ([x : ⊤] → Bool (tt ∣ tt))
                        ([x : ⊤] → Bool (tt ∣ ff))))
  (test*-true (subtype mt-Δ
                        ([x : ⊤] → Bool (tt ∣ ff))
                        ([x : ⊤] → Bool (tt ∣ ff))))
  (test*-false (subtype mt-Δ
                        ([x : ⊤] → Bool (tt ∣ tt))
                        ([x : ⊤] → Bool ((x ~ Int) ∣ tt))))
  (test*-true (subtype mt-Δ
                       ([x : ⊤] → Bool ((x ~ Int) ∣ tt))
                       ([y : ⊤] → Bool ((y ~ Int) ∣ tt))))

  ;; refinement w/ non-empty env
  (test*-true (subtype (Δ: (x ~ Int)) Int {a : Int ∣ ((a ~ Int) ∧ (x ~ Int))}))
  (test*-false (subtype (Δ: (x ~ ⊤)) Int {a : Int ∣ ((a ~ Int) ∧ (x ~ Int))}))
  
  ;; function w/ non-empty env
  (test*-true (subtype (Δ: (y ~ Int))
                       ([x : ⊤] → Bool ((x ~ Int) ∣ tt))
                       ([z : ⊤] → Bool (((y ~ Int) ∧ (z ~ Int)) ∣ (y ~ Int)))))
  (test*-false (subtype (Δ: (y ~ ⊤))
                        ([x : ⊤] → Bool ((x ~ Int) ∣ tt))
                        ([x : ⊤] → Bool (((y ~ Int) ∧ (x ~ Int)) ∣ (y ~ Int))))))

;; Ψ -> (Ψ ...)
(define (permute Ψ)
  (match Ψ
    ;; empty? leave it alone, return #f
    [(list) #f]
    ;; (tt · rst), skip tt
    [`(,(? tt?) · ,Ψ-rest)
     Ψ-rest]
    ;; proposition that can be worked with at the head,
    ;; just leave it alone, return #f
    [`(,(or (? ff?)
            (? φ?)
            (? is?)
            (? alias?)
            (? conj?)
            (? disj?))
       · ,Ψ-rest)
     #f]
    ;; there's a not-type at the front... lets double check
    ;; if other stuff needs to go first etc
    [`(,(? not?) · ,Ψ-rest)
     (define props (dot-list->list Ψ))
     (cond
       ;; contains ⊥, quick bail
       [(ormap ff? props) (term (ff · ()))]
       ;; it's all already nots, don't touch it
       [(andmap not? props) #f]
       ;; okay, time to shuffle the list
       [else
        (define actual-props (filter-not tt? props))
        (define-values (nots not-nots)
          (partition not? actual-props))
        (list->dot-list (append not-nots nots))])]
    [_ (error 'permute "unaccounted for case! ~a" Ψ)]))
