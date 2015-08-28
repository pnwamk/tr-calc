#lang racket
;; dtr-elim.rkt
;;----------------------------------------------------------------------
;; Provides a metafunction (elim-ids) for eliminating variables
;; from propositions while maintaining all relevant info about the
;; remaining variables. This is done by
;; (1) converting the proposition into disjunctive normal form (DNF)
;; (2) removing trivial/contradictory clauses
;; (3) removing the variables being eliminated by trivializing
;;     propositions in which they are the direct object
;;     (e.g. eliminating x from the proposition (x ~ Int) produces tt,
;;           whereas eliminating x from the proposition
;;           (y ~ {i : Int ∣ (i ≤ x)}) produces (y ~ {i : Int ∣ tt})
;;----------------------------------------------------------------------

(require redex
         "dtr-lang.rkt"
         "dtr-scope.rkt"
         "dtr-subst.rkt"
         "dtr-subtype.rkt"
         "dtr-fme.rkt"
         "utils.rkt")

;; normal form for a DNF clause
(struct clause (sli ts nts als) #:transparent)
;; sli - list of φ OR set of leq
;;       (they start out a list, and later during computation we
;;        convert it into a set for computational purposes)
;; ts - type env (map of id -> type)
;; nts - negative type env (map of id -> (listof type))
;; als - aliases (map of id -> id)
(define trivial-clause (clause (list) (hash) (hash) (hash)))

;;--------------------------------------------------
;; elim-ids
;; eliminates variables from a proposition
;; while attempting to not lose information
;; about the remaining variables
(define-metafunction DTR
  elim-ids : Φ Γ any (x ...) -> any
  [(elim-ids Φ Γ any ()) any]
  ;; ψ
  [(elim-ids Φ Γ ψ (x ...))
   ,(let ([Φ (term Φ)]
          [Γ (term Γ)]
          [ψ (term ψ)]
          [xs (term (x ...))])
      (define t-env (build-type-env Γ))
      (define ineq-env (Φ->sli Φ))
      (define list-of-disjuncts
        ;; first, convert to dnf
        (let* ([dnf (dnf-convert t-env ψ (list trivial-clause))]
               ;; substitute aliases in φs
               [dnf (for/list ([c (in-list dnf)])
                      (match-define (clause φs ts nts als) c)
                      (clause (for/list ([φ (in-list φs)])
                                (for/fold ([φ φ]) ([(x y) (in-hash als)])
                                  (term (subst ,φ ([,x ↦ ,y])))))
                              ts
                              nts
                              als))]
               ;; convert φs into sets in each clause
               [dnf (for/list ([c (in-list dnf)])
                      (match-define (clause φs ts nts als) c)
                      (clause (for/set ([φ (in-list φs)]) (φ->leq φ))
                              ts
                              nts
                              als))]
               ;; remove disjuncts w/ unsatisfiable linear constraints
               [dnf (filter-not (unsat-sli-in-clause? ineq-env) dnf)]
               ;; use fme elimination to remove vars from slis
               [dnf (map (elim-in-clause-sli xs) dnf)])
          dnf))
      ;; rebuild a redex proposition
      (define prop (cond
                     [(empty? list-of-disjuncts) (term ff)]
                     [(for/fold ([prop (finalized-clause->ψ (first list-of-disjuncts))])
                                ([d (in-list (rest list-of-disjuncts))])
                        `(,(finalized-clause->ψ d) ∨ ,prop))]))
      ;; eliminate vars
      (term (vaporize-vars ,prop ,xs)))]
  ;; function type
  [(elim-ids Φ Γ ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (y ...))
   ([x : (elim-ids Φ Γ σ (x ...))] ...
    →
    (elim-ids Φ Γ_* τ (z ...))
    ((elim-ids Φ Γ_* ψ_+ (z ...))
     ∣ (elim-ids Φ Γ_* ψ_- (z ...))))
   (where Γ_* (ext Γ (x : σ) ...))
   (where (z ...) ,(set-subtract (term (y ...)) (term (x ...))))]
  ;; refinement type
  [(elim-ids Φ Γ {x : τ ∣ ψ} (y ...))
   {x : (elim-ids Φ Γ τ (y ...)) ∣ (elim-ids Φ Γ ψ (z ...))}
   (where (z ...) ,(set-remove (term (y ...)) (term x)))])

;;--------------------------------------------------
;; finalized-clause->ψ
;; converts a disjunct (one of the atoms or conjuctions
;; in a dnf representation) into it's redex equivalent
(define/contract (finalized-clause->ψ d)
  (-> clause? ψ?)
  (match-define (clause s ts nts als) d)
  (define ineq-props (set-map s leq->φ))
  (define pos-props (hash-map ts (λ (x t) `(,x ~ ,t))))
  (define neg-props (hash-map nts negative-type-clause))
  (define alias-props (hash-map als (λ (x o) `(,x ⇒ ,o))))
  
  (-and (append pos-props neg-props ineq-props alias-props)))

;;--------------------------------------------------
;; negative-type-clause
;; Build a redex ψ for a single identifier x from a hash
;; table of negative type info about identifiers
(define (negative-type-clause x x-nts)
  (cond
    [(empty? x-nts) (term tt)]
    [else
     (for/fold ([prop `(,x ¬ ,(first x-nts))])
               ([t (in-list (rest x-nts))])
       `((,x ¬ ,t) ∧ ,prop))]))

;; and w/ standard simplifications
(define (-and ps)
  (let ([ps (filter-not tt? ps)])
    (cond
      [(empty? ps) (term tt)]
      [(ormap ff? ps) (term ff)]
      [else
       (for/fold ([p (first ps)])
                 ([q (in-list (rest ps))])
         `(,q ∧ ,p))])))

;;--------------------------------------------------
;; mmap : (α -> β) (listof (α or #f)) -> (listof β)
;; like map but filters out #f values in the list
(define/contract (mmap f l)
  (-> procedure? list? list?)
  (match l
    [(list) (list)]
    [(cons x xs)
     (if x
         (cons (f x) (mmap f xs))
         (mmap f xs))]))

;;--------------------------------------------------
;; build-type-env
;; takes a redex Γ and turns it into a hash table
(define/contract (build-type-env Γ)
  (-> Γ? hash?)
  (for/fold ([env (hash)])
            ([type-entry (in-list (dot-list->list Γ))])
    (match-define `(,x : ,ty) type-entry)
    (define (update old-ty)
      (term (restrict mt-Δ ,old-ty ,ty)))
    (hash-update env x update (term ⊤))))


;;--------------------------------------------------
;; update-disj+ : Γ o τ -> disj -> (disj or #f)
;; takes an obj and type, returns function which
;; updates a disj with the fact that o is of type τ
(define ((update-disj+ t-env o t) d)
  (match-define (clause φs ts nts als) d)
  (let ([o (hash-ref als o (const o))])
    (define o-nts (hash-ref nts o (const empty)))
    (define old-t (hash-ref t-env o (const (term ⊤))))
    (define o-t* (for/fold ([t (let ([ts-t (hash-ref ts o (const (term ⊤)))])
                                 (term (restrict mt-Δ (restrict mt-Δ ,old-t ,ts-t) ,t)))])
                           ([nt (in-list o-nts)])
                   (term (remove mt-Δ ,t ,nt))))
    (define o-nts* (filter (λ (nt) (term (overlap ,nt ,o-t*)))
                           o-nts))
    (cond
      [(term (subtype mt-Δ ,o-t* ⊥)) #f]
      [else (clause φs
                    (hash-set ts o o-t*)
                    (if (empty? o-nts*)
                        (hash-remove nts o)
                        (hash-set nts o o-nts*))
                    als)])))

;;--------------------------------------------------
;; update-disj- : Γ o τ -> disj -> (disj or #f)
;; takes an obj and type, returns function which
;; updates a disj with the fact that o is not of type τ
(define ((update-disj- t-env o t) d)
  (match-define (clause φs ts nts als) d)
  (let ([o (hash-ref als o (const o))])
    (define o-t (let ([old-t (hash-ref t-env o (const #f))]
                      [o-ts-t (hash-ref ts o (const #f))])
                  (cond
                    [(not old-t) o-ts-t]
                    [(not o-ts-t) old-t]
                    [else (term (restrict mt-Δ ,o-ts-t ,old-t))])))
    (define o-t* (and o-t (term (remove mt-Δ ,o-t ,t))))
    (define o-nts (hash-ref nts o (const empty)))
    (cond
      [(eq? (term ⊥) o-t*) #f]
      [else (clause φs
                    ts
                    (hash-set nts o (cons t o-nts))
                    als)])))

;;--------------------------------------------------
;; add-φ : φ -> disj -> disj
;; appends an inequality onto the inequality
;; system in the disjunct
(define ((add-φ φ) d)
  (unless (φ? φ) (error 'add-φ "non-φ"))
  (match-define (clause φs ts nts als) d)
  (clause (cons φ φs) ts nts als))

;;--------------------------------------------------
;; add-alias : x x -> clause -> clause
;; appends an alias
(define ((add-alias t-env x y) c)
  (match-define (clause φs ts nts als) c)
  ;; naively update clause w/ negative type info and alias
  (define c*
    (clause (for/list ([φ (in-list φs)]) (term (subst ,φ ([,x ↦ ,y]))))
            ts
            (hash-set nts y (append (hash-ref nts x (const '()))
                                    (hash-ref nts y (const '()))))
            (hash-set als x y)))
  ;; then update positive type info w/ naively added facts present
  ;; if there is type info about x
  (cond
    [(or (hash-has-key? ts x)
         (hash-has-key? nts x))
     ((update-disj+ t-env y (hash-ref ts x (const (term ⊤)))) c*)]
    [else
     c*]))

;;--------------------------------------------------
;; dnf-convert
;; converts a proposition into DNF
;; redex prop, (listof disj) -> (listof disj)
;; any empty list returned means all branches
;; contained ⊥/ff
(define/contract (dnf-convert t-env ψ clauses)
  (-> hash? ψ? (listof clause?) (listof clause?))
  (match ψ
    ['tt clauses]
    ['ff (list)]
    [`(,lhs ∧ ,rhs)
     (filter values (dnf-convert t-env lhs (dnf-convert t-env rhs clauses)))]
    [`(,lhs ∨ ,rhs)
     (filter values (append (dnf-convert t-env lhs clauses)
                            (dnf-convert t-env rhs clauses)))]
    [`(,o ~ ,t) (mmap (update-disj+ t-env o t) clauses)]
    [`(,o ¬ ,t) (mmap (update-disj- t-env o t) clauses)]
    [`(,lhs ≤ ,rhs) (map (add-φ ψ) clauses)]
    [`(,x ⇒ ,o) (mmap (add-alias t-env x o) clauses)]))


;;--------------------------------------------------
;; unsat-sli-in-clause?
;; is a disj's linear system unsatisfiable in
;; the current environment
(define ((unsat-sli-in-clause? ineq-env) d)
  (not (fme-sat? (set-union ineq-env (clause-sli d)))))

;;--------------------------------------------------
;; vaporize-vars
;; i.e. substitution w/ empty-obj like in ICFP 2010
(define-metafunction DTR
  vaporize-vars : any (x ...) -> any
  [(vaporize-vars any ()) any]
  ;; cases to handle specially include the following
  [(vaporize-vars (x ~ τ) (any_1 ... x any_2 ...)) tt]
  [(vaporize-vars (x ¬ τ) (any_1 ... x any_2 ...)) tt]
  [(vaporize-vars (x ⇒ o) (any_1 ... x any_2 ...)) tt]
  [(vaporize-vars (y ⇒ x) (any_1 ... x any_2 ...)) tt]
  [(vaporize-vars φ (x ...))
   tt
   (where #t ,(set-intersect (term (fv φ)) (term (x ...))))]
  ;; function type
  [(vaporize-vars ([x : σ] ... → τ (ψ_+ ∣ ψ_-)) (y ...))
   ([x : (vaporize-vars σ (y ...))] ...
    → (vaporize-vars τ (z ...))
    ((vaporize-vars ψ_+ (z ...))
     ∣
     (vaporize-vars ψ_- (z ...))))
   (where (z ...) ,(set-subtract (term (y ...)) (term (x ...))))]
  ;; refinement type
  [(vaporize-vars {x : τ ∣ ψ} (y ...))
   {x : (vaporize-vars τ (y ...))
      ∣ (vaporize-vars ψ (z ...))}
   (where (z ...) ,(set-subtract (term (y ...)) (term (x))))]
  ;; syntactic list
  [(vaporize-vars (any ...) (any_vars ...))
   ((vaporize-vars any (any_vars ...)) ...)]
  ;; other (ignore)
  [(vaporize-vars any (any_vars ...)) any])


(define ((elim-in-clause-sli xs) c)
  (match-define (clause s ts nts als) c)
  (clause (fme-elim-vars s xs) ts nts als))

(define-judgment-form DTR
  #:mode (logically-equivalent I I)
  #:contract (logically-equivalent ψ ψ)
  [(proves (Δ: ψ_1) ψ_2)
   (proves (Δ: ψ_2) ψ_1)
   -------------------------------
   (logically-equivalent ψ_1 ψ_2)])

(module+ test
  ;; basic examples
  (test*-equal (elim-ids () () tt ()) tt)
  (test*-equal (elim-ids () () ff ()) ff)
  (test*-equal (elim-ids () () ((y ~ Int) ∧ (y ¬ Int)) (y)) ff)
  (test*-equal (elim-ids () () tt (x y)) tt)
  (test*-equal (elim-ids () () (x ~ Int) ())
               (x ~ Int))
  (test*-equal (elim-ids () () (x ~ Int) (y))
               (x ~ Int))
  (test*-equal (elim-ids () () (x ¬ Int) ())
               (x ¬ Int))
  (test*-true (logically-equivalent
               (elim-ids () () (x ¬ Int) (y))
               (x ¬ Int)))
  (test*-true (logically-equivalent
               (elim-ids () () (x ≤ y) ())
               (x ≤ y)))
  (test*-true (logically-equivalent
               (elim-ids () () (x ≤ y) (z))
               (x ≤ y)))
  (test*-true (logically-equivalent
               (elim-ids () () ((x ~ Int) ∧ (y ~ Int)) (y))
               (x ~ Int)))
  (test*-true (logically-equivalent
               (elim-ids () () ((x ~ Int) ∨ (y ~ Int)) (y))
               tt))
  
  ;; examples requiring some logical reasoning
  (test*-true (logically-equivalent
               (elim-ids () () ((x ~ Int) ∨ ((y ~ Int) ∧ (y ¬ Int))) (y))
               (x ~ Int)))
  (test*-true (logically-equivalent
               (elim-ids () () ((x ≤ y) ∧ (y ≤ z)) (y))
               (x ≤ z)))
  
  ;; examples w/ aliasing
  (test*-true (logically-equivalent
               (elim-ids () () ((x ~ Int) ∧ ((y ⇒ x) ∧ (y ~ Bool))) (y))
               ff))
  (test*-true (logically-equivalent
               (elim-ids () () (((x ~ (U Int Bool))
                                 ∧ ((y ⇒ x) ∧ (y ~ Bool)))
                                ∧ ((z ⇒ y) ∧ (z ¬ ♯F)))
                         (y z))
               (x ~ ♯T)))
  (test*-true (logically-equivalent
               (elim-ids () () (((x ≤ y) ∧ (y ≤ q))
                                ∧ (q ⇒ z)) (y q))
               (x ≤ z)))
  (test*-false (logically-equivalent
                (elim-ids () () (((x ≤ y) ∧ (y ≤ q))
                                 ∧ (q ⇒ z)) (y q))
                (z ≤ x)))
  ;; simple examples in types
  
  ;; examples in types
  ) ;; end of test module



