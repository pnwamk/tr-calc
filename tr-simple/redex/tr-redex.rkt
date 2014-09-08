#lang racket

(require redex rackunit)

(define-language λTR
  [n   ::= integer]
  [b   ::= boolean]
  [x   ::= variable-not-otherwise-mentioned]
  [e   ::= x (e e) (λ (x : τ) e) (if e e e) c true false n]
  [c   ::= Add1 Zero? Num? Bool? Proc?]
  [o   ::= x]
  [oo  ::= o Null]
  [τ   ::= Top Int T F (U τ ...) (λ ([x : τ] ψ ψ oo) : τ)]
  [ψ   ::= (o -: τ) (o -! τ) (ψ AND ψ) (ψ OR ψ) TT FF]
  [Γ   ::= [ψ ...]])

(define-extended-language λTR-vl
  λTR
  [vl  ::= (vars x ...)])

(define-metafunction λTR-vl 
  app : vl ... vl -> vl
  [(app (vars x_1 ...) (vars x_2 ...))
   (vars x_1 ... x_2 ...)]
  [(app (vars x_1 ...) (vars x_2 ...) (vars x_3 ...) ...)
   (app (app (vars x_1 ...) (vars x_2 ...)) (vars x_3 ...) ...)])

(define-judgment-form λTR
  #:mode (is-U I)
  #:contract (is-U τ)
  [-------------- "IsUnion"
   (is-U (U τ_1 ...))])

(check-false (judgment-holds (is-U Int)))
(check-true (judgment-holds (is-U (U))))
(check-true (judgment-holds (is-U (U Int))))

(define-judgment-form λTR
  #:mode (non-U I)
  #:contract (non-U τ)
  [(where #f (is-U τ_1))
   -------------- "NonU"
   (non-U τ_1)])

(define-judgment-form λTR
  #:mode (nested-U I)
  #:contract (nested-U τ)
  [-------------- "IsUnion"
   (nested-U (U τ_1 ... (U τ_2 ...) τ_3 ...))])

(check-false (judgment-holds (nested-U Int)))
(check-false (judgment-holds (nested-U (U))))
(check-false (judgment-holds (nested-U (U T F))))
(check-true (judgment-holds (nested-U (U T F (U)))))
(check-true (judgment-holds (nested-U (U T (U F)))))

(define-judgment-form λTR
  #:mode (atomic-U I)
  #:contract (atomic-U τ)
  [-------------- "Atomic-U"
   (atomic-U (U τ_1))])

(define-judgment-form λTR
  #:mode (redundant-U I)
  #:contract (redundant-U τ)
  [-------------- "Redundant-U"
   (redundant-U (U τ_1 ... τ_2 τ_3 ... τ_2 τ_4 ...))])

(check-false (judgment-holds (redundant-U (U))))

(define-judgment-form λTR
  #:mode (flat-type I)
  #:contract (flat-type τ)
  [(where #f (nested-U τ_1))
   -------------- "IsFlat"
   (flat-type τ_1)])

(check-true (judgment-holds (flat-type (U))))

(define-judgment-form λTR
  #:mode (unique-type I)
  #:contract (unique-type τ)
  [(where #f (redundant-U τ_1))
   -------------- "IsFlat"
   (unique-type τ_1)])

(check-true (judgment-holds (unique-type (U))))

(define-judgment-form λTR
  #:mode (not-atomic-U I)
  #:contract (not-atomic-U τ)
  [(where #f (atomic-U τ_1))
   -------------- "IsNotAtomic"
   (not-atomic-U τ_1)])

(check-true (judgment-holds (not-atomic-U (U))))

(define-metafunction λTR
  flatten-type : τ -> τ
  [(flatten-type τ_1) τ_1
   (judgment-holds (unique-type τ_1))
   (judgment-holds (flat-type τ_1))
   (judgment-holds (not-atomic-U τ_1))]
  [(flatten-type (U τ_1)) (flatten-type τ_1)
   (judgment-holds (non-U τ_1))]
  [(flatten-type (U τ_1 ... τ_2 τ_3 ... τ_2 τ_4 ...))
   (flatten-type (U τ_1 ... τ_2 τ_3 ... τ_4 ...))
   (judgment-holds (flat-type (U τ_1 ... τ_2 τ_3 ... τ_2 τ_4 ...)))]
  [(flatten-type (U τ_1 ... (U τ_2 ... ) τ_3 ...)) 
   (flatten-type (U τ_1 ... τ_2 ... τ_3 ...))])

(check-equal? (term (flatten-type (U))) (term (U)))
(check-equal? (term (flatten-type (U T (U F)))) (term (U T F)))
(check-equal? (term (flatten-type (U (U (U (U T))) (U F) (U (U (U)))))) (term (U T F)))


(define-judgment-form λTR-vl
  #:mode (in-vl I I)
  #:contract (in-vl x vl)
  [------------------- "In-vl"
   (in-vl x_2 (vars x_1 ... x_2 x_3 ...))])

(define-metafunction λTR-vl 
  remove-var : x vl -> vl
  [(remove-var x_1 (vars))
   (vars)]
  [(remove-var x_1 (vars x_1 x_2 ...)) (remove-var (vars x_2 ...))]
  [(remove-var x_1 (vars x_2 x_3 ...)) (app (vars x_2) (remove-var (vars x_3 ...)))
   (judgment-holds (!= x_1 x_2))])

(define-metafunction λTR
  NOT : ψ -> ψ
  [(NOT (o -: τ_1)) (o -! τ_1)]
  [(NOT (o -! τ_1)) (o -: τ_1)]
  [(NOT (ψ_1 AND ψ_2)) ((NOT ψ_1) OR (NOT ψ_2))]
  [(NOT (ψ_1 OR ψ_2)) ((NOT ψ_1) AND (NOT ψ_2))]
  [(NOT TT) FF]
  [(NOT FF) TT])

(define-judgment-form λTR
  #:mode (in I I)
  #:contract (in ψ Γ)
  [------------------- "In"
   (in ψ_2 [ψ_1 ... ψ_2 ψ_3 ...])])

(define-judgment-form λTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  ; L-Atom
  [------------------- "L-Atom"
   (proves [ψ_1 ... ψ_2 ψ_3 ...] ψ_2)]
  ; L-True
  [------------------- "L-True"
   (proves Γ_1 TT)]
  ; L-False
  [------------------- "L-False"
   (proves [ψ_1 ... FF ψ_2 ...] ψ_3)]
  ; L-Bot
  [------------------- "L-Bot"
   (proves [ψ_1 ... (o -: (U)) ψ_2 ...] ψ_3)]
  ; L-AndI
  [(proves Γ_1 ψ_1)
   (proves Γ_1 ψ_2)
   ------------------- "L-AndI"
   (proves Γ_1 (ψ_1 AND ψ_2))]
  ; L-AndE
  [(proves [ψ_1 ... ψ_2 ... ψ_3 ψ_4] ψ_5)
   ------------------- "L-AndE"
   (proves [ψ_1 ... (ψ_3 AND ψ_4) ψ_2 ...] ψ_5)]
  ; L-OrI-lhs
  [(proves Γ_1 ψ_1)
   ------------------- "L-OrI-lhs"
   (proves Γ_1 (ψ_1 OR ψ_2))]
  ; L-OrI-rhs
  [(proves Γ_1 ψ_2)
   ------------------- "L-OrI-rhs"
   (proves Γ_1 (ψ_1 OR ψ_2))]
  ; L-OrE
  [(proves [ψ_1 ... ψ_2 ... ψ_3] ψ_5)
   (proves [ψ_1 ... ψ_2 ... ψ_4] ψ_5)
   ------------------- "L-OrE"
   (proves [ψ_1 ... (ψ_3 OR ψ_4) ψ_2 ...] ψ_5)]
  ; L-Sub
  [(subtype τ_1 τ_2)
   ------------------- "L-Sub"
   (proves [ψ_1 ... (o_1 -: τ_1) ψ_2 ...] (o_1 -: τ_2))]
  ; L-SubNot
  [(subtype τ_2 τ_1)
   ------------------- "L-SubNot"
   (proves [ψ_1 ... (o_1 -! τ_1) ψ_2 ...] (o_1 -! τ_2))]
  ; L-Restrict
  [(where #f (in (o_1 -: (update τ_1 #t τ_2)) 
                 [ψ_1 ... (o_1 -: τ_1) ψ_2 ... (o_1 -: τ_2) ψ_3 ...]))
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_1) (o_1 -: (update τ_1 #t τ_2))] ψ_4)
   ------------------- "L-Restrict"
  (proves [ψ_1 ... (o_1 -: τ_1) ψ_2 ... (o_1 -: τ_2) ψ_3 ...] ψ_4)]
  ; L-Remove-lhs
  [(where #f (in (o_1 -: (update τ_1 #f τ_2)) 
                 [ψ_1 ... (o_1 -! τ_2) ψ_2 ... (o_1 -: τ_2) ψ_3 ...]))
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_1) (o_1 -: (update τ_1 #f τ_2))] ψ_4)
   ------------------- "L-Remove-lhs"
  (proves [ψ_1 ... (o_1 -! τ_2) ψ_2 ... (o_1 -: τ_1) ψ_3 ...] ψ_4)]
    ; L-Remove-rhs
  [(where #f (in (o_1 -: (update τ_1 #f τ_2)) 
                 [ψ_1 ...  (o_1 -: τ_1) ψ_2 ... (o_1 -! τ_2) ψ_3 ...]))
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_1) (o_1 -: (update τ_1 #f τ_2))] ψ_4)
   ------------------- "L-Remove-rhs"
  (proves [ψ_1 ...  (o_1 -: τ_1) ψ_2 ... (o_1 -! τ_2) ψ_3 ...] ψ_4)])


(define-judgment-form λTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo_1 oo_1)]
  [------------------- "SO-Top"
   (subobj oo_1 Null)])

(define-judgment-form λTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [------------------- "S-Refl"
   (subtype τ_1 τ_1)]
  [------------------- "S-Top"
   (subtype τ_1 Top)]
  [(subtype τ_1 τ_2) ...
   ------------------- "S-UnionSub"
   (subtype (U τ_1 ...) τ_2)]
  [(subtype τ_1 τ_3)
   ------------------- "S-UnionSuper"
   (subtype τ_1 (U τ_2 ... τ_3 τ_4 ...))]
  [(subtype τ_3 (subst-τ x_2 x_1 τ_1)) (subtype (subst-τ x_2 x_1 τ_2) τ_4) 
   (subobj (subst-oo x_2 x_1 oo_1) oo_2)
   (proves [(subst-ψ x_2 x_1 ψ_1)] ψ_3) (proves [(subst-ψ x_2 x_1 ψ_2)] ψ_4)
   ------------------------------------------ "S-Fun"
   (subtype (λ ([x_1 : τ_1] ψ_1 ψ_2 oo_1) : τ_2)
            (λ ([x_2 : τ_3] ψ_3 ψ_4 oo_2) : τ_4))])

(define-judgment-form λTR
    #:mode (common-val I I)
    #:contract (common-val τ τ)
    [------------------ "CS-Eq"
     (common-val τ_1 τ_1)]
    [------------------ "CS-Top-lhs"
     (common-val Top τ_1)]
    [------------------ "CS-Top-rhs"
     (common-val τ_1 Top)]
    [(common-val τ_2 τ_4)
     ------------------ "CS-U-lhs"
     (common-val (U τ_1 ... τ_2 τ_3 ...) τ_4)]
    [(common-val τ_2 τ_4)
     ------------------ "CS-U-rhs"
     (common-val τ_4 (U τ_1 ... τ_2 τ_3 ...))]
    [------------------ "CS-Abs"
     (common-val (λ ([x_1 : τ_1] ψ_1 ψ_2 oo_1) : τ_2) 
                     (λ ([x_2 : τ_3] ψ_3 ψ_4 oo_2) : τ_4))])


(check-true (judgment-holds (common-val Int Int)))
(check-true (judgment-holds (common-val (U T Int) Int)))
(check-true (judgment-holds (common-val Top Int)))
(check-false (judgment-holds (common-val T Int)))

(define-judgment-form λTR
  #:mode (type-conflict I I)
  #:contract (type-conflict τ τ)
  [(where #f (common-val τ_1 τ_2))
   --------------- "TC"
   (type-conflict τ_1 τ_2)])


(define-metafunction λTR
  update : τ b τ -> τ
  [(update τ_1 #t τ_2) (flatten-type (restrict τ_1 τ_2))]
  [(update τ_1 #f τ_2) (flatten-type (remove τ_1 τ_2))])

; fix judgment-holds common-val clauses
(define-metafunction λTR
  restrict : τ τ -> τ
  [(restrict τ_1 τ_2) (U)
   (judgment-holds (type-conflict τ_1 τ_2))
   (judgment-holds (non-U τ_1))]
  [(restrict τ_1 τ_2) τ_1
   (judgment-holds (subtype τ_1 τ_2))
   (judgment-holds (non-U τ_1))]
  [(restrict τ_1 τ_2) τ_2
   (judgment-holds (common-val τ_1 τ_2))
   (where #f (subtype τ_1 τ_2))
   (judgment-holds (non-U τ_1))]
  [(restrict (U) τ_2) (U)]
  [(restrict (U τ_1) τ_2) (restrict τ_1 τ_2)]
  [(restrict (U τ_1 τ_2 ...) τ_3) (U (restrict τ_1 τ_3) (restrict (U τ_2 ...) τ_3))])

; fix where clauses w/ subtype
(define-metafunction λTR
  remove : τ τ -> τ
  [(remove τ_1 τ_2) (U)
   (judgment-holds (subtype τ_1 τ_2))
   (judgment-holds (non-U τ_1))]
  [(remove τ_1 τ_2) τ_1
   (where #f (subtype τ_1 τ_2))
   (judgment-holds (non-U τ_1))]
  [(remove (U τ_1) τ_2) (remove τ_1 τ_2)]
  [(remove (U τ_1 τ_2 ...) τ_3) (U (remove τ_1 τ_3) (remove (U τ_2 ...) τ_3))])

(check-equal? (term (update Int #t Int)) (term Int))
(check-equal? (term (update Int #t Top)) (term Int))
(check-equal? (term (update Int #t (U))) (term (U)))
(check-equal? (term (update Int #t (U T F Int))) (term Int))
(check-equal? (term (update (U T F) #t (U T Int))) (term T))
(check-equal? (term (update (U (U (U T) F)) #t (U T Int))) (term T))
(check-equal? (term (update Int #f Int)) (term (U)))
(check-equal? (term (update Int #f Top)) (term (U)))
(check-equal? (term (update Int #f (U))) (term Int))
(check-equal? (term (update (U T F Int) #f Int)) (term (U T F)))
(check-equal? (term (update (U T F Int) #f (U T F))) (term Int))
(check-equal? (term (update (U (U (U T F)) (U Int) Int) #f (U (U (U T) F) T F))) (term Int))


(define-metafunction λTR-vl
  free-vars : any -> vl
  ; objects
  [(free-vars Null) (vars)]
  [(free-vars x_1) (vars x_1)]
  ; types
  [(free-vars Top) (vars)]
  [(free-vars Int) (vars)]
  [(free-vars T) (vars)]
  [(free-vars F) (vars)]
  [(free-vars (U)) (vars)]
  [(free-vars (U τ_1 τ_2 ...)) (app (free-vars τ_1) 
                                    (free-vars (U τ_2 ...)))]
  [(free-vars (λ ([x_1 : τ_1] ψ_1 ψ_2 oo_1) : τ_2))
   (app (free-vars τ_1)
        (remove-var x_1 (app (free-vars τ_2)
                             (free-vars ψ_1)
                             (free-vars ψ_2)
                             (free-vars oo_1))))]
  ; props
  [(free-vars TT) (vars)]
  [(free-vars FF) (vars)]
  [(free-vars (x_1 -: τ_1)) (app (vars x_1) (free-vars τ_1))]
  [(free-vars (x_1 -! τ_1)) (app (vars x_1) (free-vars τ_1))]
  [(free-vars (ψ_1 AND ψ_2)) (app (free-vars ψ_1) (free-vars ψ_2))]
  [(free-vars (ψ_1 OR ψ_2)) (app (free-vars ψ_1) (free-vars ψ_2))])

(define-judgment-form λTR
  #:mode (!= I I)
  #:contract (!= any any)
  [------------ "Equal"
   (!= any_!_1 any_!_1)])

(define-metafunction λTR
  subst-oo : oo x oo -> oo
  [(subst-oo oo_1 x_1 Null) Null]
  [(subst-oo Null x_1 x_1) Null]
  [(subst-oo x_3 x_1 x_1) x_3])

(define-metafunction λTR
  subst-ψ : oo x ψ -> ψ
  [(subst-ψ Null x_1 (x_1 -: τ_1)) TT]
  [(subst-ψ Null x_1 (x_1 -! τ_1)) TT]
  [(subst-ψ o_1 x_1 (x_1 -: τ_1)) (o_1 -: (subst-τ o_1 x τ_1))]
  [(subst-ψ o_1 x_1 (x_1 -! τ_1)) (o_1 -! (subst-τ o_1 x τ_1))]
  [(subst-ψ o_1 x_1 (x_2 -: τ_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 τ_1))]
  [(subst-ψ o_1 x_1 (x_2 -! τ_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 τ_1))]
  [(subst-ψ o_1 x_1 (x_2 -: τ_1)) (x_2 -: τ_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 τ_1))]
  [(subst-ψ o_1 x_1 (x_2 -! τ_1)) (x_2 -! τ_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 τ_1))]
  [(subst-ψ oo_1 x_1 (ψ_1 AND ψ_2)) 
   ((subst-ψ oo_1 x_1 ψ_1) AND (subst-ψ oo_1 x_1 ψ_2))]
  [(subst-ψ oo_1 x_1 (ψ_1 OR ψ_2)) 
   ((subst-ψ oo_1 x_1 ψ_1) OR (subst-ψ oo_1 x_1 ψ_2))]
  [(subst-ψ oo_1 x_1 TT) TT]
  [(subst-ψ oo_1 x_1 FF) FF])


(define-metafunction λTR
  subst-τ : oo x τ -> τ
  [(subst-τ oo_1 x_1 Top) Top]
  [(subst-τ oo_1 x_1 Int) Int]
  [(subst-τ oo_1 x_1 T) T]
  [(subst-τ oo_1 x_1 F) F]
  [(subst-τ oo_1 x_1 (U)) (U)]
  [(subst-τ oo_1 x_1 (U τ_1)) (subst-τ oo_1 x_1 τ_1)]
  [(subst-τ oo_1 x_1 (U τ_1 τ_2 τ_3 ...)) 
   (U (subst-τ oo_1 x_1 τ_1)
      (subst-τ oo_1 x_1 (U τ_2 τ_3 ...)))]
  [(subst-τ oo_1 x_1 (λ ([x_1 : τ_1] ψ_1 ψ_2 oo_2) : τ_2))
   (λ ([x_2 : (subst-τ oo_1 x_1 τ_1)] ψ_1 ψ_2 oo_2) : τ_2)]
  [(subst-τ oo_1 x_1 (λ ([x_2 : τ_1] ψ_1 ψ_2 oo_2) : τ_2))
   (λ ([x_2 : (subst-τ oo_1 x_1 τ_1)] 
       (subst-ψ oo_1 x_1 ψ_1) 
       (subst-ψ oo_1 x_1 ψ_2) 
       (subst-oo oo_1 x_1 oo_2)) : (subst-τ oo_1 x_1 τ_2))])



(check-true (judgment-holds (subtype Int Int)))
(check-true (judgment-holds (subtype Int Top)))
(check-true (judgment-holds (subtype (U) Int)))
(check-true (judgment-holds (subtype Int (U Int F))))
(check-true (judgment-holds (subtype (U T F) (U Int T F))))
(check-true (judgment-holds (subtype Int Int)))
(check-false (judgment-holds (subtype (U Int T) Int)))
(check-true (judgment-holds (subtype (U Int Int) Int)))
(check-true (judgment-holds (subtype (U Int Int) (U Int T))))
(check-true (judgment-holds 
             (subtype (λ ([x : Top] (x -: Int) (x -! Int) Null) : (U T F)) 
                      (λ ([y : Top] (y -: Int) (y -! Int) Null) : (U T F)))))
(check-true (judgment-holds 
             (subtype (λ ([x : Top] TT TT Null) : Int) 
                      (λ ([y : Int] TT TT Null) : (U Int T F)))))


(check-false (judgment-holds (proves [ ] FF)))
(check-true (judgment-holds (proves [ ] (NOT FF))))
(check-true (judgment-holds (proves [(x -: Int)] (x -: Int))))
(check-true (judgment-holds (proves [((x -: Int) AND (y -: F))] 
                                    ((y -: F) AND (x -: Int)))))
(check-true (judgment-holds (proves [(x -: Int)] ((x -: Int) OR (x -: (U T F))))))
(check-true (judgment-holds (proves [(((z -: (U)) OR FF) OR (x -: Int))
                                     ((x -! Int) OR (y -: (U T F)))
                                     ((y -: Int) OR (z -: (U T F)))] 
                                    (z -: (U T F)))))

(define-metafunction λTR
    reduce-ψ : Γ ψ -> ψ
    [(reduce-ψ [ψ_1 ...] (x_1 -: τ_1)) FF
     (judgment-holds (proves [(x_1 -: τ_1) ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (x_1 -: τ_1)) (x_1 -: τ_1)
     (where #f (proves [(x_1 -: τ_1) ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (x_1 -! τ_1)) FF
     (judgment-holds (proves [(x_1 -! τ_1) ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (x_1 -! τ_1)) (x_1 -! τ_1)
     (where #f (proves [(x_1 -! τ_1) ψ_1 ...] FF))]
    [(reduce-ψ Γ_1 TT) TT]
    [(reduce-ψ Γ_1 FF) FF]
    [(reduce-ψ [ψ_1 ...] (ψ_2 AND ψ_3))
     ((reduce-ψ [ψ_3 ψ_1 ...] ψ_2) AND (reduce-ψ [ψ_2 ψ_1 ...] ψ_3))]
    [(reduce-ψ [ψ_1 ...] (ψ_2 OR ψ_3)) FF
     (judgment-holds (proves [ψ_3 ψ_1 ...] FF))
     (judgment-holds (proves [ψ_2 ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (ψ_2 OR ψ_3)) (reduce-ψ [ψ_1 ...] ψ_2)
     (judgment-holds (proves [ψ_3 ψ_1 ...] FF))
     (where #f (proves [ψ_2 ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (ψ_2 OR ψ_3)) (reduce-ψ [ψ_1 ...] ψ_3)
     (where #f (proves [ψ_3 ψ_1 ...] FF))
     (judgment-holds (proves [ψ_2 ψ_1 ...] FF))]
    [(reduce-ψ [ψ_1 ...] (ψ_2 OR ψ_3))
     ((reduce-ψ [ψ_1 ...] ψ_2) OR (reduce-ψ [ψ_1 ...] ψ_3))
     (where #f (proves [ψ_3 ψ_1 ...] FF))
     (where #f (proves [ψ_2 ψ_1 ...] FF))])


(check-equal? (term (reduce-ψ [] (((x -: Int) OR (x -: (U T F)))
                               AND (x -! Int))))
              (term ((x -: (U T F)) AND (x -! Int))))

(check-equal? (term (reduce-ψ [] ((x -: Int) AND (x -! Int))))
              (term (FF AND FF)))
