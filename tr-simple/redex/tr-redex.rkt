#lang racket

(require redex rackunit)

(define-language λTR
  [b   ::= boolean]
  [x   ::= variable-not-otherwise-mentioned]
  [e   ::= (ann x τ) (e e) (λ (x : τ) e) (if e e e) 
           c boolean integer string (let (x e) e)]
  [c   ::= add1 zero? int? str? bool? proc? str-len + error]
  [o   ::= x]
  [oo  ::= o Null]
  [τ   ::= Top T F Int Str (U τ ...) (λ x τ τ ψ ψ oo)]
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
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_2) (o_1 -: τ_1) (o_1 -: (update τ_1 #t τ_2))] ψ_4)
   ------------------- "L-Restrict"
  (proves [ψ_1 ... (o_1 -: τ_1) ψ_2 ... (o_1 -: τ_2) ψ_3 ...] ψ_4)]
  ; L-Remove-lhs
  [(where #f (in (o_1 -: (update τ_1 #f τ_2)) 
                 [ψ_1 ... (o_1 -! τ_2) ψ_2 ... (o_1 -: τ_1) ψ_3 ...]))
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_1) (o_1 -! τ_2) (o_1 -: (update τ_1 #f τ_2))] ψ_4)
   ------------------- "L-Remove-lhs"
  (proves [ψ_1 ... (o_1 -! τ_2) ψ_2 ... (o_1 -: τ_1) ψ_3 ...] ψ_4)]
    ; L-Remove-rhs
  [(where #f (in (o_1 -: (update τ_1 #f τ_2)) 
                 [ψ_1 ...  (o_1 -: τ_1) ψ_2 ... (o_1 -! τ_2) ψ_3 ...]))
   (proves [ψ_1 ... ψ_2 ... ψ_3 ... (o_1 -: τ_1) (o_1 -! τ_2) (o_1 -: (update τ_1 #f τ_2))] ψ_4)
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
   (subtype (λ x_1 τ_1 τ_2 ψ_1 ψ_2 oo_1)
            (λ x_2 τ_3 τ_4 ψ_3 ψ_4 oo_2))])

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
     (common-val (λ x_1 τ_1 τ_2 ψ_1 ψ_2 oo_1) 
                 (λ x_2 τ_3 τ_4 ψ_3 ψ_4 oo_2))])


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
  [(remove (U) τ_2) (U)]
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
  [(free-vars Str) (vars)]
  [(free-vars T) (vars)]
  [(free-vars F) (vars)]
  [(free-vars (U)) (vars)]
  [(free-vars (U τ_1 τ_2 ...)) (app (free-vars τ_1) 
                                    (free-vars (U τ_2 ...)))]
  [(free-vars (λ x_1 τ_1 τ_2 ψ_1 ψ_2 oo_1))
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
  [(subst-ψ oo_1 x_1 (x_2 -: τ_1)) (x_2 -: τ_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 (free-vars τ_1)))]
  [(subst-ψ oo_1 x_1 (x_2 -! τ_1)) (x_2 -! τ_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 (free-vars τ_1)))]
  [(subst-ψ oo_1 x_1 (x_2 -: τ_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 (free-vars τ_1)))]
  [(subst-ψ oo_1 x_1 (x_2 -! τ_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 (free-vars τ_1)))]
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
  [(subst-τ oo_1 x_1 Str) Str]
  [(subst-τ oo_1 x_1 T) T]
  [(subst-τ oo_1 x_1 F) F]
  [(subst-τ oo_1 x_1 (U)) (U)]
  [(subst-τ oo_1 x_1 (U τ_1)) (subst-τ oo_1 x_1 τ_1)]
  [(subst-τ oo_1 x_1 (U τ_1 τ_2 τ_3 ...)) 
   (U (subst-τ oo_1 x_1 τ_1)
      (subst-τ oo_1 x_1 (U τ_2 τ_3 ...)))]
  [(subst-τ oo_1 x_1 (λ x_1 τ_1 τ_2 ψ_1 ψ_2 oo_2))
   (λ x_1 (subst-τ oo_1 x_1 τ_1) τ_2 ψ_1 ψ_2 oo_2)]
  [(subst-τ oo_1 x_1 (λ x_2 τ_1 τ_2 ψ_1 ψ_2 oo_2))
   (λ x_2 
     (subst-τ oo_1 x_1 τ_1)
     (subst-τ oo_1 x_1 τ_2)
     (subst-ψ oo_1 x_1 ψ_1) 
     (subst-ψ oo_1 x_1 ψ_2) 
     (subst-oo oo_1 x_1 oo_2))])


(check-equal? (term (subst-oo Null x x)) (term Null))
(check-equal? (term (subst-ψ x x (x -: Int))) (term (x -: Int)))
(check-equal? (term (subst-ψ x y (y -: Int))) (term (x -: Int)))
(check-equal? (term (subst-ψ Null x (y -: Int))) (term (y -: Int)))
(check-equal? (term (subst-ψ Null y (y -: Int))) (term TT))


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
             (subtype (λ x Top (U T F) (x -: Int) (x -! Int) Null) 
                      (λ x Top (U T F) (x -: Int) (x -! Int) Null))))
(check-true (judgment-holds 
             (subtype (λ x Top (U T F) (x -: Int) (x -! Int) Null) 
                      (λ y Top (U T F) (y -: Int) (y -! Int) Null))))
(check-true (judgment-holds 
             (subtype (λ x Top Int TT TT Null) 
                      (λ y Int (U Int T F) TT TT Null))))


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
    [(reduce-ψ Γ_1 (x_1 -: τ_1)) FF
     (judgment-holds (proves Γ_1 (x_1 -! τ_1)))]
    [(reduce-ψ Γ_1 (x_1 -: τ_1)) (x_1 -: τ_1)
     (where #f (proves Γ_1 (x_1 -! τ_1)))]
    [(reduce-ψ Γ_1 (x_1 -! τ_1)) FF
     (judgment-holds (proves Γ_1 (x_1 -: τ_1)))]
    [(reduce-ψ Γ_1 (x_1 -! τ_1)) (x_1 -! τ_1)
     (where #f (proves Γ_1 (x_1 -: τ_1)))]
    [(reduce-ψ Γ_1 TT) TT]
    [(reduce-ψ Γ_1 FF) FF]
    [(reduce-ψ [ψ_1 ...] (ψ_2 AND ψ_3))
     ((reduce-ψ [ψ_3 ψ_1 ...] ψ_2) AND (reduce-ψ [ψ_2 ψ_1 ...] ψ_3))]
    [(reduce-ψ Γ_1 (ψ_2 OR ψ_3))
     ((reduce-ψ Γ_1 ψ_2) OR (reduce-ψ Γ_1 ψ_3))])


(check-equal? (term (reduce-ψ [] (((x -: Int) OR (x -: (U T F)))
                               AND (x -! Int))))
              (term ((FF OR (x -: (U T F))) AND (x -! Int))))

(check-equal? (term (reduce-ψ [] ((x -: Int) AND (x -! Int))))
              (term (FF AND FF)))

(define-metafunction λTR
    simplify-ψ : ψ -> ψ
    [(simplify-ψ ψ_1) ψ_1])  ;(reduce-ψ [] ψ_1)])

(define-metafunction λTR
  δτ : c -> τ
  [(δτ add1) (λ x Int Int TT FF Null)]
  [(δτ +) (λ x Int (λ y Int Int TT FF Null) TT FF Null)]
  [(δτ zero?) (λ x Int (U T F) TT TT x)]
  [(δτ int?) (λ x Top (U T F) (x -: Int) (x -! Int) x)]
  [(δτ str?) (λ x Top (U T F) (x -: Str) (x -! Str) x)]
  [(δτ str-len) (λ x Str Int TT FF Null)]
  [(δτ error) (λ x Str (U) FF FF Null)]
  [(δτ bool?) (λ x Top (U T F) (x -: (U T F)) (x -! (U T F)) x)]
  [(δτ proc?) (λ x Top (U T F) 
                 (x -: (λ y Top (U) TT TT Null))
                 (x -! (λ y Top (U) TT TT Null))
                 x)])


(define-metafunction λTR
  oo-join : oo oo -> oo
  [(oo-join oo_1 Null) Null]
  [(oo-join Null oo_2) Null]
  [(oo-join x_!_1 x_!_1) Null]
  [(oo-join x_1 x_1) x_1])

(define-metafunction λTR
  τ-join : τ τ -> τ
  [(τ-join τ_1 τ_2) τ_2
   (judgment-holds (subtype τ_1 τ_2))]
  [(τ-join τ_1 τ_2) τ_1
   (judgment-holds (subtype τ_2 τ_1))]
  [(τ-join τ_1 τ_2) (U τ_1 τ_2)
   (where #f (subtype τ_1 τ_2))
   (where #f (subtype τ_2 τ_1))])

(define-judgment-form λTR
  #:mode (typeof I I O O O O)
  #:contract (typeof Γ e τ ψ ψ oo)
  [-------------- "T-Num"
   (typeof Γ_1 number_1 Int TT FF Null)]
  [-------------- "T-Str"
   (typeof Γ_1 string_1 Str TT FF Null)]
  [-------------- "T-Const"
   (typeof Γ_1 c_1 (δτ c_1) TT FF Null)]
  [-------------- "T-True"
   (typeof Γ_1 #t T TT FF Null)]
  [-------------- "T-False"
   (typeof Γ_1 #f F FF TT Null)]
  [(proves Γ_1 (x_1 -: τ_1))
   -------------- "T-AnnVar"
   (typeof Γ_1 (ann x_1 τ_1) τ_1 (x_1 -! F) (x_1 -: F) x_1)]
  [(typeof [(x_1 -: τ_1) ψ_1 ...] e_1 τ_2 ψ_2 ψ_3 oo_1)
   -------------- "T-Abs"
   (typeof [ψ_1 ...]
           (λ (x_1 : τ_1) e_1) 
           (λ x_1 τ_1 τ_2 (simplify-ψ ψ_2) (simplify-ψ ψ_3) oo_1)
           TT FF
           Null)]
  [(typeof Γ_1 e_1 (λ x_1 τ_1 τ_2 ψ_1 ψ_2 oo_0) ψ_3 ψ_4 oo_1)
   (typeof Γ_1 e_2 τ_3 ψ_5 ψ_6 oo_2)
   (subtype τ_3 τ_1)
   -------------- "T-App"
   (typeof Γ_1
           (e_1 e_2)
           (subst-τ oo_2 x_1 τ_2)
           (subst-ψ oo_2 x_1 (simplify-ψ ψ_1))
           (subst-ψ oo_2 x_1 (simplify-ψ ψ_2))
           (subst-oo oo_2 x_1 oo_0))]
  [(typeof [ψ_1 ...]     e_1 τ_1 ψ_2 ψ_3 oo_1)
   (typeof [ψ_2 ψ_1 ...] e_2 τ_2 ψ_4 ψ_5 oo_2)
   (typeof [ψ_3 ψ_1 ...] e_3 τ_3 ψ_6 ψ_7 oo_3)
   ------------------------------------------- "T-If"
   (typeof [ψ_1 ...] 
           (if e_1 e_2 e_3)
           (τ-join τ_2 τ_3)
           (simplify-ψ ((ψ_2 AND ψ_4) OR (ψ_3 AND ψ_6))) 
           (simplify-ψ ((ψ_2 AND ψ_5) OR (ψ_3 AND ψ_7)))
           (oo-join oo_2 oo_3))]
  [(typeof [ψ_2 ...] e_0 τ_0 ψ_0+ ψ_0- oo_0)
   (typeof [(x_1 -: τ_0) (((x_1 -! F) AND ψ_0+) 
                          OR ((x_1 -: F) AND ψ_0-)) ψ_2 ...] 
           e_1
           τ_1
           ψ_1+ ψ_1- 
           oo_1)
   (where ψ_5 ((x_1 -: τ_0) AND (((x_1 -! F) AND ψ_0+) 
                                 OR ((x_1 -: F) AND ψ_0-))))
   -------------------------- "T-Let"
   (typeof [ψ_2 ...]
           (let (x_1 e_0) e_1)
           (subst-τ oo_0 x_1 τ_1)
           (subst-ψ oo_0 x_1 
                    (simplify-ψ (ψ_1+ AND ψ_5)))
           (subst-ψ oo_0 x_1 
                    (simplify-ψ (ψ_1- AND ψ_5)))
           (subst-oo oo_0 x_1 oo_1))])


(define-judgment-form λTR
  #:mode (typeof* I I I I I I)
  #:contract (typeof* Γ e τ ψ ψ oo)
  [(typeof Γ_1 e_1 τ_2 ψ_3 ψ_4 oo_2)
   (subtype τ_2 τ_1)
   (proves [ψ_3] ψ_1) (proves [ψ_4] ψ_2)
   (subobj oo_2 oo_1)
   -------------- "T-Subsume"
   (typeof* Γ_1 e_1 τ_1 ψ_1 ψ_2 oo_1)])

(define-metafunction λTR
  and : e e -> e
  [(and e_1 e_2) (if e_1 e_2 #f)])

(define-metafunction λTR
  or : e e -> e
  [(or e_1 e_2) (let (x_42 e_1) 
                  (if (ann x_42 Top)
                      (ann x_42 Top)
                      e_2))])

(define-metafunction λTR
  Option : τ -> τ
  [(Option τ_1) (U τ_1 F)])

; Example 1
(check-true (judgment-holds (typeof* [(x -: Top)] 
                                     (if (int? (ann x Top))
                                         (add1 (ann x Int))
                                         0) 
                                     Int 
                                     TT FF 
                                     Null)))
; Example 2
(check-true (judgment-holds (typeof* []
                                    (λ (x : (U Str Int))
                                      (if (int? (ann x Top))
                                          (add1 (ann x Int))
                                          (str-len (ann x Str))))
                                     (λ x (U Str Int) Int TT FF Null)
                                     TT FF
                                     Null)))
; Example 3
(check-true (judgment-holds (typeof* [(x -: (Option Str))]
                                     (if (ann x Top)
                                         (str-len (ann x Str))
                                         (error "string not found"))
                                     Int
                                     TT FF
                                     Null)))
; Example 4
#;(check-true (judgment-holds (typeof* [(f -: (λ x (U Int Str) Int TT FF Null))
                                      (x -: Top)]
                                     (if (or (int? (ann x Top))
                                             (str? (ann x Top)))
                                         ((ann f (λ x (U Int Str) Int TT FF Null))
                                          (ann x (U Int Str)))
                                         0)
                                     Int
                                     TT FF
                                     Null)))
; Example 5
(check-true (judgment-holds (typeof* [(x -: Top) (y -: Top)]
                                     (if (and (int? (ann x Top)) (str? (ann y Top)))
                                         ((+ (ann x Int)) (str-len (ann y Str)))
                                         0)
                                     Int
                                     TT FF
                                     Null)))
; Example 6
(check-false (judgment-holds (typeof* [(x -: Top) (y -: Top)]
                                     (if (and (int? (ann x Top)) (str? (ann y Top)))
                                         ((+ (ann x Int)) (str-len (ann y Str)))
                                         (str-len (ann y Str)))
                                     Int
                                     TT FF
                                     Null)))
; Example 7
(check-true (judgment-holds (typeof* [(x -: Top) (y -: Top)]
                                     (if (if (int? (ann x Top)) (str? (ann y Top)) #f)
                                         ((+ (ann x Int)) (str-len (ann y Str)))
                                         0)
                                     Int
                                     TT FF
                                     Null)))
; Example 8
#;(check-true (judgment-holds (typeof* [(x -: Top)]
                                     (let (tmp (str? (ann x Top)))
                                       (if (ann tmp Top)
                                           (ann tmp Top)
                                           (int? (ann x Top))))
                                     Top
                                     TT TT;(x -: (U Str Int)) (x -! (U Str Int))
                                     Null)))

#;(check-true (judgment-holds (typeof* [(x -: Top)]
                          (let (tmp (str? (ann x Top)))
                            tmp)
                          (U T F)
                          (x -: Str)
                          (x -! Str)
                          Null)))
