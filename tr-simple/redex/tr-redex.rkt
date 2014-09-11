#lang racket

(require redex rackunit)

(define-language λTR
  [b   ::= boolean]
  [x   ::= variable-not-otherwise-mentioned]
  [e   ::= (ann x t) (e e) (λ (x : t) e) (if e e e) 
           c boolean integer string (let (x e) e)]
  [c   ::= add1 zero? int? str? bool? proc? str-len plus error]
  [o   ::= x]
  [oo   ::= o Null]
  [t   ::= Top T F Int Str (U t ...) (λ x t t P oo)]
  [is  ::= (o -: t)]
  [not ::= (o -! t)]
  [α   ::= is not]
  [p   ::= α (p OR p) (p AND p) TT FF]
  [P   ::= p Unk Err]
  [is*   ::= (is ...)]
  [not*  ::= (not ...)]
  [E   ::= (P ...)])

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
  #:contract (is-U t)
  [-------------- "IsUnion"
   (is-U (U t_1 ...))])

(check-false (judgment-holds (is-U Int)))
(check-true (judgment-holds (is-U (U))))
(check-true (judgment-holds (is-U (U Int))))

(define-judgment-form λTR
  #:mode (non-U I)
  #:contract (non-U t)
  [(where #f (is-U t_1))
   -------------- "NonU"
   (non-U t_1)])

(define-judgment-form λTR
  #:mode (nested-U I)
  #:contract (nested-U t)
  [-------------- "IsUnion"
   (nested-U (U t_1 ... (U t_2 ...) t_3 ...))])

(check-false (judgment-holds (nested-U Int)))
(check-false (judgment-holds (nested-U (U))))
(check-false (judgment-holds (nested-U (U T F))))
(check-true (judgment-holds (nested-U (U T F (U)))))
(check-true (judgment-holds (nested-U (U T (U F)))))

(define-judgment-form λTR
  #:mode (atomic-U I)
  #:contract (atomic-U t)
  [-------------- "Atomic-U"
   (atomic-U (U t_1))])

(define-judgment-form λTR
  #:mode (redundant-U I)
  #:contract (redundant-U t)
  [-------------- "Redundant-U"
   (redundant-U (U t_1 ... t_2 t_3 ... t_2 t_4 ...))])

(check-false (judgment-holds (redundant-U (U))))

(define-judgment-form λTR
  #:mode (flat-type I)
  #:contract (flat-type t)
  [(where #f (nested-U t_1))
   -------------- "IsFlat"
   (flat-type t_1)])

(check-true (judgment-holds (flat-type (U))))

(define-judgment-form λTR
  #:mode (unique-type I)
  #:contract (unique-type t)
  [(where #f (redundant-U t_1))
   -------------- "IsFlat"
   (unique-type t_1)])

(check-true (judgment-holds (unique-type (U))))

(define-judgment-form λTR
  #:mode (not-atomic-U I)
  #:contract (not-atomic-U t)
  [(where #f (atomic-U t_1))
   -------------- "IsNotAtomic"
   (not-atomic-U t_1)])

(check-true (judgment-holds (not-atomic-U (U))))

(define-metafunction λTR
  flatten-type : t -> t
  [(flatten-type t_1) t_1
   (judgment-holds (unique-type t_1))
   (judgment-holds (flat-type t_1))
   (judgment-holds (not-atomic-U t_1))]
  [(flatten-type (U t_1)) (flatten-type t_1)
   (judgment-holds (non-U t_1))]
  [(flatten-type (U t_1 ... t_2 t_3 ... t_2 t_4 ...))
   (flatten-type (U t_1 ... t_2 t_3 ... t_4 ...))
   (judgment-holds (flat-type (U t_1 ... t_2 t_3 ... t_2 t_4 ...)))]
  [(flatten-type (U t_1 ... (U t_2 ... ) t_3 ...)) 
   (flatten-type (U t_1 ... t_2 ... t_3 ...))])

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
  NOT : P -> P
  [(NOT (o -: t_1)) (o -! t_1)]
  [(NOT (o -! t_1)) (o -: t_1)]
  [(NOT (p_1 AND p_2)) ((NOT p_1) OR (NOT p_2))]
  [(NOT (p_1 OR p_2)) ((NOT p_1) AND (NOT p_2))]
  [(NOT TT) FF]
  [(NOT FF) TT]
  [(NOT Unk) Unk]
  [(NOT Err) Err])

(define-judgment-form λTR
  #:mode (not-in I I)
  #:contract (not-in any any)
  [------------------- "NotIn-Empty"
   (not-in any_1 ())]
  [(!= any_1 any_2)
   (not-in any_1 (any_3 ...))
   ------------------- "NotIn-Cons"
   (not-in any_1 (any_2 any_3 ...))])


(define-judgment-form λTR
  #:mode (proves* I I I I)
  #:contract (proves* is* not* E P)
  ; L-Atom Is
  [(subtype t_1 t_2)
   ------------------- "L-Atom-Is"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ...) 
           not*_1
           ()
           (o_1 -: t_2))]
  ; L-Atom Not
  [(subtype t_2 t_1)
   ------------------- "L-Atom-Not"
   (proves* is*_1
           (not_1 ... (o_1 -! t_1) not_2 ...)
           ()
           (o_1 -! t_2))]
  ; L-True
  [------------------- "L-True"
   (proves* is*_1 not*_1 () TT)]
  ; L-True-skip
  [(proves* is*_1 not*_1 (P_2 ...) P_1)
   ------------------- "L-True-skip"
   (proves* is*_1 not*_1 (TT P_2 ...) P_1)]
  ; L-False
  [------------------- "L-False"
   (proves* is*_1 not*_1 (FF P_2 ...) P_1)]
    ; L-Unk
  [(proves* is*_1 not*_1 (P_2 ...) P_1)
   ------------------- "L-Unk-skip"
   (proves* is*_1 not*_1 (Unk P_2 ...) P_1)]
  ; L-Error
  [------------------- "L-Error"
   (proves* is*_1 not*_1 (Err P_2 ...) P_1)]
  ; L-Bot
  [------------------- "L-Bot"
   (proves* (is_1 ... (o_1 -: (U)) is_2 ...) not*_1 () P_1)]
  ; L-Is-move
  [(proves* ((o_1 -: t_1) is_1 ...) not*_1 (P_1 ...) P_2)
   ------------------- "L-Is-move"
   (proves* (is_1 ...) not*_1 ((o_1 -: t_1) P_1 ...) P_2)]
    ; L-Not-move
  [(proves* is*_1 ((o_1 -! t_1) not_1 ...) (P_1 ...) P_2)
   ------------------- "L-Not-move"
   (proves* is*_1 (not_1 ...) ((o_1 -! t_1) P_1 ...) P_2)]
  ; L-AndE
  [(proves* is*_1 not*_1 (p_1 p_2 P_1 ...) P_2)
   ------------------- "L-AndE"
   (proves* is*_1 not*_1 ((p_1 AND p_2) P_1 ...) P_2)]
    ; L-AndI
  [(proves* is*_1 not*_1 () p_1)
   (proves* is*_1 not*_1 () p_2)
   ------------------- "L-AndI"
   (proves* is*_1 not*_1 () (p_1 AND p_2))]
  ; L-OrI-lhs
  [(proves* is*_1 not*_1 () p_1)
   ------------------- "L-OrI-lhs"
   (proves* is*_1 not*_1 () (p_1 OR p_2))]
  ; L-OrI-rhs
  [(proves* is*_1 not*_1 () p_2)
   ------------------- "L-OrI-rhs"
   (proves* is*_1 not*_1 () (p_1 OR p_2))]
  ; L-OrE
  [(proves* is*_1 not*_1 (p_1 P_1 ...) P_2)
   (proves* is*_1 not*_1 (p_2 P_1 ...) P_2)
   ------------------- "L-OrE"
   (proves* is*_1 not*_1 ((p_1 OR p_2) P_1 ...) P_2)]
  ; L-Restrict
  [(proves* (is_1 ... is_2 ... is_3 ... (o_1 -: (restrict t_1 t_2))) 
           not*_1
           ()
           P_1)
   ------------------- "L-Restrict"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ... (o_1 -: t_2) is_3 ...) 
           not*_1
           ()
           P_1)]
  [(not-in (o_1 -: (remove t_1 t_2)) 
           (is_1 ... (o_1 -: t_1) is_2 ...))
   (proves* (is_1 ... is_2 ... (o_1 -: (remove t_1 t_2)))
           (not_1 ... not_2 ... (o_1 -! t_2))
           ()
           P_1)
   ------------------- "L-Remove"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ...) 
            (not_1 ... (o_1 -! t_2) not_2 ...)
            ()
            P_1)])

(define-judgment-form λTR
  #:mode (proves I I)
  #:contract (proves E P)
  [(proves* () () E_1 P_1)
   ---------------------- "Proves!"
   (proves E_1 P_1)])


(define-judgment-form λTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo_1 oo_1)]
  [------------------- "SO-Top"
   (subobj oo_1 Null)])

(define-judgment-form λTR
  #:mode (subP I I)
  #:contract (subP P P)
  [------------------- "SP-Top"
   (subP P_1 Unk)]
  [(proves [P_1] P_2)
   (proves [(NOT P_1)] (NOT P_2))
   ------------------- "SP-Impl"
   (subP P_1 P_2)])


(define-judgment-form λTR
  #:mode (subtype I I)
  #:contract (subtype t t)
  [------------------- "S-Refl"
   (subtype t_1 t_1)]
  [------------------- "S-Top"
   (subtype t_1 Top)]
  [(subtype t_1 t_2) ...
   ------------------- "S-UnionSub"
   (subtype (U t_1 ...) t_2)]
  [(subtype t_1 t_3)
   ------------------- "S-UnionSuper"
   (subtype t_1 (U t_2 ... t_3 t_4 ...))]
  [(subtype t_3 (subst-t x_2 x_1 t_1)) 
   (subtype (subst-t x_2 x_1 t_2) t_4) 
   (subobj (subst-oo x_2 x_1 oo_1) oo_2)
   (subP (subst-P x_2 x_1 P_1) P_2)
   ------------------------------------------ "S-Fun"
   (subtype (λ x_1 t_1 t_2 P_1 oo_1)
            (λ x_2 t_3 t_4 P_2 oo_2))])

(define-judgment-form λTR
    #:mode (common-val I I)
    #:contract (common-val t t)
    [------------------ "CS-Eq"
     (common-val t_1 t_1)]
    [------------------ "CS-Top-lhs"
     (common-val Top t_1)]
    [------------------ "CS-Top-rhs"
     (common-val t_1 Top)]
    [(common-val t_2 t_4)
     ------------------ "CS-U-lhs"
     (common-val (U t_1 ... t_2 t_3 ...) t_4)]
    [(common-val t_2 t_4)
     ------------------ "CS-U-rhs"
     (common-val t_4 (U t_1 ... t_2 t_3 ...))]
    [------------------ "CS-Abs"
     (common-val (λ x_1 t_1 t_2 P_1 oo_1) 
                 (λ x_2 t_3 t_4 P_2 oo_2))])


(check-true (judgment-holds (common-val Int Int)))
(check-true (judgment-holds (common-val (U T Int) Int)))
(check-true (judgment-holds (common-val Top Int)))
(check-false (judgment-holds (common-val T Int)))

(define-judgment-form λTR
  #:mode (type-conflict I I)
  #:contract (type-conflict t t)
  [(where #f (common-val t_1 t_2))
   --------------- "TC"
   (type-conflict t_1 t_2)])


(define-metafunction λTR
  update : t b t -> t
  [(update t_1 #t t_2) (flatten-type (restrict t_1 t_2))]
  [(update t_1 #f t_2) (flatten-type (remove t_1 t_2))])

; fix judgment-holds common-val clauses
(define-metafunction λTR
  restrict : t t -> t
  [(restrict t_1 t_2) (U)
   (judgment-holds (type-conflict t_1 t_2))
   (judgment-holds (non-U t_1))]
  [(restrict t_1 t_2) t_1
   (judgment-holds (subtype t_1 t_2))
   (judgment-holds (non-U t_1))]
  [(restrict t_1 t_2) t_2
   (judgment-holds (common-val t_1 t_2))
   (where #f (subtype t_1 t_2))
   (judgment-holds (non-U t_1))]
  [(restrict (U) t_2) (U)]
  [(restrict (U t_1) t_2) (restrict t_1 t_2)]
  [(restrict (U t_1 t_2 ...) t_3) (U (restrict t_1 t_3) (restrict (U t_2 ...) t_3))])

; fix where clauses w/ subtype
(define-metafunction λTR
  remove : t t -> t
  [(remove t_1 t_2) (U)
   (judgment-holds (subtype t_1 t_2))
   (judgment-holds (non-U t_1))]
  [(remove t_1 t_2) t_1
   (where #f (subtype t_1 t_2))
   (judgment-holds (non-U t_1))]
  [(remove (U) t_2) (U)]
  [(remove (U t_1) t_2) (remove t_1 t_2)]
  [(remove (U t_1 t_2 ...) t_3) (U (remove t_1 t_3) (remove (U t_2 ...) t_3))])

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
  [(free-vars (U t_1 t_2 ...)) (app (free-vars t_1) 
                                    (free-vars (U t_2 ...)))]
  [(free-vars (λ x_1 t_1 t_2 P_1 oo_1))
   (app (free-vars t_1)
        (remove-var x_1 (app (free-vars t_2)
                             (free-vars P_1)
                             (free-vars oo_1))))]
  ; props
  [(free-vars TT) (vars)]
  [(free-vars FF) (vars)]
  [(free-vars Unk) (vars)]
  [(free-vars Err) (vars)]
  [(free-vars (x_1 -: t_1)) (app (vars x_1) (free-vars t_1))]
  [(free-vars (x_1 -! t_1)) (app (vars x_1) (free-vars t_1))]
  [(free-vars (p_1 AND p_2)) (app (free-vars p_1) (free-vars p_2))]
  [(free-vars (p_1 OR  p_2)) (app (free-vars p_1) (free-vars p_2))])

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
  subst-p : oo x p -> p
  [(subst-p Null x_1 (x_1 -: t_1)) TT]
  [(subst-p Null x_1 (x_1 -! t_1)) TT]
  [(subst-p o_1 x_1 (x_1 -: t_1)) (o_1 -: (subst-t o_1 x t_1))]
  [(subst-p o_1 x_1 (x_1 -! t_1)) (o_1 -! (subst-t o_1 x t_1))]
  [(subst-p oo_1 x_1 (x_2 -: t_1)) (x_2 -: t_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 (free-vars t_1)))]
  [(subst-p oo_1 x_1 (x_2 -! t_1)) (x_2 -! t_1)
   (judgment-holds (!= x_1 x_2))
   (where #f (in-vl x_2 (free-vars t_1)))]
  [(subst-p oo_1 x_1 (x_2 -: t_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 (free-vars t_1)))]
  [(subst-p oo_1 x_1 (x_2 -! t_1)) TT
   (judgment-holds (!= x_1 x_2))
   (judgment-holds (in-vl x_2 (free-vars t_1)))]
  [(subst-p oo_1 x_1 (p_1 AND p_2)) 
   ((subst-p oo_1 x_1 p_1) AND (subst-p oo_1 x_1 p_2))]
  [(subst-p oo_1 x_1 (p_1 OR p_2)) 
   ((subst-p oo_1 x_1 p_1) OR (subst-p oo_1 x_1 p_2))]
  [(subst-p oo_1 x_1 TT) TT]
  [(subst-p oo_1 x_1 FF) FF])

(define-metafunction λTR
  subst-P : oo x P -> P
  [(subst-P oo_1 x_1 Unk) Unk]
  [(subst-P oo_1 x_1 Err) Err]
  [(subst-P oo_1 x_1 p_1) (subst-p oo_1 x_1 p_1)])


(define-metafunction λTR
  subst-t : oo x t -> t
  [(subst-t oo_1 x_1 Top) Top]
  [(subst-t oo_1 x_1 Int) Int]
  [(subst-t oo_1 x_1 Str) Str]
  [(subst-t oo_1 x_1 T) T]
  [(subst-t oo_1 x_1 F) F]
  [(subst-t oo_1 x_1 (U)) (U)]
  [(subst-t oo_1 x_1 (U t_1)) (subst-t oo_1 x_1 t_1)]
  [(subst-t oo_1 x_1 (U t_1 t_2 t_3 ...)) 
   (U (subst-t oo_1 x_1 t_1)
      (subst-t oo_1 x_1 (U t_2 t_3 ...)))]
  [(subst-t oo_1 x_1 (λ x_1 t_1 t_2 P_1 oo_2))
   (λ x_1 (subst-t oo_1 x_1 t_1) t_2 P_1 oo_2)]
  [(subst-t oo_1 x_1 (λ x_2 t_1 t_2 P_1 oo_2))
   (λ x_2 
     (subst-t oo_1 x_1 t_1)
     (subst-t oo_1 x_1 t_2)
     (subst-P oo_1 x_1 P_1)
     (subst-oo oo_1 x_1 oo_2))])


(check-equal? (term (subst-oo Null x x)) (term Null))
(check-equal? (term (subst-p x x (x -: Int))) (term (x -: Int)))
(check-equal? (term (subst-p x y (y -: Int))) (term (x -: Int)))
(check-equal? (term (subst-p Null x (y -: Int))) (term (y -: Int)))
(check-equal? (term (subst-p Null y (y -: Int))) (term TT))


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
             (subtype (λ x Top (U T F) (x -: Int) Null) 
                      (λ x Top (U T F) (x -: Int) Null))))
(check-true (judgment-holds 
             (subtype (λ x Top (U T F) (x -: Int) Null) 
                      (λ y Top (U T F) (y -: Int) Null))))
(check-true (judgment-holds 
             (subtype (λ x Top Int Unk Null)
                      (λ y Int (U Int T F) Unk Null))))

(check-false (judgment-holds (proves [ ] FF)))
(check-true (judgment-holds (proves [ ] (NOT FF))))
(check-true (judgment-holds (proves [(x -: Int)] (x -: Int))))
(check-true (judgment-holds (proves [((x -: Int) AND (y -: F))] 
                                    ((y -: F) AND (x -: Int)))))
(check-true (judgment-holds (proves [(x -: Int)] ((x -: Int) OR (x -: (U T F))))))
(check-true (judgment-holds (proves [(x -: Int) (x -! Int)] FF)))
(check-true (judgment-holds (proves [(x -: Int) (x -: Str)] FF)))
(check-true (judgment-holds (proves [(x -: (U T F Int)) 
                                     ((x -! T) AND (x -: (U T Int)))] 
                                    (x -: Int))))
(check-true (judgment-holds (proves [(((z -: (U)) OR FF) OR (x -: Int))
                                     ((x -! Int) OR (y -: (U T F)))
                                     ((y -: Int) OR (z -: (U T F)))] 
                                    (z -: (U T F)))))

;; (define-metafunction λTR
;;     reduce-ψ : Γ ψ -> ψ
;;     [(reduce-ψ Γ_1 (x_1 -: t_1)) FF
;;      (judgment-holds (proves Γ_1 (x_1 -! t_1)))]
;;     [(reduce-ψ Γ_1 (x_1 -: t_1)) (x_1 -: t_1)
;;      (where #f (proves Γ_1 (x_1 -! t_1)))]
;;     [(reduce-ψ Γ_1 (x_1 -! t_1)) FF
;;      (judgment-holds (proves Γ_1 (x_1 -: t_1)))]
;;     [(reduce-ψ Γ_1 (x_1 -! t_1)) (x_1 -! t_1)
;;      (where #f (proves Γ_1 (x_1 -: t_1)))]
;;     [(reduce-ψ Γ_1 TT) TT]
;;     [(reduce-ψ Γ_1 FF) FF]
;;     [(reduce-ψ [ψ_1 ...] (ψ_2 AND ψ_3))
;;      ((reduce-ψ [ψ_3 ψ_1 ...] ψ_2) AND (reduce-ψ [ψ_2 ψ_1 ...] ψ_3))]
;;     [(reduce-ψ Γ_1 (ψ_2 OR ψ_3))
;;      ((reduce-ψ Γ_1 ψ_2) OR (reduce-ψ Γ_1 ψ_3))])


;; (check-equal? (term (reduce-ψ [] (((x -: Int) OR (x -: (U T F)))
;;                                AND (x -! Int))))
;;               (term ((FF OR (x -: (U T F))) AND (x -! Int))))

;; (check-equal? (term (reduce-ψ [] ((x -: Int) AND (x -! Int))))
;;               (term (FF AND FF)))

;; (define-metafunction λTR
;;     simplify-ψ : ψ -> ψ
;;     [(simplify-ψ ψ_1) ψ_1])  ;(reduce-ψ [] ψ_1)])

;; (define-metafunction λTR
;;   δt : c -> t
;;   [(δt add1) (λ x Int Int TT FF Null)]
;;   [(δt +) (λ x Int (λ y Int Int TT FF Null) TT FF Null)]
;;   [(δt zero?) (λ x Int (U T F) TT TT x)]
;;   [(δt int?) (λ x Top (U T F) (x -: Int) (x -! Int) x)]
;;   [(δt str?) (λ x Top (U T F) (x -: Str) (x -! Str) x)]
;;   [(δt str-len) (λ x Str Int TT FF Null)]
;;   [(δt error) (λ x Str (U) FF FF Null)]
;;   [(δt bool?) (λ x Top (U T F) (x -: (U T F)) (x -! (U T F)) x)]
;;   [(δt proc?) (λ x Top (U T F) 
;;                  (x -: (λ y Top (U) TT TT Null))
;;                  (x -! (λ y Top (U) TT TT Null))
;;                  x)])


;; (define-metafunction λTR
;;   oo-join : oo oo -> oo
;;   [(oo-join oo_1 Null) Null]
;;   [(oo-join Null oo_2) Null]
;;   [(oo-join x_!_1 x_!_1) Null]
;;   [(oo-join x_1 x_1) x_1])

;; (define-metafunction λTR
;;   t-join : t t -> t
;;   [(t-join t_1 t_2) t_2
;;    (judgment-holds (subtype t_1 t_2))]
;;   [(t-join t_1 t_2) t_1
;;    (judgment-holds (subtype t_2 t_1))]
;;   [(t-join t_1 t_2) (U t_1 t_2)
;;    (where #f (subtype t_1 t_2))
;;    (where #f (subtype t_2 t_1))])

;; (define-judgment-form λTR
;;   #:mode (typeof I I O O O O)
;;   #:contract (typeof Γ e t ψ ψ oo)
;;   [-------------- "T-Num"
;;    (typeof Γ_1 number_1 Int TT FF Null)]
;;   [-------------- "T-Str"
;;    (typeof Γ_1 string_1 Str TT FF Null)]
;;   [-------------- "T-Const"
;;    (typeof Γ_1 c_1 (δt c_1) TT FF Null)]
;;   [-------------- "T-True"
;;    (typeof Γ_1 #t T TT FF Null)]
;;   [-------------- "T-False"
;;    (typeof Γ_1 #f F FF TT Null)]
;;   [(proves Γ_1 (x_1 -: t_1))
;;    -------------- "T-AnnVar"
;;    (typeof Γ_1 (ann x_1 t_1) t_1 (x_1 -! F) (x_1 -: F) x_1)]
;;   [(typeof [(x_1 -: t_1) ψ_1 ...] e_1 t_2 ψ_2 ψ_3 oo_1)
;;    -------------- "T-Abs"
;;    (typeof [ψ_1 ...]
;;            (λ (x_1 : t_1) e_1) 
;;            (λ x_1 t_1 t_2 (simplify-ψ ψ_2) (simplify-ψ ψ_3) oo_1)
;;            TT FF
;;            Null)]
;;   [(typeof Γ_1 e_1 (λ x_1 t_1 t_2 ψ_1 ψ_2 oo_0) ψ_3 ψ_4 oo_1)
;;    (typeof Γ_1 e_2 t_3 ψ_5 ψ_6 oo_2)
;;    (subtype t_3 t_1)
;;    -------------- "T-App"
;;    (typeof Γ_1
;;            (e_1 e_2)
;;            (subst-t oo_2 x_1 t_2)
;;            (subst-ψ oo_2 x_1 (simplify-ψ ψ_1))
;;            (subst-ψ oo_2 x_1 (simplify-ψ ψ_2))
;;            (subst-oo oo_2 x_1 oo_0))]
;;   [(typeof [ψ_1 ...]     e_1 t_1 ψ_2 ψ_3 oo_1)
;;    (typeof [ψ_2 ψ_1 ...] e_2 t_2 ψ_4 ψ_5 oo_2)
;;    (typeof [ψ_3 ψ_1 ...] e_3 t_3 ψ_6 ψ_7 oo_3)
;;    ------------------------------------------- "T-If"
;;    (typeof [ψ_1 ...] 
;;            (if e_1 e_2 e_3)
;;            (t-join t_2 t_3)
;;            (simplify-ψ ((ψ_2 AND ψ_4) OR (ψ_3 AND ψ_6))) 
;;            (simplify-ψ ((ψ_2 AND ψ_5) OR (ψ_3 AND ψ_7)))
;;            (oo-join oo_2 oo_3))]
;;   [(typeof [ψ_2 ...] e_0 t_0 ψ_0+ ψ_0- oo_0)
;;    (typeof [(x_1 -: t_0) (((x_1 -! F) AND ψ_0+) 
;;                           OR ((x_1 -: F) AND ψ_0-)) ψ_2 ...] 
;;            e_1
;;            t_1
;;            ψ_1+ ψ_1- 
;;            oo_1)
;;    (where ψ_5 ((x_1 -: t_0) AND (((x_1 -! F) AND ψ_0+) 
;;                                  OR ((x_1 -: F) AND ψ_0-))))
;;    -------------------------- "T-Let"
;;    (typeof [ψ_2 ...]
;;            (let (x_1 e_0) e_1)
;;            (subst-t oo_0 x_1 t_1)
;;            (subst-ψ oo_0 x_1 
;;                     (simplify-ψ (ψ_1+ AND ψ_5)))
;;            (subst-ψ oo_0 x_1 
;;                     (simplify-ψ (ψ_1- AND ψ_5)))
;;            (subst-oo oo_0 x_1 oo_1))])


;; (define-judgment-form λTR
;;   #:mode (typeof* I I I I I I)
;;   #:contract (typeof* Γ e t ψ ψ oo)
;;   [(typeof Γ_1 e_1 t_2 ψ_3 ψ_4 oo_2)
;;    (subtype t_2 t_1)
;;    (proves [ψ_3] ψ_1) (proves [ψ_4] ψ_2)
;;    (subobj oo_2 oo_1)
;;    -------------- "T-Subsume"
;;    (typeof* Γ_1 e_1 t_1 ψ_1 ψ_2 oo_1)])

;; (define-metafunction λTR
;;   and : e e -> e
;;   [(and e_1 e_2) (if e_1 e_2 #f)])

;; (define-metafunction λTR
;;   or : e e -> e
;;   [(or e_1 e_2) (let (x_42 e_1) 
;;                   (if (ann x_42 Top)
;;                       (ann x_42 Top)
;;                       e_2))])

;; (define-metafunction λTR
;;   Option : t -> t
;;   [(Option t_1) (U t_1 F)])

;; ; Example 1
;; (check-true (judgment-holds (typeof* [(x -: Top)] 
;;                                      (if (int? (ann x Top))
;;                                          (add1 (ann x Int))
;;                                          0) 
;;                                      Int 
;;                                      TT FF 
;;                                      Null)))
;; ; Example 2
;; (check-true (judgment-holds (typeof* []
;;                                     (λ (x : (U Str Int))
;;                                       (if (int? (ann x Top))
;;                                           (add1 (ann x Int))
;;                                           (str-len (ann x Str))))
;;                                      (λ x (U Str Int) Int TT FF Null)
;;                                      TT FF
;;                                      Null)))
;; ; Example 3
;; (check-true (judgment-holds (typeof* [(x -: (Option Str))]
;;                                      (if (ann x Top)
;;                                          (str-len (ann x Str))
;;                                          (error "string not found"))
;;                                      Int
;;                                      TT FF
;;                                      Null)))
;; ; Example 4
;; #;(check-true (judgment-holds (typeof* [(f -: (λ x (U Int Str) Int TT FF Null))
;;                                       (x -: Top)]
;;                                      (if (or (int? (ann x Top))
;;                                              (str? (ann x Top)))
;;                                          ((ann f (λ x (U Int Str) Int TT FF Null))
;;                                           (ann x (U Int Str)))
;;                                          0)
;;                                      Int
;;                                      TT FF
;;                                      Null)))
;; ; Example 5
;; (check-true (judgment-holds (typeof* [(x -: Top) (y -: Top)]
;;                                      (if (and (int? (ann x Top)) (str? (ann y Top)))
;;                                          ((+ (ann x Int)) (str-len (ann y Str)))
;;                                          0)
;;                                      Int
;;                                      TT FF
;;                                      Null)))
;; ; Example 6
;; (check-false (judgment-holds (typeof* [(x -: Top) (y -: Top)]
;;                                      (if (and (int? (ann x Top)) (str? (ann y Top)))
;;                                          ((+ (ann x Int)) (str-len (ann y Str)))
;;                                          (str-len (ann y Str)))
;;                                      Int
;;                                      TT FF
;;                                      Null)))
;; ; Example 7
;; (check-true (judgment-holds (typeof* [(x -: Top) (y -: Top)]
;;                                      (if (if (int? (ann x Top)) (str? (ann y Top)) #f)
;;                                          ((+ (ann x Int)) (str-len (ann y Str)))
;;                                          0)
;;                                      Int
;;                                      TT FF
;;                                      Null)))
;; ; Example 8
;; #;(check-true (judgment-holds (typeof* [(x -: Top)]
;;                                      (let (tmp (str? (ann x Top)))
;;                                        (if (ann tmp Top)
;;                                            (ann tmp Top)
;;                                            (int? (ann x Top))))
;;                                      Top
;;                                      TT TT;(x -: (U Str Int)) (x -! (U Str Int))
;;                                      Null)))

;; #;(check-true (judgment-holds (typeof* [(x -: Top)]
;;                           (let (tmp (str? (ann x Top)))
;;                             tmp)
;;                           (U T F)
;;                           (x -: Str)
;;                           (x -! Str)
;;                           Null)))
