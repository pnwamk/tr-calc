#lang racket

(require redex rackunit)

(define-language λTR
  [x   ::= variable-not-otherwise-mentioned]
  [e   ::= (ann x t) (e e) (λ (x : t) e) (if e e e) 
           c #t #f integer string (let (x e) e)]
  [c   ::= add1 zero? int? str? bool? proc? str-len + error]
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

(define-judgment-form λTR
  #:mode (!= I I)
  #:contract (!= any any)
  [------------ "Equal"
   (!= any_!_1 any_!_1)])

(define-metafunction λTR-vl 
  app : vl ... vl -> vl
  [(app (vars x_1 ...) (vars x_2 ...))
   (vars x_1 ... x_2 ...)]
  [(app (vars x_1 ...) (vars x_2 ...) (vars x_3 ...) ...)
   (app (app (vars x_1 ...) (vars x_2 ...)) (vars x_3 ...) ...)])

(define-judgment-form λTR-vl
  #:mode (in-vl I I)
  #:contract (in-vl x vl)
  [------------------- "In-vl"
   (in-vl x_2 (vars x_1 ... x_2 x_3 ...))])

(define-judgment-form λTR
  #:mode (is-U I)
  #:contract (is-U t)
  [-------------- "IsUnion"
   (is-U (U t_1 ...))])

(define-judgment-form λTR
  #:mode (non-U I)
  #:contract (non-U t)
  [(where #f (is-U t_1))
   -------------- "NonU"
   (non-U t_1)])

(define-metafunction λTR-vl 
  remove-var : x vl -> vl
  [(remove-var x_1 (vars))
   (vars)]
  [(remove-var x_1 (vars x_1 x_2 ...)) (remove-var (vars x_2 ...))]
  [(remove-var x_1 (vars x_2 x_3 ...)) (app (vars x_2) (remove-var (vars x_3 ...)))
   (judgment-holds (!= x_1 x_2))])

(define-metafunction λTR
  ~ : P -> P
  [(~ (o -: t_1)) (o -! t_1)]
  [(~ (o -! t_1)) (o -: t_1)]
  [(~ (p_1 AND p_2)) ((~ p_1) OR (~ p_2))]
  [(~ (p_1 OR p_2)) ((~ p_1) AND (~ p_2))]
  [(~ TT) FF]
  [(~ FF) TT]
  [(~ Unk) Unk]
  [(~ Err) Err])

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
   (proves* is*_1 not*_1 (P_1 ...) TT)]
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
   ---------------------- "Proves"
   (proves E_1 P_1)])


(define-judgment-form λTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo_1 oo_1)]
  [------------------- "SO-Top"
   (subobj oo_1 Null)])

(define-judgment-form λTR
  #:mode (subprop I I)
  #:contract (subprop P P)
  [------------------- "SP-Top"
   (subprop P_1 Unk)]
  [(proves [P_1] P_2)
   (proves [(~ P_1)] (~ P_2))
   ------------------- "SP-Impl"
   (subprop P_1 P_2)])


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
   (subprop (subst-P x_2 x_1 P_1) P_2)
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
  [(update t_1 #t t_2) (restrict t_1 t_2)]
  [(update t_1 #f t_2) (remove t_1 t_2)])

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

(define-judgment-form λTR
  #:mode (eqv-type? I I)
  #:contract (eqv-type? t t)
  [(subtype t_1 t_2)
   (subtype t_2 t_1)
   ----------------- "Equiv-Type"
   (eqv-type? t_1 t_2)])

; restrict tests
(check-true (judgment-holds (eqv-type? (restrict Int Int) Int)))
(check-true (judgment-holds (eqv-type? (restrict Int Top) Int)))
(check-true (judgment-holds (eqv-type? (restrict Int (U)) (U))))
(check-true (judgment-holds (eqv-type? (restrict Int (U T F Int)) Int)))
(check-true (judgment-holds (eqv-type? (restrict (U T F) (U T Int)) T)))
(check-true (judgment-holds (eqv-type? (restrict (U (U (U T) F)) (U T Int Str)) T)))

; remove tests
(check-true (judgment-holds (eqv-type? (remove Int Int) (U))))
(check-true (judgment-holds (eqv-type? (remove Int Str) Int)))
(check-true (judgment-holds (eqv-type? (remove Int (U Int Str)) (U))))
(check-true (judgment-holds (eqv-type? (remove (U Int Str) Int) Str)))
(check-true (judgment-holds (eqv-type? (remove (U (U (U T F)) (U Int) Int) 
                                               (U (U (U T) F) T F)) 
                                       Int)))


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
(check-true (judgment-holds (proves [ ] (~ FF))))
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

(define-metafunction λTR
    reduce-P : E P -> P
    [(reduce-P E_1 TT) TT]
    [(reduce-P E_1 FF) FF]
    [(reduce-P E_1 Unk) Unk]
    [(reduce-P E_1 Err) Err]
    [(reduce-P E_1 (x_1 -: t_1)) FF
     (judgment-holds (proves E_1 (x_1 -! t_1)))]
    [(reduce-P E_1 (x_1 -: t_1)) (x_1 -: t_1)
     (where #f (proves E_1 (x_1 -! t_1)))]
    [(reduce-P E_1 (x_1 -! t_1)) FF
     (judgment-holds (proves E_1 (x_1 -: t_1)))]
    [(reduce-P E_1 (x_1 -! t_1)) (x_1 -! t_1)
     (where #f (proves E_1 (x_1 -: t_1)))]
    [(reduce-P [P_1 ...] (p_1 AND p_2))
     ((reduce-P [p_2 P_1 ...] p_1) AND (reduce-P [p_1 P_1 ...] p_2))]
    [(reduce-P E_1 (p_1 OR p_2))
     ((reduce-P E_1 p_1) OR (reduce-P E_1 p_2))])

(check-equal? (term (reduce-P [] (((x -: Int) OR (x -: (U T F)))
                               AND (x -! Int))))
              (term ((FF OR (x -: (U T F))) AND (x -! Int))))

(check-equal? (term (reduce-P [] ((x -: Int) AND (x -! Int))))
              (term (FF AND FF)))

(define-metafunction λTR
    simplify-P : P -> P
    [(simplify-P P_1) (reduce-P [] P_1)])

(define-metafunction λTR
  δt : c -> t
  [(δt add1) (λ x Int Int TT Null)]
  [(δt +) (λ x Int (λ y Int Int TT Null) TT Null)]
  [(δt zero?) (λ x Int (U T F) Unk Null)]
  [(δt int?) (λ x Top (U T F) (x -: Int) Null)]
  [(δt str?) (λ x Top (U T F) (x -: Str) Null)]
  [(δt str-len) (λ x Str Int TT Null)]
  [(δt error) (λ x Str (U) Err Null)]
  [(δt bool?) (λ x Top (U T F) (x -: (U T F)) Null)]
  [(δt proc?) (λ x Top (U T F) 
                 (x -: (λ y (U) Top Unk Null))
                 Null)])

(define-metafunction λTR
  oo-join : oo oo -> oo
  [(oo-join oo_1 Null) Null]
  [(oo-join Null oo_2) Null]
  [(oo-join x_!_1 x_!_1) Null]
  [(oo-join x_1 x_1) x_1])

(define-metafunction λTR
  t-join : t t -> t
  [(t-join t_1 t_2) t_2
   (judgment-holds (subtype t_1 t_2))]
  [(t-join t_1 t_2) t_1
   (judgment-holds (subtype t_2 t_1))]
  [(t-join t_1 t_2) (U t_1 t_2)
   (where #f (subtype t_1 t_2))
   (where #f (subtype t_2 t_1))])

; meta-and
(define-metafunction λTR
  mAND : P P -> P
  [(mAND Err _) Err]
  [(mAND _ Err) Err]
  [(mAND Unk P_1) P_1]
  [(mAND P_1 Unk) P_1]
  [(mAND p_1 p_2) (p_1 AND p_2)])

(define-metafunction λTR
  mOR : P P -> P
  [(mOR Err P_1) P_1]
  [(mOR P_1 Err) P_1]
  [(mOR Unk _) Unk]
  [(mOR _ Unk) Unk]
  [(mOR p_1 p_2) (p_1 OR p_2)])

(define-judgment-form λTR
  #:mode (typeof I I O O O)
  #:contract (typeof E e t P oo)
  [-------------- "T-Num"
   (typeof E integer Int TT Null)]
  [-------------- "T-Str"
   (typeof E string Str TT Null)]
  [-------------- "T-Const"
   (typeof E c_1 (δt c_1) TT Null)]
  [-------------- "T-True"
   (typeof E #t T TT Null)]
  [-------------- "T-False"
   (typeof E #f F FF Null)]
  [(proves E_1 (x_1 -: t_1))
   -------------- "T-AnnVar"
   (typeof E_1 (ann x_1 t_1) t_1 (x_1 -! F) x_1)]
  [(typeof [(x_1 -: t_1-) P_0 ...] e_1 t_1+ P_1 oo_1)
   -------------- "T-Abs"
   (typeof [P_0 ...]
           (λ (x_1 : t_1-) e_1)
           (λ x_1 t_1- t_1+ P_1 oo_1)
           TT
           Null)]
  [(typeof E_1 e_1 (λ x_0 t_0- t_0+ P_0 oo_0) P_1 oo_1)
   (typeof E_1 e_2 t_2 P_2 oo_2)
   (subtype t_2 t_0-)
   -------------- "T-App"
   (typeof E_1
           (e_1 e_2)
           (subst-t oo_2 x_0 t_0+)
           (subst-P oo_2 x_0 (simplify-P P_0))
           (subst-oo oo_2 x_0 oo_0))]
  [(typeof [P_0 ...] e_1 t_1 P_1 oo_1)
   (typeof [P_1 P_0 ...] e_2 t_2 P_2 oo_2)
   (typeof [(~ P_1) P_0 ...] e_3 t_3 P_3 oo_3)
   ------------------------------ "T-If"
   (typeof [P_0 ...]
           (if e_1 e_2 e_3)
           (t-join t_2 t_3)
           (mOR (mAND P_1 P_2) 
                (mAND (~ P_1) P_3))
           (oo-join oo_2 oo_3))]
  [(typeof [P_0 ...] e_1 t_1 P_1 oo_1)
   (typeof [(x_1 -: t_1) 
            (mOR (mAND (x_1 -! F) P_1) 
                 (mAND (x_1 -: F) (~ P_1)))
            P_0 ...] 
           e_2
           t_2
           P_2 
           oo_2)
   -------------------------- "T-Let"
   (typeof [P_0 ...]
           (let (x_1 e_1) e_2)
           (subst-t oo_1 x_1 t_2)
           (subst-P oo_1 x_1 
                    (simplify-P (mAND P_2 
                                      (mOR (mAND (x_1 -! F) P_1) 
                                           (mAND (x_1 -: F) (~ P_1))))))
           (subst-oo oo_1 x_1 oo_2))])


(define-judgment-form λTR
  #:mode (typeof* I I I I I)
  #:contract (typeof* E e t P oo)
  [(typeof E_1 e_1 t_2 P_2 oo_2)
   ;(eqv-type? t_2 t_1)
   (subtype t_2 t_1)
   (subprop P_2 P_1)
   (subobj oo_2 oo_1)
   -------------- "T-Subsume"
   (typeof* E_1 e_1 t_1 P_1 oo_1)])

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
  Option : t -> t
  [(Option t_1) (U t_1 F)])

; Example 1
(check-true (judgment-holds (typeof* [(x -: Top)] 
                                     (if (int? (ann x Top))
                                         (add1 (ann x Int))
                                         0) 
                                     Int 
                                     TT 
                                     Null)))

(check-true (judgment-holds (typeof* []
                                     (λ (x : Int)
                                       (add1 (ann x Int)))
                                     (λ x Int Int TT Null)
                                     TT
                                     Null)))

(check-true (judgment-holds (typeof* [(x -: (U Str Int))] 
                                     (if (int? (ann x Top))
                                         (add1 (ann x Int))
                                         (str-len (ann x Str)))
                                     Int
                                     TT
                                     Null)))

(check-true (judgment-holds (typeof* [(x -: Top)]
                                     (int? (ann x Top))
                                     (U T F)
                                     (x -: Int)
                                     Null)))

(check-true (judgment-holds (typeof* []
                                     (λ (x : Top)
                                       (int? (ann x Top)))
                                     (λ x Top (U T F) (x -: Int) Null)
                                     TT
                                     Null)))

;Example 2
(check-true (judgment-holds (typeof* []
                                    (λ (x : (U Str Int))
                                      (if (int? (ann x Top))
                                          (add1 (ann x Int))
                                          (str-len (ann x Str))))
                                     (λ x (U Str Int) Int TT Null)
                                     TT                                    
                                     Null)))

(check-true (judgment-holds (typeof* []
                                     (error "string not found!")
                                     (U)
                                     Err
                                     Null)))

 ; Example 3
 (check-true (judgment-holds (typeof* [(x -: (Option Str))]
                                      (if (ann x Top)
                                          (str-len (ann x Str))
                                          0) ;(error "string not found!"))
                                      Int
                                      TT
                                      Null)))
#|
(mOR (mAND P_1 P_2) 
     (mAND (~ P_1) P_3))
==>
(mOR (mAND (x -! F) TT) 
     (mAND (x -: F) Err))
==> 
(mOR ((x -! F) AND TT) 
     Err)
==> 
(x -! F)
----------------------- OTHER
True
(or (and (x -! F) TT)
    (and (x -: F) Err))
---------------------------
False
~(or (and (x -! F) TT)
     (and (x -: F) Err))
==>
(and ~(and (x -! F) TT)
     ~(and (x -: F) Err))
==>
(and (or (x -: F) FF)
     (or (x -! F) Err))
THIS IS THE CORRECT NEGATION!!!


|#

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
