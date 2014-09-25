#lang racket

(require redex)

(module+ test
  (require redex)
  (require rackunit))

(define-language λTR
  [x   ::= variable-not-otherwise-mentioned]
  [b   ::= boolean]
  [z   ::= integer]
  [e   ::= (ann x t) (e e) (λ ([x : t]) e) (if e e e) 
       c b z string (let ([x e]) e)]
  [c   ::= add1 zero? int? str? bool? proc? str-len + error]
  [o   ::= x]
  [oo  ::= o Null]
  [t   ::= Top T F Int Str (U t ...) (λ x t t P P oo)]
  [is  ::= (o -: t)]
  [neg ::= (o -! t)]
  [P   ::= is neg (OR P P) (AND P P) TT FF]
  [E   ::= (P ...)])

(define-judgment-form λTR
  #:mode (<> I I)
  #:contract (<> any any)
  [------------ "NotEqual"
   (<> any_!_1 any_!_1)])

(define-metafunction λTR 
  app : (any ...) ... -> (any ...)
  [(app (any_1 ...)) (any_1 ...)]
  [(app (any_1 ...) (any_2 ...) ...) (app (any_1 ... any_2 ...) ...)])

(define-judgment-form λTR
  #:mode (in I I)
  #:contract (in any any)
  [(side-condition ,(list? (member (term any_1) (term (any_2 ...)))))
   --------------------- "In"
   (in any_1 (any_2 ...))])

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

(define-judgment-form λTR
  #:mode (not-in I I)
  #:contract (not-in any any) 
  [(side-condition ,(not (member (term any_1) (term (any_2 ...)))))
   ------------------------ "Not-In"
   (not-in any_1 (any_2 ...))])


(define-judgment-form λTR
  #:mode (proves* I I I I)
  #:contract (proves* (is ...) (neg ...) E P)
  ; L-Atom Is
  [(subtype t_1 t_2)
   ------------------- "L-Atom-Is"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ...)
            (neg ...)
            ()
            (o_1 -: t_2))]
  
  ; L-Atom Neg
  [(proves* ((o_1 -: t_2) is_1 ...)
            (neg_1 ...)
            ()
            FF)
   ------------------- "L-Atom-Neg"
   (proves* (is_1 ...)
            (neg_1 ...)
            ()
            (o_1 -! t_2))]
  
  ; L-True
  [------------------- "L-True"
   (proves* (is ...) (neg ...) (P_1 ...) TT)]
  
  ; L-True-skip
  [(proves* (is_1 ...) (neg_1 ...) (P_2 ...) P_1)
   ------------------- "L-True-skip"
   (proves* (is_1 ...) (neg_1 ...) (TT P_2 ...) P_1)]
  
  ; L-False
  [------------------- "L-False"
   (proves* (is_1 ...) (neg_1 ...) (FF P_2 ...) P_1)]
  
  ; L-Bot
  [(subtype t_1 (U))
   ------------------- "L-Bot"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ...) (neg_1 ...) () P_1)]
  
  ; L-Is-move
  [(proves* ((o_1 -: t_1) is_1 ...) (neg_1 ...) (P_1 ...) P_2)
   ------------------- "L-Is-move"
   (proves* (is_1 ...) (neg_1 ...) ((o_1 -: t_1) P_1 ...) P_2)]
  
  ; L-Neg-move
  [(proves* (is_1 ...) ((o_1 -! t_1) neg_1 ...) (P_1 ...) P_2)
   ------------------- "L-Neg-move"
   (proves* (is_1 ...) (neg_1 ...) ((o_1 -! t_1) P_1 ...) P_2)]
  
  ; L-AndE
  [(proves* (is_1 ...) (neg_1 ...) (P_1 P_2 P_3 ...) P_4)
   ------------------- "L-AndE"
   (proves* (is_1 ...) (neg_1 ...) ((AND P_1 P_2) P_3 ...) P_4)]
  
  ; L-AndI
  [(proves* (is_1 ...) (neg_1 ...) () P_1)
   (proves* (is_1 ...) (neg_1 ...) () P_2)
   ------------------- "L-AndI"
   (proves* (is_1 ...) (neg_1 ...) () (AND P_1 P_2))]
  
  ; L-OrI-lhs
  [(proves* (is_1 ...) (neg_1 ...) () P_1)
   ------------------- "L-OrI-lhs"
   (proves* (is_1 ...) (neg_1 ...) () (OR P_1 P_2))]
  
  ; L-OrI-rhs
  [(proves* (is_1 ...) (neg_1 ...) () P_2)
   ------------------- "L-OrI-rhs"
   (proves* (is_1 ...) (neg_1 ...) () (OR P_1 P_2))]
  
  ; L-OrE
  [(proves* (is_1 ...) (neg_1 ...) (P_1 P_3 ...) P_4)
   (proves* (is_1 ...) (neg_1 ...) (P_2 P_3 ...) P_4)
   ------------------- "L-OrE"
   (proves* (is_1 ...) (neg_1 ...) ((OR P_1 P_2) P_3 ...) P_4)]
  
  ; L-Update-Is
  [(where t_new (update t_1 #t t_2))
   (not-in (o_1 -: t_new) (is_1 ... (o_1 -: t_1) is_2 ... (o_1 -: t_2) is_3 ...))
   (proves* ((o_1 -: t_new) is_1 ... is_2 ... is_3 ... (o_1 -: t_2) (o_1 -: t_1))
            (neg_1 ...)
            ()
            P_1)
  ------------------- "L-Update-Is"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ... (o_1 -: t_2) is_3 ...)
            (neg_1 ...)
            ()
            P_1)]
  
  ;L-Update-Neg
  [(where t_new (update t_1 #f t_2))
   (not-in (o_1 -: t_new) (is_1 ... (o_1 -: t_1) is_2 ...))
   (proves* ((o_1 -: t_new) is_1 ... is_2 ... (o_1 -: t_1))
            (neg_1 ... (o_1 -! t_2) neg_2 ...)
            ()
            P_1)
  ------------------- "L-Update-Neg"
   (proves* (is_1 ... (o_1 -: t_1) is_2 ...)
            (neg_1 ... (o_1 -! t_2) neg_2 ...)
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
   (proves [(subst-P x_2 x_1 P_1+)] P_2+)
   (proves [(subst-P x_2 x_1 P_1-)] P_2-)
   ------------------------------------------ "S-Fun"
   (subtype (λ x_1 t_1 t_2 P_1+ P_1- oo_1)
            (λ x_2 t_3 t_4 P_2+ P_2- oo_2))])

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

(module+ test
  (check-true (judgment-holds (common-val Int Int)))
  (check-true (judgment-holds (common-val (U T Int) Int)))
  (check-true (judgment-holds (common-val Top Int)))
  (check-false (judgment-holds (common-val T Int))))

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


(module+ test
  
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
                                       Int))))



(define-judgment-form λTR
  #:mode (eqv-type? I I)
  #:contract (eqv-type? t t)
  [(subtype t_1 t_2)
   (subtype t_2 t_1)
   ----------------- "Equiv-Type"
   (eqv-type? t_1 t_2)])


(define-metafunction λTR
  free-vars : any -> (x ...)
  ; objects
  [(free-vars Null) ()]
  [(free-vars x_1) (x_1)]
  ; types
  [(free-vars Top) ()]
  [(free-vars Int) ()]
  [(free-vars Str) ()]
  [(free-vars T) ()]
  [(free-vars F) ()]
  [(free-vars (U)) ()]
  [(free-vars (U t_1 t_2 ...)) (app (free-vars t_1) 
                                    (free-vars (U t_2 ...)))]
  [(free-vars (λ x_1 t_1 t_2 P_1 P_2 oo_1))
   (app (free-vars t_1)
        (remove* x_1 (app (free-vars t_2)
                          (free-vars P_1)
                          (free-vars P_2)
                          (free-vars oo_1))))]
  ; props
  [(free-vars TT) ()]
  [(free-vars FF) ()]
  [(free-vars (x_1 -: t_1)) (app (x_1) (free-vars t_1))]
  [(free-vars (x_1 -! t_1)) (app (x_1) (free-vars t_1))]
  [(free-vars (AND P_1 P_2)) (app (free-vars P_1) (free-vars P_2))]
  [(free-vars (OR P_1  P_2)) (app (free-vars P_1) (free-vars P_2))])


(define-metafunction λTR
  subst-oo : oo x oo -> oo
  [(subst-oo oo_1 x_1 Null) Null]
  [(subst-oo Null x_1 x_1) Null]
  [(subst-oo x_3 x_1 x_1) x_3])

(define-metafunction λTR
  subst-P : oo x P -> P
  [(subst-P Null x_1 (x_1 -: t_1)) TT]
  [(subst-P Null x_1 (x_1 -! t_1)) TT]
  [(subst-P o_1 x_1 (x_1 -: t_1)) (o_1 -: (subst-t o_1 x t_1))]
  [(subst-P o_1 x_1 (x_1 -! t_1)) (o_1 -! (subst-t o_1 x t_1))]
  [(subst-P oo_1 x_1 (x_2 -: t_1)) (x_2 -: t_1)
   (judgment-holds (<> x_1 x_2))
   (judgment-holds (not-in x_2 (free-vars t_1)))]
  [(subst-P oo_1 x_1 (x_2 -! t_1)) (x_2 -! t_1)
   (judgment-holds (<> x_1 x_2))
   (judgment-holds (not-in x_2 (free-vars t_1)))]
  [(subst-P oo_1 x_1 (x_2 -: t_1)) TT
   (judgment-holds (<> x_1 x_2))
   (judgment-holds (in x_2 (free-vars t_1)))]
  [(subst-P oo_1 x_1 (x_2 -! t_1)) TT
   (judgment-holds (<> x_1 x_2))
   (judgment-holds (in x_2 (free-vars t_1)))]
  [(subst-P oo_1 x_1 (AND P_1 P_2)) 
   (AND (subst-P oo_1 x_1 P_1) (subst-P oo_1 x_1 P_2))]
  [(subst-P oo_1 x_1 (OR P_1 P_2)) 
   (OR (subst-P oo_1 x_1 P_1) 
       (subst-P oo_1 x_1 P_2))]
  [(subst-P oo_1 x_1 TT) TT]
  [(subst-P oo_1 x_1 FF) FF])


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
  [(subst-t oo_1 x_1 (λ x_1 t_1 t_2 P_1 P_2 oo_2))
   (λ x_1 (subst-t oo_1 x_1 t_1) t_2 P_1 P_2 oo_2)]
  [(subst-t oo_1 x_1 (λ x_2 t_1 t_2 P_1 P_2 oo_2))
   (λ x_2 
     (subst-t oo_1 x_1 t_1)
     (subst-t oo_1 x_1 t_2)
     (subst-P oo_1 x_1 P_1)
     (subst-P oo_1 x_1 P_2)
     (subst-oo oo_1 x_1 oo_2))
   (judgment-holds (<> x_1 x_2))])


(module+ test
  (check-equal? (term (subst-oo Null x x)) (term Null))
  (check-equal? (term (subst-P x x (x -: Int))) (term (x -: Int)))
  (check-equal? (term (subst-P x y (y -: Int))) (term (x -: Int)))
  (check-equal? (term (subst-P Null x (y -: Int))) (term (y -: Int)))
  (check-equal? (term (subst-P Null y (y -: Int))) (term TT))

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
  (check-true (judgment-holds (proves [(x -: Int)] (x -: Int))))
  (check-true (judgment-holds (proves [(AND (x -: Int) (y -: F))] 
                                      (AND (y -: F) (x -: Int)))))
  (check-true (judgment-holds (proves [(x -: Int)] (OR (x -: Int) (x -: (U T F))))))
  (check-true (judgment-holds (proves [(x -: Int) (x -! Int)] FF)))
  (check-true (judgment-holds (proves [(x -: Int) (x -: Str)] FF)))
  (check-true (judgment-holds (proves [(x -: (U T F Int)) 
                                       (AND (x -! T) (x -: (U T Int)))] 
                                      (x -: Int))))
  (check-true (judgment-holds (proves [(OR (OR (z -: (U)) FF) (x -: Int))
                                       (OR (x -! Int) (y -: (U T F)))
                                       (OR (y -: Int) (z -: (U T F)))] 
                                      (z -: (U T F))))))

(define-judgment-form λTR
  #:mode (disj I)
  #:contract (disj P)
  [------------ "Disj"
   (disj (OR P_1 P_2))])

(define-judgment-form λTR
  #:mode (nondisj I)
  #:contract (nondisj P)
  [(where #f (disj P_1))
   ------------ "NonDisj"
   (nondisj P_1)])


(define-metafunction λTR
  normalize-P : P -> P
  [(normalize-P TT) TT]
  [(normalize-P FF) FF]
  [(normalize-P (o_1 -: t_1)) (o_1 -: t_1)]
  [(normalize-P (o_1 -! t_1)) (o_1 -! t_1)]
  [(normalize-P (AND P_1 P_2)) 
   (AND (normalize-P P_1) 
        (normalize-P P_2))
   (judgment-holds (nondisj P_1))
   (judgment-holds (nondisj P_2))]
  [(normalize-P (OR P_1 P_2))
   (OR (normalize-P P_1)
       (normalize-P P_2))]
  [(normalize-P (AND P_1 (OR P_2 P_3))) 
   (normalize-P (OR (normalize-P (AND P_1 P_2)) 
                    (normalize-P (AND P_1 P_3))))]
  [(normalize-P (AND (OR P_1 P_2) P_3)) 
   (normalize-P (OR (normalize-P (AND P_1 P_3)) 
                    (normalize-P (AND P_2 P_3))))
   (judgment-holds (nondisj P_3))])

(define-metafunction λTR
  norm-P : P -> P
  [(norm-P P_1) (norm-P (normalize-P P_1))
   (judgment-holds (<> P_1 (normalize-P P_1)))]
  [(norm-P P_1) P_1
   (where P_1 (normalize-P P_1))])


(define-metafunction λTR
    reduce-P : E P -> P
    [(reduce-P E_1 TT) TT]
    [(reduce-P E_1 FF) FF]
    [(reduce-P E_1 (x_1 -: t_1)) FF
     (judgment-holds (proves E_1 (x_1 -! t_1)))]
    [(reduce-P E_1 (x_1 -: t_1)) (x_1 -: t_1)
     (where #f (proves E_1 (x_1 -! t_1)))]
    [(reduce-P E_1 (x_1 -! t_1)) FF
     (judgment-holds (proves E_1 (x_1 -: t_1)))]
    [(reduce-P E_1 (x_1 -! t_1)) (x_1 -! t_1)
     (where #f (proves E_1 (x_1 -: t_1)))]
    [(reduce-P [P_3 ...] (AND P_1 P_2))
     (AND (reduce-P [P_2 P_3 ...] P_1) 
          (reduce-P [P_1 P_3 ...] P_2))]
    [(reduce-P E_1 (OR P_1 P_2))
     (OR (reduce-P E_1 P_1)
         (reduce-P E_1 P_2))])


(define-metafunction λTR
    simplify-P : P -> P
    [(simplify-P P_1) (reduce-P [] (norm-P P_1))])


(module+ test
  (check-equal? (term (reduce-P [] (AND (OR (x -: Int) 
                                            (x -: (U T F)))
                                        (x -! Int))))
                (term (AND (OR FF 
                               (x -: (U T F))) 
                           (x -! Int))))

  (check-equal? (term (reduce-P [] (AND (x -: Int) 
                                        (x -! Int))))
                (term (AND FF FF))))

(define-metafunction λTR
  δt : c -> t
  [(δt add1) (λ x Int Int TT FF Null)]
  [(δt +) (λ x Int (λ y Int Int TT FF Null) TT FF Null)]
  [(δt zero?) (λ x Int (U T F) TT TT Null)]
  [(δt int?) (λ x Top (U T F) (x -: Int) (x -! Int) Null)]
  [(δt str?) (λ x Top (U T F) (x -: Str) (x -! Str) Null)]
  [(δt str-len) (λ x Str Int TT FF Null)]
  [(δt error) (λ x Str (U) FF FF Null)]
  [(δt bool?) (λ x Top (U T F) (x -: (U T F)) (x -! (U T F)) Null)]
  [(δt proc?) (λ x Top (U T F) 
                (x -: (λ y (U) Top TT TT Null))
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


(define-judgment-form λTR
  #:mode (typeof I I O O O O)
  #:contract (typeof E e t P P oo)
  [-------------- "T-Num"
   (typeof E z Int TT FF Null)]
  
  [-------------- "T-Str"
   (typeof E string Str TT FF Null)]
  
  [-------------- "T-Const"
   (typeof E c_1 (δt c_1) TT FF Null)]
  
  [-------------- "T-True"
   (typeof E #t T TT FF Null)]
  
  [-------------- "T-False"
   (typeof E #f F FF TT Null)]
  
  [(proves E_1 (x_1 -: t_1))
   -------------- "T-AnnVar"
   (typeof E_1 (ann x_1 t_1) t_1 (x_1 -! F) (x_1 -: F) x_1)]
  
  [(typeof [(x_1 -: t_1-) P_0 ...] e_1 t_1+ P_1+ P_1- oo_1)
   -------------- "T-Abs"
   (typeof [P_0 ...]
           (λ ([x_1 : t_1-]) e_1)
           (λ x_1 t_1- t_1+ P_1+ P_1- oo_1)
           TT FF
           Null)]
  
  [(typeof E_1 e_1 (λ x_0 t_0- t_0+ P_0+ P_0- oo_0) P_1+ P_1- oo_1)
   (typeof E_1 e_2 t_2 P_2+ P_2- oo_2)
   (subtype t_2 t_0-)
   -------------- "T-App"
   (typeof E_1
           (e_1 e_2)
           (subst-t oo_2 x_0 t_0+)
           (subst-P oo_2 x_0 (simplify-P P_0+))
           (subst-P oo_2 x_0 (simplify-P P_0-))
           (subst-oo oo_2 x_0 oo_0))]
  
  [(typeof [P_0 ...] e_1 t_1 P_1+ P_1- oo_1)
   (typeof [P_1+ P_0 ...] e_2 t_2 P_2+ P_2- oo_2)
   (typeof [P_1- P_0 ...] e_3 t_3 P_3+ P_3- oo_3)
   ------------------------------ "T-If"
   (typeof [P_0 ...]
           (if e_1 e_2 e_3)
           (t-join t_2 t_3)
           (OR (AND P_1+ P_2+) 
               (AND P_1- P_3+))
           (OR (AND P_1+ P_2-) 
               (AND P_1- P_3-))
           (oo-join oo_2 oo_3))]
  
  [(typeof [P_0 ...] e_1 t_1 P_1+ P_1- oo_1)
   (where P_let (AND (x_1 -: t_1)
                     (OR (AND (x_1 -! F) P_1+) 
                         (AND (x_1 -: F) P_1-))))
   (typeof [P_let P_0 ...]
           e_2 t_2 P_2+ P_2- oo_2)
   -------------------------- "T-Let"
   (typeof [P_0 ...]
           (let ([x_1 e_1]) e_2)
           (subst-t oo_1 x_1 t_2)
           (subst-P oo_1 x_1 
                    (simplify-P (AND P_2+ P_let)))
           (subst-P oo_1 x_1 
                    (simplify-P (AND P_2- P_let)))
           (subst-oo oo_1 x_1 oo_2))])


(define-judgment-form λTR
  #:mode (typeof* I I I I I I)
  #:contract (typeof* E e t P P oo)
  [(typeof E_1 e_1 t_2 P_2+ P_2- oo_2)
   ;(eqv-type? t_2 t_1)
   (subtype t_2 t_1)
   (proves [P_2+] P_1+)
   (proves [P_2-] P_1-)
   (subobj oo_2 oo_1)
   -------------- "T-Subsume"
   (typeof* E_1 e_1 t_1 P_1+ P_1- oo_1)])

(define-metafunction λTR
  and : e e -> e
  [(and e_1 e_2) (if e_1 e_2 #f)])

(define-metafunction λTR
  or : e e -> e
  [(or e_1 e_2) (let ([tmp e_1]) 
                  (if (ann tmp (U T F))
                      (ann tmp (U T F))
                      e_2))])

(define-metafunction λTR
  Option : t -> t
  [(Option t_1) (U t_1 F)])


(module+ test

; Example 1
(check-true 
 (judgment-holds 
  (typeof* [(x -: Top)] 
           (if (int? (ann x Top))
               (add1 (ann x Int))
               0) 
           Int 
           TT TT
           Null)))

(check-true 
 (judgment-holds 
  (typeof* []
           (λ ([x : Int])
             (add1 (ann x Int)))
           (λ x Int Int TT FF Null)
           TT TT
           Null)))

(check-true 
 (judgment-holds 
  (typeof* [(x -: (U Str Int))] 
           (if (int? (ann x Top))
               (add1 (ann x Int))
               (str-len (ann x Str)))
           Int
           TT TT
           Null)))

(check-true 
 (judgment-holds 
  (typeof* [(x -: Top)]
           (int? (ann x Top))
           (U T F)
           (x -: Int) (x -! Int)
           Null)))

(check-true 
 (judgment-holds 
  (typeof* []
           (λ ([x : Top])
             (int? (ann x Top)))
           (λ x Top (U T F) (x -: Int) (x -! Int) Null)
           TT TT
           Null)))


;;Example 2
(check-true 
 (judgment-holds 
  (typeof* []
           (λ ([x : (U Str Int)])
             (if (int? (ann x Top))
                 (add1 (ann x Int))
                 (str-len (ann x Str))))
           (λ x (U Str Int) Int TT FF Null)
           TT FF
           Null)))

(check-true 
 (judgment-holds 
  (typeof* [(x -: Top)]
           (if (int? (ann x Top))
               #t
               (str? (ann x Top)))
           (U T F)
           (x -: (U Int Str)) (x -! (U Int Str))
           Null)))

;; Example 3
(check-true 
 (judgment-holds 
  (typeof* [(x -: (Option Str))]
           (if (ann x Top)
               (str-len (ann x Str))
               (error "string not found!"))
           Int
           TT FF
           Null)))


(check-true
 (judgment-holds 
  (typeof* [(x -: Top)]
           (let ([tmp (int? (ann x Top))]) 
             (ann tmp (U T F)))
           (U T F)
           (x -: Int) (x -! Int)
           Null)))

(check-true
 (judgment-holds 
  (typeof* [(x -: Top)]
           (let ([tmp (int? (ann x Top))]) 
             (if (ann tmp (U T F))
                 (ann tmp (U T F))
                 (str? (ann x Top))))
           (U T F)
           (x -: (U Int Str)) (x -! (U Int Str))
           Null)))

(check-true 
 (judgment-holds 
  (typeof* [(x -: Top)]
           (or (int? (ann x Top))
               (str? (ann x Top)))
           (U T F)
           (x -: (U Int Str)) (x -! (U Int Str))
           Null)))

; Example 4
(check-true (judgment-holds 
               (typeof* [(f -: (λ x (U Int Str) Int TT FF Null))
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
(check-true (judgment-holds (typeof* [(x -: Top)]
                                     (let ([tmp (str? (ann x Top))])
                                       (if (ann tmp Top)
                                           (ann tmp Top)
                                           (int? (ann x Top))))
                                     Top
                                     (x -: (U Str Int)) (x -! (U Str Int))
                                     Null)))

; Example 9
(check-true (judgment-holds (typeof* [(x -: Top)]
                                     (if (let ([tmp (int? (ann x Top))])
                                           (if (ann tmp Top)
                                               (ann tmp Top)
                                               (str? (ann x Top))))
                                         ((λ ([x : (U Str Int)])
                                            (if (int? (ann x Top))
                                                (add1 (ann x Int))
                                                (str-len (ann x Str))))
                                          (ann x (U Int Str)))
                                         0)
                                     Int
                                     TT FF
                                     Null)))

; Example 13
(check-true (judgment-holds (typeof* [(x -: Top) (y -: (U Int Str))]
                                     (if (and (int? (ann x Top)) (str? (ann y Top)))
                                         ((+ (ann x Int)) (str-len (ann y Str)))
                                         (if (int? (ann x Top))
                                             ((+ (ann x Int)) (ann y Int))
                                             0))
                                     Int
                                     TT FF
                                     Null)))

; Example 14
(check-true (judgment-holds (typeof* [(x -: Top)]
                                     (λ ([y : (U Int Str)])
                                       (if (and (int? (ann x Top)) (str? (ann y Top)))
                                         ((+ (ann x Int)) (str-len (ann y Str)))
                                         (if (int? (ann x Top))
                                             ((+ (ann x Int)) (ann y Int))
                                             0)))
                                     (λ x (U Str Int) Int TT FF Null)
                                     TT FF
                                     Null)))
) ; endof test
