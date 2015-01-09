#lang racket

(require redex "dtr-lang.rkt" "dtr-logic.rkt" "dtr-optypes.rkt")
(provide (all-defined-out))

;                                             ;;;; 
;                                            ;     
;  ;;;;;;;                           ;;;     ;     
;     ;    ;      ; ; ;;;     ;;;   ;   ;  ;;;;;;; 
;     ;     ;    ;  ;;   ;   ;   ; ;     ;   ;     
;     ;     ;    ;  ;    ;  ;    ; ;     ;   ;     
;     ;      ;  ;   ;    ;  ;;;;;; ;     ;   ;     
;     ;      ;  ;   ;    ;  ;      ;     ;   ;     
;     ;       ;;    ;;   ;  ;       ;   ;    ;     
;     ;       ;;    ; ;;;    ;;;;;   ;;;     ;     
;             ;     ;                              
;            ;      ;                              
;          ;;;      ;                              


(define-judgment-form λDTR
  #:mode (typeof I I O O)
  #:contract (typeof Γ e τ (ψ ψ oo))
  
  [-------------- "T-Int"
   (typeof Γ i (Int= i) (TT FF i))]
  
  [-------------- "T-Str"
   (typeof Γ string Str (TT FF Ø))]
  
  [-------------- "T-Const"
   (typeof Γ op (op-τ op) (TT FF Ø))]
  
  [-------------- "T-True"
   (typeof Γ #t #t (TT FF Ø))]
  
  [-------------- "T-False"
   (typeof Γ #f #f (FF TT Ø))]
  
  [(proves Γ (is x τ))
   -------------- "T-AnnVar"
   (typeof Γ (ann x τ) τ ((And: (! x #f) (is x τ)) 
                          (And: (is x #f) (is x τ)) 
                          (id x)))]
  
  [(typeof (env/sift+ψ* Γ (is x σ)) e τ (ψ_+ ψ_- oo))
   -------------- "T-Abs"
   (typeof Γ
           (λ (x : σ) e)
           (x : σ → τ (ψ_+ ψ_- oo))
           (TT FF Ø))]
  
  [(where/hidden #f ,(member (term e_1) '(car cdr vec)))
   (typeof Γ e_1 σ_λ (ψ_1+ ψ_1- oo_1))
   (where (x : σ_f → τ_f (ψ_f+ ψ_f- oo_f)) (exists/fun-τ σ_λ))
   (typeof Γ e_2 σ_2 (ψ_2+ ψ_2- oo_2))
   (subtype Γ (id (fresh-var Γ (e_1 e_2))) σ_2 σ_f)
   (where τ_f* (update-τ Γ τ_f (is x σ_2)))
   -------------- "T-App"
   (typeof Γ
           (e_1 e_2)
           (subst τ_f* oo_2 x)
           ((And: (subst ψ_f+ oo_2 x) (true-ψ τ_f*))
            (And: (subst ψ_f- oo_2 x) (false-ψ τ_f*))
            (subst oo_f oo_2 x)))]
  
  [(typeof Γ e_1 τ_1 (ψ_1+ ψ_1- oo_1))
   (typeof (env/sift+ψ* Γ ψ_1+) e_2 τ_2 (ψ_2+ ψ_2- oo_2))
   (typeof (env/sift+ψ* Γ ψ_1-) e_3 τ_3 (ψ_3+ ψ_3- oo_3))
   ------------------------------ "T-If"
   (typeof Γ
           (if e_1 e_2 e_3)
           (τ-join τ_2 τ_3)
           ((Or: (And: ψ_1+ ψ_2+) 
                 (And: ψ_1- ψ_3+))
            (Or: (And: ψ_1+ ψ_2-) 
                 (And: ψ_1- ψ_3-))
            (oo-join oo_2 oo_3)))]
  
  [(typeof Γ e_x τ (ψ_x+ ψ_x- oo_x))
   (where ψ (And: (is x τ)
                  (Or: (And: (! x #f)  ψ_x+) 
                       (And: (is x #f) ψ_x-))))
   (typeof (env/sift+ψ* Γ ψ) e σ (ψ_+ ψ_- oo))
   -------------------------- "T-Let"
   (typeof Γ
           (let (x e_x) e)
           (subst σ oo_x x)
           ((subst (And: ψ_+ ψ) oo_x x)
            (subst (And: ψ_- ψ) oo_x x)
            (subst oo oo_x x)))]
  
  [(typeof Γ e_1 τ (ψ_1+ ψ_1- oo_1))
   (typeof Γ e_2 σ (ψ_2+ ψ_2- oo_2))
   ------------------------- "T-Cons"
   (typeof Γ (cons e_1 e_2) (τ × σ) (TT FF Ø))]

  [(typeof Γ e σ_c (ψ_+ ψ_- oo))
   (where (τ × σ) (exists/pair-τ σ_c))
   (where/hidden x (fresh-var Γ (car e)))
   ------------------------- "T-Car"
   (typeof Γ
           (car e) 
           τ
           ((subst (And: (((CAR) @ x) ¬ #f)
                         (And: (((CAR) @ x) ~ τ)
                               (true-ψ τ))) 
                   oo x)
            (subst (And: (((CAR) @ x) ~ #f)
                         (And: (((CAR) @ x) ~ τ)
                               (false-ψ τ)))
                   oo x)
            (subst ((CAR) @ x) oo x)))]
  
  [(typeof Γ e σ_c (ψ_+ ψ_- oo))
   (where (τ × σ) (exists/pair-τ σ_c))
   (where/hidden x (fresh-var Γ (cdr e)))
   ------------------------- "T-Cdr"
   (typeof Γ
           (cdr e) 
           σ
           ((subst (And: (((CDR) @ x) ¬ #f)
                         (And: (((CDR) @ x) ~ σ)
                               (true-ψ σ))) 
                   oo x)
            (subst (And: (((CDR) @ x) ~ #f)
                         (And: (((CDR) @ x) ~ σ)
                               (false-ψ σ)))
                   oo x)
            (subst ((CDR) @ x) oo x)))]
  
  [(typeof Γ e_0 τ_0 (ψ_0+ ψ_0- oo_0)) ...
   (typeof Γ e_i τ_i (ψ_i+ ψ_i- oo_i))
   (where τ (τ-join τ_0 ... τ_i))
   (where/hidden i ,(length (term (e_0 ... e_i))))
   (where x (fresh-var Γ (vec e_0 ... e_i)))
   ------------------------- "T-Vec"
   (typeof Γ (vec e_0 ... e_i) (x : (♯ τ) where (Φ= i (o-len (id x))))
           (TT FF Ø))]
  
  [(typeof Γ e_1 σ_v (ψ_1+ ψ_1- oo_1))
   (typeof Γ e_2 σ_i (ψ_2+ ψ_2- oo_2))
   (where (♯ τ) (exists/vec-τ σ_v))
   (where x (fresh-var Γ (vec-ref e_1 e_2)))
   (where o_1 ,(fresh-if-needed (term oo_1)))
   (where o_2 ,(fresh-if-needed (term oo_2)))
   (subtype (env/sift+ψ* Γ (o_1 ~ σ_v)) o_2 σ_i (IntRange 0 (+ -1 (o-len o_1))))
   ------------------------- "T-VecRef"
   (typeof Γ (vec-ref e_1 e_2) τ 
           ((true-ψ τ) (false-ψ τ) Ø))])


(define-judgment-form λDTR
  #:mode (TypeOf I I I O)
  #:contract (TypeOf Γ e τ (ψ ψ oo))
  [-------------- "T-Int"
   (TypeOf Γ i (Int= i) (TT FF i))]
  
  [-------------- "T-Str"
   (TypeOf Γ string Str (TT FF Ø))]
  
  [-------------- "T-Const"
   (TypeOf Γ op (op-τ op) (TT FF Ø))]
  
  [-------------- "T-True"
   (TypeOf Γ #t #t (TT FF Ø))]
  
  [-------------- "T-False"
   (TypeOf Γ #f #f (FF TT Ø))]
  
  [(proves Γ (is x τ))
   -------------- "T-AnnVar"
   (TypeOf Γ (ann x τ) τ ((! x #f) (is x #f) (id x)))]
  
  [(TypeOf (env+ψ Γ (is x σ)) e τ (ψ_+ ψ_- oo))
   -------------- "T-Abs"
   (TypeOf Γ (λ (x : σ) e) (x : σ → τ (ψ_+ ψ_- oo)) (TT FF Ø))]
  
  [(where/hidden #f ,(member (term e_1) '(car cdr vec)))
   (where/hidden (x : σ → τ (ψ_f+ ψ_f- oo_f)) ,(gensym))
   (where/hidden σ_2 ,(gensym))
   (TypeOf Γ e_1 (x : σ → τ (ψ_f+ ψ_f- oo_f)) (ψ_1+ ψ_1- oo_1))
   (TypeOf Γ e_2 σ_2 (ψ_2+ ψ_2- oo_2))
   (where τ_* (subst (update-τ Γ τ (is x σ_2)) oo_2 x)) ;;? subsumption?
   -------------- "T-App"
   (TypeOf Γ (e_1 e_2) τ_* (subt (ψ_f+ ψ_f- oo_f) oo_2 x))]
  
  [(where/hidden τ_1 ,(gensym))
   (TypeOf Γ e_1 τ_1 (ψ_1+ ψ_1- oo_1))
   (TypeOf (env+ψ Γ ψ_1+) e_2 τ (ψ_+ ψ_- oo))
   (TypeOf (env+ψ Γ ψ_1-) e_3 τ (ψ_+ ψ_- oo))
   ------------------------------ "T-If"
   (TypeOf Γ (if e_1 e_2 e_3) τ (ψ_+ ψ_- oo))]
  
  [(where/hidden τ ,(gensym))
   (TypeOf Γ e_x τ (ψ_x+ ψ_x- oo_x))
   (where ψ (And: (is x τ)
                  (Or: (And: (! x #f)  ψ_x+) 
                       (And: (is x #f) ψ_x-))))
   (TypeOf (env+ψ Γ ψ) e σ (ψ_+ ψ_- oo))
   -------------------------- "T-Let"
   (TypeOf Γ (let (x e_x) e) (subst σ oo_x x) (subst (ψ_+ ψ_- oo) oo_x x))]
  
  [(where/hidden (τ σ) ,(gensym))
   (TypeOf Γ e_1 τ (ψ_1+ ψ_1- oo_1))
   (TypeOf Γ e_2 σ (ψ_2+ ψ_2- oo_2))
   ------------------------- "T-Cons"
   (TypeOf Γ (cons e_1 e_2) (τ × σ) (TT FF Ø))]

  [(where/hidden (τ σ) ,(gensym))
   (TypeOf Γ e (τ × σ) (ψ_+ ψ_- oo))
   (where/hidden x (fresh-var Γ (car e)))
   (where o (o-car (id x)))
   ------------------------- "T-Car"
   (TypeOf Γ (car e) τ (subst ((o ¬ #f) (o ~ #f) o) oo x))]
  
  [(where/hidden (τ σ) ,(gensym))
   (TypeOf Γ e (τ × σ) (ψ_+ ψ_- oo))
   (where/hidden x (fresh-var Γ (cdr e)))
   (where o (o-cdr (id x)))
   ------------------------- "T-Cdr"
   (TypeOf Γ (cdr e) σ (subst ((o ¬ #f) (o ~ #f) o) oo x))]
  
  [(where/hidden τ ,(gensym))
   (TypeOf Γ e_1 τ (ψ_1+ ψ_1- oo_1)) ...
   (TypeOf Γ e_i τ (ψ_i+ ψ_i- oo_i)) 
   (where/hidden i ,(length (term (e_1 ... e_i))))
   (where/hidden x (fresh-var Γ (vec e_1 ... e_i)))
   (where o (o-len (id x)))
   ------------------------- "T-Vec"
   (TypeOf Γ (vec e_1 ... e_i) (x : (♯ τ) where (Φ= i o)) (TT FF Ø))]
  
  [(where/hidden (τ σ_i) ,(gensym))
   (TypeOf Γ e_1 (♯ τ) (ψ_1+ ψ_1- oo_1))
   (TypeOf Γ e_2 σ_i (ψ_2+ ψ_2- oo_2))
   (where/hidden x (fresh-var Γ (vec-ref e_1 e_2)))
   (where o_1 ,(fresh-if-needed (term oo_1)))
   (where o_2 ,(fresh-if-needed (term oo_2)))
   (subtype (env+ψ Γ (o_1 ~ (♯ τ))) o_2 σ_i (IntRange 0 (+ -1 (o-len o_1))))
   ------------------------- "T-VecRef"
   (TypeOf Γ (vec-ref e_1 e_2) τ ((true-ψ τ) (false-ψ τ) Ø))]
  
  [(where/hidden (τ_1 ψ_2+ ψ_2- oo_2) ,(gensym))
   (TypeOf Γ e τ_1 (ψ_1+ ψ_1- oo_1))
   (proves (env+ψ Γ ψ_1+) ψ_2+)
   (proves (env+ψ Γ ψ_1-) ψ_2-)
   (where/hidden o_fresh (id (fresh-var Γ e τ_1 (ψ_1+ ψ_1- oo_1))))
   (subtype Γ o_fresh τ_1 τ_2 )
   (subobj oo_1 oo_2)
   -------------- "T-Subsume"
   (TypeOf Γ e τ_2 (ψ_2+ ψ_2- oo_2))])


