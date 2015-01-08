#lang racket

(require redex "fme-bridge.rkt")
(provide (all-defined-out))

(define-language λDTR
  [x y z  ::= variable-not-otherwise-mentioned]
  [i      ::= integer]
  [b      ::= boolean]
  [e      ::= (ann x τ) (e e) (λ (x : τ) e) (if e e e) 
              op b i string (let (x e) e) (cons e e) (vec e ...)
              (car e) (cdr e) (vec-ref e e)]
  [op     ::= add1 zero? int? str? bool? proc? 
              str-len vec-len + (* i) error cons? vec?]
  [pe     ::= CAR CDR LEN]
  [π      ::= (pe ...)]
  [o      ::= i (π @ x) (* i o) (+ o o)]
  [Φ      ::= ((≤ o o) ...)] 
  [oo     ::= o Ø]
  [τ σ    ::= Top #t #f Int Str (U τ ...) (x : τ → τ (ψ ψ oo)) 
              (τ × τ) (♯ τ) (x : τ where Φ)]
  [?      ::= -: -!]
  [δ      ::= (o ? τ)]
  [ψ      ::= δ (ψ ∧ ψ) (ψ ∨ ψ) TT FF Φ]
  [δ*     ::= (δ ...)]
  [ψ*     ::= (ψ ...)]
  [Γ      ::= (env Φ δ* ψ*)])

(define-metafunction λDTR
  empty-env : -> Γ
  [(empty-env) (env () () ())])

(define-metafunction λDTR
  env+Φ : Γ Φ -> Γ
  [(env+Φ (env Φ δ* ψ*) Φ_new) (env (app Φ Φ_new) δ* ψ*)])

(define-metafunction λDTR
  env+ψ* : Γ ψ ... -> Γ
  [(env+ψ* (env Φ δ* ψ*) ψ ...) (env Φ δ* (app ψ* (ψ ...)))])

(define-metafunction λDTR
  env/sift+ψ* : Γ ψ ... -> Γ
  [(env/sift+ψ* (env Φ δ* ψ*) ψ ...) (env Φ δ* (app ψ* (sift-ψ* (ψ ...))))])

(define-metafunction λDTR
  env: : ψ ... -> Γ
  [(env: ψ ...) (env () () (sift-ψ* (ψ ...)))])

(define-judgment-form λDTR
  #:mode (fme-imp I I)
  #:contract (fme-imp Φ Φ)
  [(where #t ,(redex-fme-imp? (term Φ_1) (term Φ_2)))
   ----------- "FME-Imp"
   (fme-imp Φ_1 Φ_2)])

(define-judgment-form λDTR
  #:mode (fme-sat I)
  #:contract (fme-sat Φ)
  [(where #t ,(redex-fme-sat? (term Φ)))
   ----------- "FME-Sat"
   (fme-sat Φ)])

(define-metafunction λDTR
  fme-elim : Φ x -> Φ
  [(fme-elim Φ x) ,(sli->redex (fme-elim-var (redex->fme (term Φ)) (term x)))])

(define-judgment-form λDTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj o o)]
  
  [(lexp-equal o_1 o_2)
   ------------------- "SO-Equal"
   (subobj o_1 o_2)]
  
  [------------------- "SO-Top"
   (subobj oo Ø)])

(define-judgment-form λDTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [(subtype/ctx (empty-env) (id (fresh-var σ τ)) σ τ)
   --------------------------- "S-EmptyCtx"
   (subtype σ τ)])

;; Φ : what linear inequalities currently hold
;; o : who are we talking about
;; τ : subtype
;; σ : supertype
(define-judgment-form λDTR
  #:mode (subtype/ctx I I I I)
  #:contract (subtype/ctx Γ o τ σ)
  [--------------- "S-Refl"
   (subtype/ctx Γ o τ τ)]
  
  [--------------- "S-Top"
   (subtype/ctx Γ o τ Top)]
  
  [(subtype/ctx Γ o σ τ)
   --------------- "S-UnionSuper"
   (subtype/ctx Γ o σ (U τ_1 ... τ τ_2 ...))]
  
  [(subtype/ctx Γ o τ σ) ...
   --------------- "S-UnionSub"
   (subtype/ctx Γ o (U τ ...) σ)]
  
  [(subtype/ctx Γ (o-car o) τ_1 τ_2)
   (subtype/ctx Γ (o-cdr o) σ_1 σ_2)
   ----------------- "S-Pair"
   (subtype/ctx Γ o (τ_1 × σ_1) (τ_2 × σ_2))]
  
  [(subtype/ctx Γ (id (fresh-var Γ o τ σ)) τ σ)
   ----------------- "S-Vec"
   (subtype/ctx Γ o (♯ τ) (♯ σ))]
  
  [(where z (fresh-var Γ o
                      (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
                      (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2))))
   (subtype/ctx Γ (id z) σ_2 σ_1) 
   (subtype/ctx Γ (id z) (subst τ_1 (id y) x) τ_2) 
   (proves (env/sift+ψ* Γ (subst ψ_1+ (id y) x)) ψ_2+)
   (proves (env/sift+ψ* Γ (subst ψ_1- (id y) x)) ψ_2-)
   (subobj (subst oo_1 (id y) x) oo_2)
   ------------------------------------------ "S-Abs"
   (subtype/ctx Γ o
                (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
                (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2)))]
  
  [(proves (env (app Φ (subst Φ_x o x)) 
                δ* 
                (ext ψ* (sift-ψ (o -: (subst τ_x o x)))))
           (o -: τ))
   ------------------- "S-Refine-Sub"
   (subtype/ctx (env Φ δ* ψ*) o (x : τ_x where Φ_x) τ)]
  
  [(proves (env/sift+ψ* Γ (o -: τ))
           (And: (o -: (subst τ_y o y)) 
                 (subst Φ_y o y)))
   ;(where #f (is-Refine τ)) TODO remove if all tests pass
   ------------------- "S-Refine-Super"
   (subtype/ctx Γ o τ (y : τ_y where Φ_y))])

(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  
  [(subtype/ctx (env Φ (δ_1 ... δ_2 ...) ()) o_1 τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Sub"
   (proves (env Φ (δ_1 ... (o_1 -: τ) δ_2 ...) ()) 
           (o_2 -: σ))]
  
  [(subtype/ctx (env Φ [δ_1 ... δ_2 ...] ()) o_1 σ τ)
   (lexp-equal o_1 o_2)
   ---------------- "L-SubNot"
   (proves (env Φ (δ_1 ... (o_1 -! τ) δ_2 ...) ()) 
           (o_2 -! σ))]
  
  [(type-conflict Φ τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Conflict"
   (proves (env Φ (δ_1 ... (o_1 -: τ) δ_2 ...) ()) 
           (o_2 -! σ))]
  
  [(fme-imp Φ Φ_1)
   ---------------- "L-FME"
   (proves (env Φ δ* ()) 
           Φ_1)]
  
  [(where #f (fme-sat Φ))
   ---------------- "L-FME-Unsat"
   (proves (env Φ δ* ()) 
           ψ)]
  
  [---------------------- "L-Bot"
   (proves (env Φ (δ_1 ... (o -: (U)) δ_2 ...) ()) 
           ψ)]
  
  [---------------------- "L-True"
   (proves Γ TT)]
  
  [(proves (env Φ δ* (ψ_1 ...)) 
           ψ)
   ---------------------- "L-Weaken"
   (proves (env Φ δ* (TT ψ_1 ...)) 
           ψ)]
  
  [---------------------- "L-ExFalso"
   (proves (env Φ δ* (FF ψ_1 ...)) 
           ψ)]
  
  [(proves (env Φ δ* [ψ_1 ψ_2 ψ_3 ...]) 
           ψ)
   ---------------------- "L-Simp"
   (proves (env Φ δ* ((ψ_1 ∧ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(proves (env Φ δ* ()) ψ_1)
   (proves (env Φ δ* ()) ψ_2)
   ---------------------- "L-Conj"
   (proves (env Φ δ* ()) 
           (ψ_1 ∧ ψ_2))]
  
  [(proves (env Φ δ* (ψ_1 ψ_3 ...)) 
           ψ)
   (proves (env Φ δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-DisjElim"
   (proves (env Φ δ* ((ψ_1 ∨ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(proves (env Φ δ* ()) ψ_1)
   ---------------------- "L-Add-L"
   (proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(proves (env Φ δ* ()) 
           ψ_2)
   ---------------------- "L-Add-R"
   (proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(proves (env (app Φ Φ_1) δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-SLI"
   (proves (env Φ δ* (Φ_1 ψ_2 ψ_3 ...)) 
           ψ)]
  
  [(where Φ_2 (app Φ Φ_1))
   (proves (env Φ_2 (Φ-update-δ* δ* Φ_2) ()) 
           ψ)
   ---------------------- "L-SLI/Φ"
   (proves (env Φ δ* (Φ_1)) 
           ψ)]
  
  [(contains-non-δ (ψ_2 ...))
   (proves (env Φ δ* (ψ_2 ... δ_1)) 
           ψ)
   ---------------------- "L-Delay-δ"
   (proves (env Φ δ* (δ_1 ψ_2 ...)) 
           ψ)]
  
  [(proves (env Φ
                (ext (update* Φ (ext δ*) δ_1) δ_1)
                (update* Φ (δ_2 δ_3 ...) δ_1))
           ψ)
   ---------------------- "L-Update*"
   (proves (env Φ δ* (δ_1 δ_2 δ_3 ...)) 
           ψ)]
  
  [(proves (env Φ
                (Φ-update-δ* (ext (update* Φ δ* δ) δ) Φ)
                ())
           ψ)
   ---------------------- "L-Update*/Φ"
   (proves (env Φ δ* (δ)) 
           ψ)])


(define-judgment-form λDTR
  #:mode (is-δ I)
  #:contract (is-δ ψ)
  [------------ "Is-δ"
   (is-δ δ)])

(define-judgment-form λDTR
  #:mode (contains-non-δ I)
  #:contract (contains-non-δ ψ*)
  [(where #f (is-δ ψ_2))
   ------------ "Contains-Non-δ"
   (contains-non-δ (ψ_1 ... ψ_2 ψ_3 ...))])

(define-metafunction λDTR
  π-update : Φ ? τ ? σ π -> τ ;; TODO all Φ's in update, rest, rem
  ;; updates CAR/CDR
  [(π-update Φ ?_τ τ ?_σ σ [pe ... CAR])
   (π-update Φ ?_τ τ ?_σ (σ × Top) [pe ... ])]
  
  [(π-update Φ ?_τ τ ?_σ σ [pe ... CDR])
   (π-update Φ ?_τ τ ?_σ (Top × σ) [pe ... ])]
  
  ;; updates LEN
  [(π-update Φ ?_τ τ ?_σ σ [pe ... LEN])
   (π-update Φ ?_τ τ ?_σ (♯ Top) [pe ... ])]
  
  ;; restrict
  [(π-update Φ -: τ -: σ ()) (restrict Φ τ σ)]
  
  ;; remove
  [(π-update Φ -: τ -! σ ()) (remove Φ τ σ)]
  [(π-update Φ -! τ -: σ ()) τ] ; can't flip them and remove, since τ's 
                                ; boolean is fixed by caller already
  ; negation union
  [(π-update Φ -! τ -! σ ()) σ
   (judgment-holds (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))]
  [(π-update Φ -! τ -! σ ()) τ
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))
   (judgment-holds (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) σ τ))]
  [(π-update Φ -! τ -! σ ()) (U: τ σ)
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) σ τ))])


(define-metafunction λDTR
  restrict : Φ τ σ -> τ
  ;; No common value
  [(restrict Φ τ σ) (U)
   (judgment-holds (type-conflict Φ τ σ))]
  
  ;; Refinements
  [(restrict Φ (x : τ_x where Φ_x) (y : τ_y where Φ_y))
   (x : (restrict Φ τ_x τ_y) where (app Φ_x (subst Φ_y (id x) y)))
   (where/hidden #f (type-conflict Φ (x : τ_x where Φ_x) (y : τ_y where Φ_y)))]
  [(restrict Φ (x : τ_x where Φ_x) τ)
   (x : (restrict Φ τ_x τ) where Φ_x)
   (where/hidden #f (is-Refine τ))
   (where/hidden #f (type-conflict Φ (x : τ_x where Φ_x) τ))]
  [(restrict Φ τ (y : τ_y where Φ_y)) (y : (restrict Φ τ τ_y) where Φ_y)
   (where/hidden #f (is-Refine τ))
   (where/hidden #f (type-conflict Φ τ (y : τ_y where Φ_y)))]
  
  ;; Unions
  [(restrict Φ (U τ ...) σ) (U: ,@(map (λ (t) (term (restrict Φ ,t σ))) (term (τ ...))))
   (where/hidden #f (type-conflict () (U τ ...) σ))]
  
  [(restrict Φ τ (U σ ...)) (U: ,@(map (λ (t) (term (restrict Φ τ ,t))) (term (σ ...))))
   (where/hidden #f (is-U τ))
   (where/hidden #f (type-conflict Φ τ (U σ ...)))]
  
  ;; Pairs
  [(restrict Φ (τ_0 × σ_0) (τ_1 × σ_1)) (Pair: (restrict Φ τ_0 τ_1) (restrict Φ σ_0 σ_1))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ_0 σ_0 τ_1 σ_1)) (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(restrict Φ (♯ τ) (♯ σ)) (Vec: (restrict Φ τ σ))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) (♯ τ) (♯ σ)))]
  
  ;; else if τ <: σ
  [(restrict Φ τ σ) τ
   (judgment-holds (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))]
  
  ;; else
  [(restrict Φ τ σ) σ
   (where #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))])

;; remove
(define-metafunction λDTR
  remove : Φ τ σ -> τ
  ;; τ_1 <: τ_2
  [(remove Φ τ σ) (U)
   (judgment-holds (subtype τ σ))]
  
  ;; Union
  [(remove Φ (U τ ...) σ) (U: ,@(map (λ (t) (term (remove Φ ,t σ))) (term (τ ...))))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ (U τ ...) σ)) (U τ ...) σ))]
  
  ;; Refinement
  [(remove Φ (x : τ where Φ_x) σ) (x : (remove Φ τ σ) where Φ_x)
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ (x : τ where Φ_x) σ)) (x : τ where Φ_x) σ))
   (where/hidden #f (is-Refine σ))]
  
  ;; Pairs
  [(remove Φ (τ_0 × σ_0) (τ_1 × σ_1)) (Pair: (remove Φ τ_0 τ_1) 
                                             (remove Φ σ_0 σ_1))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ (τ_0 × σ_0) (τ_1 × σ_1))) (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(remove Φ (♯ τ) (♯ σ)) (Vec: (remove Φ τ σ))
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ (♯ τ) (♯ σ))) (♯ τ) (♯ σ)))]
  
  ;; non-special-case
  [(remove Φ τ σ) τ
   (where/hidden #f (subtype/ctx (env Φ () ()) (id (fresh-var Φ τ σ)) τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-Refine τ))
   (where/hidden #f ,(and (term (is-Pair τ)) (term (is-Pair σ))))
   (where/hidden #f ,(and (term (is-Vec τ)) (term (is-Vec σ))))])

(define-judgment-form λDTR
  #:mode (path-postfix I I)
  #:contract (path-postfix o o)
  ;; lhs is a postfix of the rhs object 
  ;; (i.e. rhs can update lhs)
  [------------------ "Path-Postfix"
   (path-postfix ((pe_2 ...) @ x) 
                 ((pe_1 ... pe_2 ...) @ x))])

(define-judgment-form λDTR
  #:mode (lexp-equal I I)
  #:contract (lexp-equal o o)
  [----------- "LExp-Equal-Refl"
   (lexp-equal o o)]
  [(where #t (redex-sli-equal? o_1 o_2))
   ----------- "LExp-Equal"
   (lexp-equal o_1 o_2)])

;; update type info in lhs w/ rhs if applicable
(define-metafunction λDTR
  τ-update : Φ δ δ -> δ
  ;; overlapping paths, update w/ path
  [(τ-update Φ 
             (((pe_τ ...) @ x) ?_τ τ) 
             (((pe_σ ... pe_τ ...) @ x) ?_σ σ))
   (((pe_τ ...) @ x) ?_τ (π-update Φ ?_τ τ ?_σ σ (pe_σ ...)))]
  
  ;; equal linear expressions, update types w/ empty path
  [(τ-update Φ (o_τ ?_τ τ) (o_σ ?_σ σ))
   (o_τ ?_τ (π-update Φ ?_τ τ ?_σ σ ()))
   (judgment-holds (lexp-equal o_τ o_σ))]
  
  ;; incompatible objects, no-op
  [(τ-update Φ (o_τ ?_τ τ) (o_σ ?_σ σ)) (o_τ ?_τ τ)
   (where #f (path-postfix o_τ o_σ))
   (where #f (lexp-equal o_τ o_σ))])

(define-metafunction λDTR
  ψ-update : Φ ψ δ -> ψ
  [(ψ-update Φ TT δ) TT]
  [(ψ-update Φ FF δ) FF]
  [(ψ-update Φ δ δ_new) (τ-update Φ δ δ_new)]
  [(ψ-update Φ (ψ_1 ∧ ψ_2) δ_new) (And: (ψ-update Φ ψ_1 δ_new) 
                                        (ψ-update Φ ψ_2 δ_new))]
  [(ψ-update Φ (ψ_1 ∨ ψ_2) δ_new) (Or:  (ψ-update Φ ψ_1 δ_new) 
                                        (ψ-update Φ ψ_2 δ_new))]
  [(ψ-update Φ_1 Φ_2 δ) Φ_2])

(define-metafunction λDTR
  update* : Φ ψ* δ -> ψ*
  [(update* Φ ψ* δ)
   ,(map (λ (ψ) (term (ψ-update Φ ,ψ δ))) (term ψ*))])


(define-judgment-form λDTR
  #:mode (common-val I I I)
  #:contract (common-val Φ τ τ)
  [------------------ "CV-Eq"
   (common-val Φ τ τ)]
  
  [------------------ "CV-Top-lhs"
   (common-val Φ Top τ)]
  
  [------------------ "CV-Top-rhs"
   (common-val Φ τ Top)]
  
  [(common-val Φ τ σ)
   ------------------ "CV-Union-lhs"
   (common-val Φ (U τ_1 ... τ τ_2 ...) σ)]
  
  [(common-val Φ τ σ)
   (where/hidden #f (is-U τ))
   ------------------ "CV-Union-rhs"
   (common-val Φ τ (U σ_1 ... σ σ_2 ...))]
  
  [(common-val Φ τ_1 τ_2)
   (common-val Φ σ_1 σ_2)
   -------------------- "CV-Pair"
   (common-val Φ (τ_1 × σ_1) (τ_2 × σ_2))]
  
  [(common-val Φ τ σ)
   -------------------- "CV-Vec"
   (common-val Φ (♯ τ) (♯ σ))]
  
  [------------------ "CV-Abs"
   (common-val Φ (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1)) 
                 (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2)))]
  
  [(fme-sat (app Φ Φ_x))
   (common-val Φ τ σ)
   (not-Refine σ)
   ----------------- "CV-Refine-L"
   (common-val Φ (x : τ where Φ_x) σ)]
  
  [(fme-sat (app Φ Φ_y))
   (common-val Φ τ σ)
   (not-Refine τ)
   ----------------- "CV-Refine-R"
   (common-val Φ τ (y : σ where Φ_y))]
  
  [(where o_f (id (fresh-var Φ 
                            (x : τ where Φ_x) 
                            (y : σ where Φ_y))))
   (fme-sat (app (subst Φ_x o_f x) 
                 (subst Φ_y o_f y)
                 Φ))
   (common-val Φ τ σ)
   ----------------- "CV-Refine"
   (common-val Φ (x : τ where Φ_x) 
                 (y : σ where Φ_y))])

(define-judgment-form λDTR
  #:mode (type-conflict I I I)
  #:contract (type-conflict Φ τ τ)
  [(where #f (common-val Φ τ σ))
   --------------- "TC-Conflict"
   (type-conflict Φ τ σ)])


(define-judgment-form λDTR
  #:mode (is-U I)
  #:contract (is-U τ)
  [-------------- "IsUnion"
   (is-U (U τ ...))])

(define-judgment-form λDTR
  #:mode (is-Pair I)
  #:contract (is-Pair τ)
  [-------------- "IsPair"
   (is-Pair (τ × σ))])

(define-judgment-form λDTR
  #:mode (is-Vec I)
  #:contract (is-Vec τ)
  [-------------- "IsVec"
   (is-Vec (♯ τ))])

(define-judgment-form λDTR
  #:mode (not-U I)
  #:contract (not-U τ)
  [(where #f (is-U τ))
   -------------- "NonU"
   (not-U τ)])

(define-judgment-form λDTR
  #:mode (is-Refine I)
  #:contract (is-Refine τ)
  [-------------- "IsRefine"
   (is-Refine (x : τ where Φ))])

(define-judgment-form λDTR
  #:mode (not-Refine I)
  #:contract (not-Refine τ)
  [(where #f (is-Refine τ))
   -------------- "NonU"
   (not-Refine τ)])

(define-metafunction λDTR 
  app : (any ...) ... -> (any ...)
  [(app (any_1 ...)) (any_1 ...)]
  [(app (any_1 ...) (any_2 ...) ...) (app (any_1 ... any_2 ...) ...)])

;; substitute oo_new for x in the first argument
;; USE THIS ONE! this will do dnf simplification
;; when nullifying in props, which is a *must*
(define-metafunction λDTR
  subst : any oo x -> any
  [(subst oo oo_new x) (subst-oo oo       oo_new x)]
  [(subst ψ  Ø  x)     (subst-ψ  (dnf ψ)  Ø x)]
  [(subst ψ  o_new  x) (subst-ψ  ψ        o_new x)]
  [(subst τ  oo_new x) (subst-τ  τ        oo_new x)])

(define-metafunction λDTR
  And: : ψ ψ -> ψ
  [(And: TT ψ) ψ]
  [(And: ψ TT) ψ]
  [(And: FF ψ) FF]
  [(And: ψ FF) FF]
  [(And: ψ_l ψ_r) (ψ_l ∧ ψ_r)
   (judgment-holds (<> TT ψ_l))
   (judgment-holds (<> TT ψ_r))
   (judgment-holds (<> FF ψ_l))
   (judgment-holds (<> FF ψ_r))])

(define-metafunction λDTR
  Or: : ψ ψ -> ψ
  [(Or: TT ψ) TT]
  [(Or: ψ TT) TT]
  [(Or: FF ψ) ψ]
  [(Or: ψ FF) ψ]
  [(Or: ψ_l ψ_r) (ψ_l ∨ ψ_r)
   (judgment-holds (<> TT ψ_l))
   (judgment-holds (<> TT ψ_r))
   (judgment-holds (<> FF ψ_l))
   (judgment-holds (<> FF ψ_r))])

(define-metafunction λDTR
  Type: : o ? τ -> ψ
  [(Type: o -: τ) FF
   (judgment-holds (subtype τ (U)))]
  [(Type: o -: τ) (o -: τ)
   (where #f (subtype τ (U)))]
  [(Type: o -! τ) (o -! τ)])

(define-metafunction λDTR
  +: : oo oo -> oo
  [(+: Ø oo) Ø]
  [(+: oo Ø) Ø]
  [(+: 0 o) o]
  [(+: o 0) o]
  [(+: i_l i_r) ,(+ (term i_l) (term i_r))]
  [(+: o_l o_r) (+ o_l o_r)
   (side-condition (nand (exact-integer? (term o_l))
                         (exact-integer? (term o_r))))])

(define-metafunction λDTR
  *: : oo oo -> oo
  [(*: Ø oo) Ø]
  [(*: oo Ø) Ø]
  [(*: i_l i_r) ,(* (term i_l) (term i_r))]
  [(*: 0 o) 0]
  [(*: 1 o) o]
  [(*: i o) (* i o)
   (side-condition (nor (exact-integer? (term o))
                        (= 0 (term i))
                        (= 1 (term i))))]
  [(*: o i) (*: i o)
   (where #f (exact-integer? (term o)))]
  [(*: o_l o_r) Ø
   (side-condition (not (exact-integer? (term oo_l))))
   (side-condition (not (exact-integer? (term oo_r))))])

;; substitution in oo
;; will null out completely invalid combinations 
;; (e.g. creating a linear expression w/ a non-empty path)
(define-metafunction λDTR
  subst-oo : oo oo x -> oo
  ;; null -> null
  [(subst-oo Ø oo_new x) Ø]
  ;; matched obj w/ empty path
  [(subst-oo (() @ x) oo_new x) oo_new]
  ;; null into obj
  [(subst-oo (π @ x) Ø x) Ø]
  [(subst-oo (π @ x) oo y) (π @ x)
   (judgment-holds (<> x y))]
  ;; obj into obj, path join
  [(subst-oo ([pe_0 pe_1 ...] @ x) (π_y @ y) x) ((app [pe_0 pe_1 ...] π_y) @ y)]
  ;; invalid obj/linear combinations, resulting in Ø
  [(subst-oo ([pe_0 pe_1 ...] @ x) i x) Ø]
  [(subst-oo ([pe_0 pe_1 ...] @ x) (* i o) x) Ø]
  [(subst-oo ((pe_0 pe_1 ...) @ x) (+ o_l o_r) x) Ø]
  ;; possibly valid linear combinations
  [(subst-oo i oo x) i]
  [(subst-oo (+ o_l o_r) oo x) (+: (subst-oo o_l oo x)
                                   (subst-oo o_r oo x))]
  [(subst-oo (* i o) oo x) (*: i
                               (subst-oo o oo x))])

(define-metafunction λDTR
  subst-ψ : ψ oo x -> ψ
  ;; TT/FF
  [(subst-ψ TT oo x) TT]
  [(subst-ψ FF oo x) FF]
  ;; fact
  [(subst-ψ (o ? τ) oo x) TT
   (where Ø (subst-oo o oo x))]
  [(subst-ψ (o_1 ? τ) oo x) (o_2 ? (subst-τ τ oo x))
   (where o_2 (subst-oo o_1 oo x))]
  ;; And/Or
  [(subst-ψ (ψ_1 ∧ ψ_2) oo x) (And: (subst-ψ ψ_1 oo x)
                                    (subst-ψ ψ_2 oo x))]
  [(subst-ψ (ψ_1 ∨ ψ_2) oo x) (Or: (subst-ψ ψ_1 oo x)
                                   (subst-ψ ψ_2 oo x))]
  
  ;; Φ
  [(subst-ψ Φ Ø x) (fme-elim Φ x)]
  [(subst-ψ Φ o x) (subst-Φ Φ o x)])


(define-metafunction λDTR 
  ≤: : oo oo -> Φ
  [(≤: Ø oo) []]
  [(≤: oo Ø) []]
  [(≤: o_1 o_2) [(≤ o_1 o_2)]])

(define-metafunction λDTR
  subst-Φ : Φ o x -> ψ
  [(subst-Φ [] o x) []]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) FF
   (where FF (subst-Φ [(≤ o_2l o_2r) ...] o x))]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) FF
    (where [] (≤: (subst-oo o_1l o x)
                  (subst-oo o_1r o x)))]
  [(subst-Φ [(≤ o_1l o_1r) (≤ o_2l o_2r) ...] o x) (app [(≤ o_l o_r)] Φ_rest)
   (where Φ_rest (subst-Φ [(≤ o_2l o_2r) ...] o x))
   (where [(≤ o_l o_r)] (≤: (subst-oo o_1l o x)
                            (subst-oo o_1r o x)))])

;; standard captura avoiding substitution
;; with smart constructors
(define-metafunction λDTR
  subst-τ : τ oo x -> τ
  [(subst-τ Top oo x) Top]
  [(subst-τ Int oo x) Int]
  [(subst-τ Str oo x) Str]
  [(subst-τ #t oo x) #t]
  [(subst-τ #f oo x) #f]
  [(subst-τ (U τ ...) oo x) (U: (subst-τ τ oo x) ...)]
  [(subst-τ (τ × σ) oo x)
   (Pair: (subst-τ τ oo x) (subst-τ σ oo x))]
  [(subst-τ (♯ τ) oo x)
   (Vec: (subst-τ τ oo x))]
  [(subst-τ (x : σ → τ (ψ_+ ψ_- oo_f)) oo x) 
   (x : (subst-τ σ oo x) → τ (ψ_+ ψ_- oo_f))]
  [(subst-τ (y : σ → τ (ψ_+ ψ_- oo_f)) oo x)
   (z : (subst-τ (subst-τ σ (id z) y) oo x)
      →
      (subst (subst-τ τ (id z) y) oo x)
      ((subst (subst-ψ ψ_+ (id z) y) oo x)
       (subst (subst-ψ ψ_- (id z) y) oo x)
       (subst-oo (subst-oo oo_f (id z) y) oo x)))
   (judgment-holds (<> x y))
   (where z (fresh-var (y : σ → τ (ψ_+ ψ_- oo_f)) oo x))]
  [(subst-τ (x : τ where Φ) oo x) (x : τ where Φ)]
  [(subst-τ (y : τ where Φ) oo x)
   (z : (subst-τ (subst-τ τ (id z) y) oo x) 
      where (subst (subst Φ (id z) y) oo x))
   (judgment-holds (<> x y))
   (where z (fresh-var (y : τ where Φ) oo x))])

(define-metafunction λDTR
  op-τ : op -> τ
  [(op-τ add1) (x : Int → (Int= (+ 1 (id x))) 
                  (TT FF (+ 1 (id x))))]
  [(op-τ +) (x : Int → 
               (y : Int → (Int= (+ (id x) (id y)))
                  (TT FF (+ (id x) (id y))))
               (TT FF Ø))]
  [(op-τ (* i)) (x : Int → (Int= (* i (id x)))
                   (TT FF (* i (id x))))]
  [(op-τ zero?) (x : Int → 
                   (U #t #f)
                   ((is x (Int= 0))
                    (Or: (is x (Int> 0))
                         (is x (Int< 0)))
                    Ø))]
  [(op-τ int?) (x : Top → 
                  (U #t #f)
                  ((is x Int) (! x Int) Ø))]
  [(op-τ str?) (x : Top → 
                  (U #t #f)
                  ((is x Str) (! x Str) Ø))]
  [(op-τ str-len) (x : Str → 
                     Int 
                     (TT FF Ø))]
  [(op-τ vec-len) (x : (♯ Top) → (Int= (o-len (id x)))
                     (TT FF ((LEN) @ x)))]
  [(op-τ error) (x : Str → (U) 
                  (FF FF Ø))]
  [(op-τ bool?) (x : Top → 
                   (U #t #f)
                   ((is x (U #t #f)) (! x (U #t #f)) Ø))]
  [(op-τ proc?) (x : Top → 
                   (U #t #f)
                   ((is x (y : (U) → Top (TT TT Ø)))
                    (! x (y : (U) → Top (TT TT Ø)))
                    Ø))]
  [(op-τ cons?) (x : Top → 
                   (U #t #f)
                   ((is x (Top × Top))
                    (! x (Top × Top))
                    Ø))]
  [(op-τ vec?) (x : Top → 
                   (U #t #f)
                   ((is x (♯ Top))
                    (! x (♯ Top))
                    Ø))])

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
  
  [(where/hidden #f ,(member (term e_1) '(car cdr vec-ref)))
   (typeof Γ e_1 σ_λ (ψ_1+ ψ_1- oo_1))
   (where (x : σ_f → τ_f (ψ_f+ ψ_f- oo_f)) (exists/fun-τ σ_λ))
   (typeof Γ e_2 σ_2 (ψ_2+ ψ_2- oo_2))
   (subtype/ctx Γ (id (fresh-var Γ (e_1 e_2))) σ_2 σ_f)
   -------------- "T-App"
   (typeof Γ
           (e_1 e_2)
           (subst τ_f oo_2 x)
           ((subst ψ_f+ oo_2 x)
            (subst ψ_f- oo_2 x)
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
           ((subst (And: (((CAR) @ x) -! #f)
                         (And: (((CAR) @ x) -: τ)
                               (true-ψ τ))) 
                   oo x)
            (subst (And: (((CAR) @ x) -: #f)
                         (And: (((CAR) @ x) -: τ)
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
           ((subst (And: (((CDR) @ x) -! #f)
                         (And: (((CDR) @ x) -: σ)
                               (true-ψ σ))) 
                   oo x)
            (subst (And: (((CDR) @ x) -: #f)
                         (And: (((CDR) @ x) -: σ)
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
   (subtype/ctx (env/sift+ψ* Γ (o_1 -: σ_v)) o_2 σ_i (IntRange 0 (+ -1 (o-len o_1))))
   ------------------------- "T-VecRef"
   (typeof Γ (vec-ref e_1 e_2) τ 
           ((true-ψ τ) (false-ψ τ) Ø))])

(define-metafunction λDTR
  exists/pair-τ : τ -> τ
  [(exists/pair-τ (τ × σ)) (τ × σ)]
  [(exists/pair-τ (x : τ where Φ)) (exists/pair-τ τ)]
  [(exists/pair-τ σ) (U)
   (where #f (is-Refine σ))
   (where #f (is-Pair σ))])

(define-metafunction λDTR
  exists/vec-τ : τ -> τ
  [(exists/vec-τ (♯ τ)) (♯ τ)]
  [(exists/vec-τ (x : τ where Φ)) (exists/vec-τ τ)]
  [(exists/vec-τ σ) (U)
   (where #f (is-Refine σ))
   (where #f (is-Vec σ))])

(define-metafunction λDTR
  exists/fun-τ : τ -> τ
  [(exists/fun-τ (x : σ → τ (ψ_+ ψ_- oo))) (x : σ → τ (ψ_+ ψ_- oo))]
  [(exists/fun-τ (x : τ where Φ)) (exists/fun-τ τ)]
  [(exists/fun-τ σ) (U)
   (where #f (is-Refine σ))
   (where #f (is-Abs σ))])

(define (fresh-if-needed oo . rest)
  (match oo
    ['Ø (term (id ,(gensym)))]
    [_ oo]))

(define-metafunction λDTR
  true-ψ : τ -> ψ
  [(true-ψ τ) TT
   (where #f (subtype #f τ))]
  [(true-ψ τ) FF
   (judgment-holds (subtype #f τ))])

(define-metafunction λDTR
  false-ψ : τ -> ψ
  [(false-ψ τ) FF
   (where #f (subtype #f τ))]
  [(false-ψ τ) TT
   (judgment-holds (subtype #f τ))])


(define-judgment-form λDTR
  #:mode (in I I)
  #:contract (in any any)
  [(side-condition ,(list? (member (term any_1) (term (any_2 ...)))))
   --------------------- "In"
   (in any_1 (any_2 ...))])

(define-judgment-form λDTR
  #:mode (not-in I I)
  #:contract (not-in any any) 
  [(side-condition ,(not (member (term any_1) (term (any_2 ...)))))
   ------------------------ "Not-In"
   (not-in any_1 (any_2 ...))])

(define-judgment-form λDTR
  #:mode (<> I I)
  #:contract (<> any any)
  [------------ "NotEqual"
   (<> any_!_1 any_!_1)])



(define-metafunction λDTR
  dnf : ψ -> ψ
  [(dnf ψ) ,(let* ([unfolded-ψ (term (dnf* (([] [])) (sift-ψ ψ) []))]
                   [disjuncts (map (λ (univ)
                                     (match univ
                                       [(list) (term TT)]
                                       [(list '() fs)
                                        (term ,(foldl (λ (cur acc)
                                                        (match cur
                                                          [(list o b t) 
                                                           (term (And: ,acc (Type: ,o ,b ,t)))]))
                                                      (term TT)
                                                      fs))]
                                       [(list sli fs) 
                                        (term (,sli ∧ ,(foldl (λ (cur acc) 
                                                                (term (And: ,acc ,cur)))
                                                              (term TT)
                                                              fs)))]))
                                   unfolded-ψ)])
              (foldl 
               (λ (disj dnf) (term (Or: ,disj ,dnf)))
               (term FF) 
               disjuncts))])

(define-metafunction λDTR
  ;; ((Φ (δ ...)) ...) disjuncts so far
  ;; ψ current prop
  ;; Γ prop stack (i.e. TO DO))
  dnf* : ((Φ (δ ...)) ...) ψ ψ* -> ((Φ (δ ...)) ...)
  ;; TT
  [(dnf* ((Φ (δ ...)) ...) TT ()) 
   ((Φ (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) TT (ψ ψ_1 ...)) 
   (dnf* ((Φ (δ ...)) ...) ψ (ψ_1 ...))]
  ;; FF
  [(dnf* ((Φ (δ ...)) ...) FF (ψ ...))
   ()]
  ;; And
  [(dnf* ((Φ (δ ...)) ...) (ψ_1 ∧ ψ_2) (ψ ...))
   (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ_2 ψ ...))]
  ;; Or
  [(dnf* ((Φ (δ ...)) ...) (ψ_1 ∨ ψ_2) (ψ ...))
   (app (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ ...))
        (dnf* ((Φ (δ ...)) ...) ψ_2 (ψ ...)))]
  ;; Φ
  [(dnf* ((Φ (δ ...)) ...) Φ_1 ())
   (((app Φ Φ_1) (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) Φ_1 (ψ ψ_1 ...))
   (dnf* (((app Φ Φ_1) (δ ...)) ...) ψ (ψ_1 ...))]
  
  ;; δ
  [(dnf* ((Φ (δ ...)) ...) (o ? τ) ())
   ((Φ (update* () (ext (δ ...) (o ? τ)) (o ? τ))) ...)]
  [(dnf* ((Φ (δ ...)) ...) (o ? τ) (ψ ψ_1 ...))
   (dnf* ((Φ (update* () (ext (δ ...) (o ? τ)) (o ? τ))) ...) 
         (ψ-update () ψ (o ? τ))
         (update* () (ψ_1 ...) (o ? τ)))])



(define-metafunction λDTR
  id : x -> o
  [(id x) (() @ x)])

(define-metafunction λDTR
  fresh-var : any ... -> x
  [(fresh-var any ...) ,(gensym 'fresh)])

(define-metafunction λDTR
  ext : any any ... -> any
  [(ext [any_1 ...] any_2 ...) [any_1 ... any_2 ...]])

(define-metafunction λDTR
  o-car : o -> o
  [(o-car i) i]
  [(o-car (* 1 o)) (o-car o)]
  [(o-car (+ o_1 o_2)) (+ o_1 o_2)]
  [(o-car ((pe ...) @ x)) ((CAR pe ...) @ x)])

(define-metafunction λDTR
  o-cdr : o -> o
  [(o-cdr i) i]
  [(o-cdr (* 1 o)) (o-cdr o)]
  [(o-cdr (+ o_1 o_2)) (+ o_1 o_2)]
  [(o-cdr ((pe ...) @ x)) ((CDR pe ...) @ x)])

(define-metafunction λDTR
  o-len : o -> o
  [(o-len i) i]
  [(o-len (* 1 o)) (o-len o)]
  [(o-len (+ o_1 o_2)) (+ o_1 o_2)]
  [(o-len ((pe ...) @ x)) ((LEN pe ...) @ x)])

(define-metafunction λDTR
  sift-δ : δ b -> ψ
  [(sift-δ (o -! τ) b) (o -! τ)]
  [(sift-δ (o -: Top) #t) (o -: Top)]
  [(sift-δ (o -: Top) #f) TT]
  [(sift-δ (o -: #t) #t) (o -: #t)]
  [(sift-δ (o -: #t) #f) TT]
  [(sift-δ (o -: #f) #t) (o -: #f)]
  [(sift-δ (o -: #f) #f) TT]
  [(sift-δ (o -: Int) #t) (o -: Int)]
  [(sift-δ (o -: Int) #f) TT]
  [(sift-δ (o -: Str) #t) (o -: Str)]
  [(sift-δ (o -: Str) #f) TT]
  [(sift-δ (o -: (U τ ...)) #t) (o -: (U τ ...))]
  [(sift-δ (o -: (U τ ...)) #f) TT]
  [(sift-δ (o -: (x : σ → τ (ψ_+ ψ_- oo))) #t) (o -: (x : σ → τ (ψ_+ ψ_- oo)))]
  [(sift-δ (o -: (x : σ → τ (ψ_+ ψ_- oo))) #f) TT]
  [(sift-δ (o -: (τ × σ)) #t) (And: (o -: (τ × σ))
                                    (And: (sift-δ ((o-car o) -: τ) #f)
                                          (sift-δ ((o-cdr o) -: σ) #f)))]
  [(sift-δ (o -: (τ × σ)) #f) (And: (sift-δ ((o-car o) -: τ) #f)
                                    (sift-δ ((o-cdr o) -: σ) #f))]
  [(sift-δ (o -: (♯ τ)) #t) (And: (o -: (♯ τ))
                                  (subst (sift-δ ((id x) -: τ) #f) Ø x))
                            (where x (fresh-var (o -: (♯ τ))))]
  [(sift-δ (o -: (♯ τ)) #f) (subst (sift-δ ((id x) -: τ) #f) Ø x)
                                  
                            (where x (fresh-var (o -: (♯ τ))))]
  [(sift-δ (o -: (x : τ where Φ)) b) (And: (subst Φ o x)
                                           (sift-δ (o -: (subst τ o x)) b))])

(define-metafunction λDTR
  sift-ψ : ψ -> ψ
  ;; TT/FF
  [(sift-ψ TT) TT]
  [(sift-ψ FF) FF]
  ;; fact
  [(sift-ψ δ) (sift-δ δ #t)]
  ;; And/Or
  [(sift-ψ (ψ_1 ∧ ψ_2)) (And: (sift-ψ ψ_1)
                              (sift-ψ ψ_2))]
  [(sift-ψ (ψ_1 ∨ ψ_2)) (Or: (sift-ψ ψ_1)
                             (sift-ψ ψ_2))]
  ;; Φ
  [(sift-ψ Φ) Φ])


(define-metafunction λDTR
  sift-ψ* : ψ* -> ψ*
  [(sift-ψ* (ψ ...)) ((sift-ψ ψ) ...)])

(define-metafunction λDTR
  Φ-update-δ* : δ* Φ -> δ*
  [(Φ-update-δ* ((o ? τ) ...) Φ) ((o ? (Φ-update-τ o ? τ Φ)) ...)]) ;; TODO

(define-metafunction λDTR
  Φ-update-τ : o ? τ Φ -> τ
  [(Φ-update-τ o -! τ Φ) τ]
  [(Φ-update-τ o -: Top Φ) Top]
  [(Φ-update-τ o -: #t Φ) #t]
  [(Φ-update-τ o -: #f Φ) #f]
  [(Φ-update-τ o -: Int Φ) Int]
  [(Φ-update-τ o -: Str Φ) Str]
  [(Φ-update-τ o -: (U τ ...) Φ) (U  (Φ-update-τ o -: τ Φ) ...)]
  [(Φ-update-τ o -: (x : σ → τ (ψ_+ ψ_- oo)) Φ) (x : σ → τ (ψ_+ ψ_- oo))]
  [(Φ-update-τ o -: (τ × σ) Φ) ((Φ-update-τ (o-car o) -: τ Φ) × (Φ-update-τ (o-cdr o) -: σ Φ))]
  [(Φ-update-τ o -: (♯ τ) Φ) (♯ (Φ-update-τ (id (fresh-var o τ Φ)) -: τ Φ))]
  [(Φ-update-τ o -: (x : τ where Φ_x) Φ) (z : (Φ-update-τ o -: (subst τ (id z) x) Φ) 
                                            where (subst Φ_x (id z) x))
   (judgment-holds (fme-sat (app Φ (subst Φ_x (id (fresh-var o x τ Φ_x Φ z)) x))))
   (where z (fresh-var o x τ Φ_x Φ))]
  [(Φ-update-τ o -: (x : τ where Φ_x) Φ) (U)
   (where #f (fme-sat (app Φ (subst Φ_x (id (fresh-var o x τ Φ_x Φ)) x))))])

(define-metafunction λDTR
  Pair: : τ τ -> τ
  [(Pair: τ σ) (U)
   (judgment-holds (subtype τ (U)))]
  [(Pair: τ σ) (U)
   (judgment-holds (subtype σ (U)))
   (where/hidden #f (subtype τ (U)))]
  [(Pair: τ σ) (τ × σ)
   (where #f (subtype τ (U)))
   (where #f (subtype σ (U)))])

(define-metafunction λDTR
  Vec: : τ -> τ
  [(Vec: τ) (U)
   (judgment-holds (subtype τ (U)))]
  [(Vec: τ) (♯ τ)
   (where #f (subtype τ (U)))])

(define-metafunction λDTR
  Int= : o -> τ
  [(Int= o) (x : Int where [(≤ (id x) o) (≤ o (id x))])
   (where x (fresh-var o))])

(define-metafunction λDTR
  Int< : o -> τ
  [(Int< o) (x : Int where [(≤ (+ 1 (id x)) o)])
   (where x (fresh-var o))])

(define-metafunction λDTR
  Int> : o -> τ
  [(Int> o) (x : Int where [(≤ (+ 1 o) (id x))])
   (where x (fresh-var o))])


(define-metafunction λDTR
  Int<= : o -> τ
  [(Int<= o) (x : Int where [(≤ (id x) o)])
   (where x (fresh-var o))])

(define-metafunction λDTR
  Int>= : o -> τ
  [(Int>= o) (x : Int where [(≤ o (id x))])
   (where x (fresh-var o))])

(define-metafunction λDTR
  IntRange : o o -> τ
  [(IntRange o_l o_h) (x : Int where (Φin-range (id x) o_l o_h))
   (where x (fresh-var o_l o_h))])

(define-metafunction λDTR
  Φ= : o o -> Φ
  [(Φ= o_1 o_2) [(≤ o_1 o_2) (≤ o_2 o_1)]])

(define-metafunction λDTR
  Φin-range : o o o -> Φ
  [(Φin-range o o_low o_high) [(≤ o o_high)
                             (≤ o_low o)]])

(define-judgment-form λDTR
  #:mode (flat-U I)
  #:contract (flat-U (U τ ...))
  [(not-U τ) ...
   --------------- "Flat-U"
   (flat-U (U τ ...))])

(define-metafunction λDTR
  flatten-U : (U τ ...) -> τ
  [(flatten-U (U τ ...)) (U τ ...)
                         (judgment-holds (flat-U (U τ ...)))]
  [(flatten-U (U τ_0 ... (U σ ...) τ_1 ...)) (flatten-U (U τ_0 ... σ ... τ_1 ...))
                                             (judgment-holds (flat-U (U τ_1 ...)))])

(define-metafunction λDTR
  flatten+dedupe-U : (U τ ...) -> τ
  [(flatten+dedupe-U (U τ ...)) 
   (U ,@(remove-duplicates (cdr (term (flatten-U (U τ ...))))))])


(define-metafunction λDTR
  U: : τ ... -> τ
  [(U: τ ...) σ
   (where (U σ) (flatten+dedupe-U (U τ ...)))]
  [(U: τ ...) (U)
   (where (U) (flatten+dedupe-U (U τ ...)))]
  [(U: τ ...) (U σ_0 σ_1 ...)
   (where (U σ_0 σ_1 ...) (flatten+dedupe-U (U τ ...)))])



(define-metafunction λDTR
  oo-join : oo oo -> oo
  [(oo-join oo Ø) Ø]
  [(oo-join Ø oo) Ø]
  [(oo-join o_1 o_2) Ø
   (where #f (lexp-equal o_1 o_2))]
  [(oo-join o_1 o_2) o_1
   (judgment-holds (lexp-equal o_1 o_2))])

(define-metafunction λDTR
  τ-join : τ σ ... -> τ
  [(τ-join τ) τ]
  [(τ-join τ σ) σ
   (judgment-holds (subtype τ σ))]
  [(τ-join τ σ) τ
   (judgment-holds (subtype σ τ))]
  [(τ-join τ σ) (U: τ σ)
   (where #f (subtype τ σ))
   (where #f (subtype σ τ))]
  [(τ-join τ σ_0 σ_1 σ_2)
   (τ-join (τ-join τ σ_0) σ_2)]
  [(τ-join τ σ_0 σ_1 σ_2 σ_3 ...)
   (τ-join (τ-join τ σ_0) σ_2 σ_3 ...)])

(define-metafunction λDTR
  is : x τ -> δ
  [(is x τ) ((id x) -: τ)])

(define-metafunction λDTR
  ! : x τ -> δ
  [(! x τ) ((id x) -! τ)])












