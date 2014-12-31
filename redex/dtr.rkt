#lang racket

(require redex "bridge.rkt")
(provide (all-defined-out))

(define-language λDTR
  [x y z  ::= variable-not-otherwise-mentioned]
  [b      ::= boolean]
  [i      ::= integer]
  [s      ::= string]
  [e      ::= x (ann e t) (e e) (λ (x : t) e) (if e e e) 
          op b i s (let (x e) e) (cons e e) (vec e ...)
          (car e) (cdr e) (vec-ref e e)]
  [op     ::= add1 zero? int? str? bool? proc? 
          str-len + * error cons? vec?]
  [pe     ::= CAR CDR LEN]
  [π      ::= (pe ...)]
  [o      ::= i (π @ x) (* i o) (+ o o)]
  [Φ      ::= ((o ≤ o) ...)] 
  [oo     ::= o Ø]
  [τ σ    ::= Top #t #f Int Str (U τ ...) (x : σ → τ (ψ ψ oo)) 
             (τ × σ) (♯ τ) (x : τ where Φ)]
  [?      ::= -: -!]
  [δ      ::= (o ? τ)]
  [ψ      ::= δ (ψ ∧ ψ) (ψ ∨ ψ) TT FF Φ]
  [Δ      ::= (δ ...)]
  [Γ      ::= (ψ ...)])

(define-judgment-form λDTR
  #:mode (fme-imp I I)
  #:contract (fme-imp Φ Φ)
  [(where #t ,(redex-fme-imp? (term Φ_1) (term Φ_2)))
   ----------- "FME-Imp"
   (fme-imp Φ_1 Φ_2)])

(define-judgment-form λDTR
  #:mode (fme-sat I)
  #:contract (fme-sat Φ)
  [(where #t ,(redex-fme-sat? (term Φ))) ;(where #t ,(redex-fme-sat? (term Φ)))
   ----------- "FME-Sat"
   (fme-sat Φ)])

(define-metafunction λDTR
  fme-elim : Φ x -> Φ
  [(fme-elim Φ x) ,(sli->redex (fme-elim-var (redex->fme (term Φ)) (term x)))])

(define-judgment-form λDTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo oo)]
  
  [(lexp-equal o_1 o_2)
   ------------------- "SO-LExp"
   (subobj o_1 o_2)]
  
  [------------------- "SO-Top"
   (subobj oo Ø)])


(define-judgment-form λDTR
  #:mode (subtype I I)
  #:contract (subtype τ σ)
  [(subtype/ctx () (fresh-o) τ σ)
   --------------------------- "S-EmptyCtx"
   (subtype τ σ)])

;; Φ : what linear inequalities currently hold
;; o : who are we talking about
;; τ : subtype
;; σ : supertype
(define-judgment-form λDTR
  #:mode (subtype/ctx I I I I)
  #:contract (subtype/ctx Φ o τ σ)
  [--------------- "S-Refl"
   (subtype/ctx Φ o τ τ)]
  
  [--------------- "S-Top"
   (subtype/ctx Φ o τ Top)]
  
  [(subtype/ctx Φ o σ τ)
   --------------- "S-UnionSuper"
   (subtype/ctx Φ o σ (U τ_1 ... τ τ_2 ...))]
  
  [(subtype/ctx Φ o τ σ) ...
   --------------- "S-UnionSub"
   (subtype/ctx Φ o (U τ ...) σ)]
  
  [(subtype/ctx Φ (o-car o) τ_1 τ_2)
   (subtype/ctx Φ (o-cdr o) σ_1 σ_2)
   ----------------- "S-Pair"
   (subtype/ctx Φ o (τ_1 × σ_1) (τ_2 × σ_2))]
  
  [(subtype/ctx Φ (fresh-o) τ σ)
   ----------------- "S-Vec"
   (subtype/ctx Φ o (♯ τ) (♯ σ))]
  
  [(subtype/ctx Φ (fresh-o) σ_2 σ_1) 
   (subtype/ctx Φ (fresh-o) (subst τ_1 (var y) x) τ_2) 
   (proves (Φ (subst ψ_1+ (var y) x)) ψ_2+)
   (proves (Φ (subst ψ_1- (var y) x)) ψ_2-)
   (subobj (subst oo_1 (var y) x) oo_2)
   ------------------------------------------ "S-Abs"
   (subtype/ctx Φ
                o
                (x : σ_1 → τ_1 (ψ_1+ ψ_1- oo_1))
                (y : σ_2 → τ_2 (ψ_2+ ψ_2- oo_2)))]
  
  [(where #f (fme-sat Φ))
   ------------------- "S-Unsat"
   (subtype/ctx Φ o τ σ)]
  
  [(subtype/ctx (app Φ (subst Φ_x o x))
                o
                (subst τ o x) 
                σ)
   ------------------- "S-Refine-Sub"
   (subtype/ctx Φ o (x : τ where Φ_x) σ)]
  
  [(subtype/ctx Φ o τ σ)
   (fme-imp Φ (subst Φ_y o y))
   (where/hidden #f (is-Refine τ))
   ------------------- "S-Refine-Super"
   (subtype/ctx Φ o τ (y : σ where Φ_y))])

(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  [(proves-alg () () Γ ψ)
   ------------------- "Proves"
   (proves Γ ψ)])

(define-judgment-form λDTR
  #:mode (proves-alg I I I I)
  #:contract (proves-alg Φ Δ Γ ψ)
  
  [(subtype/ctx Φ o τ σ)
   ---------------- "L-Sub"
   (proves-alg Φ (δ_1 ... (o -: τ) δ_2 ...) () (o -: σ))]
  
  [(subtype/ctx Φ o σ τ)
   ---------------- "L-SubNot"
   (proves-alg Φ (δ_1 ... (o -! τ) δ_2 ...) () (o -! σ))]
  
  [(type-conflict Φ τ σ)
   ---------------- "L-Conflict"
   (proves-alg Φ (δ_1 ... (o -: τ) δ_2 ...) () (o -! σ))]
  
  [---------------------- "L-Bot"
   (proves-alg Φ (δ_1 ... (o -: (U)) δ_2 ...) () ψ)]
  
  [---------------------- "L-True"
   (proves-alg Φ Δ Γ TT)]
  
  [(proves-alg Φ Δ (ψ_1 ...) ψ)
   ---------------------- "L-Weaken"
   (proves-alg Φ Δ (TT ψ_1 ...) ψ)]
  
  [---------------------- "L-ExFalso"
   (proves-alg Φ Δ (FF ψ_1 ...) ψ)]
  
  [(proves-alg Φ Δ [ψ_1 ψ_2 ψ_3 ...] ψ)
   ---------------------- "L-AndE"
   (proves-alg Φ Δ ((ψ_1 ∧ ψ_2) ψ_3 ...) ψ)]
  
  [(proves-alg Φ Δ () ψ_1)
   (proves-alg Φ Δ () ψ_2)
   ---------------------- "L-AndI"
   (proves-alg Φ Δ () (ψ_1 ∧ ψ_2))]
  
  [(proves-alg Φ Δ (ψ_1 ψ_3 ...) ψ)
   (proves-alg Φ Δ (ψ_2 ψ_3 ...) ψ)
   ---------------------- "L-OrE"
   (proves-alg Φ Δ ((ψ_1 ∨ ψ_2) ψ_3 ...) ψ)]
  
  [(proves-alg Φ Δ () ψ_1)
   ---------------------- "L-OrI-L"
   (proves-alg Φ Δ () (ψ_1 ∨ ψ_2))]
  
  [(proves-alg Φ Δ () ψ_2)
   ---------------------- "L-OrI-R"
   (proves-alg Φ Δ () (ψ_1 ∨ ψ_2))]
  
  [(proves-alg (app Φ Φ_1) Δ (ψ_2 ...) ψ)
   ---------------------- "L-Linear"
   (proves-alg Φ Δ (Φ_1 ψ_2 ...) ψ)]
  
  [(proves-alg (app Φ (implied-Φ o ? τ))
               (update* (ext Δ (o ? τ)) (o ? τ)) 
               (update* (ψ_1 ...) (o ? τ)) 
               ψ)
   ---------------------- "L-Update*"
   (proves-alg Φ Δ ((o ? τ) ψ_1 ...) ψ)])


(define-metafunction λDTR
  π-update : ? τ ? σ π -> τ
  ;; updates CAR/CDR
  [(π-update ?_τ τ ?_σ σ [pe ... CAR])
   (π-update ?_τ τ ?_σ (σ × Top) [pe ... ])]
  
  [(π-update ?_τ τ ?_σ σ [pe ... CDR])
   (π-update ?_τ τ ?_σ (Top × σ) [pe ... ])]
  
  ;; updates LEN
  [(π-update ?_τ τ ?_σ σ [pe ... LEN])
   (π-update ?_τ τ ?_σ (♯ Top) [pe ... ])]
  
  ;; restrict
  [(π-update -: τ -: σ ()) (restrict τ σ)]
  
  ;; remove
  [(π-update -: τ -! σ ()) (remove τ σ)]
  [(π-update -! τ -: σ ()) τ] ; can't flip them and remove, since τ's 
                              ; boolean is fixed by caller already
  ; union negations
  [(π-update -! τ -! σ ()) σ
   (judgment-holds (subtype τ σ))]
  [(π-update -! τ -! σ ()) τ
   (where #f (subtype τ σ))
   (judgment-holds (subtype σ τ))]
  [(π-update -! τ -! σ ()) (U τ σ)
   (where #f (subtype σ τ))
   (where #f (subtype τ σ))])

;; restrict
(define-metafunction λDTR
  restrict : τ σ -> τ
  ;; No common value
  [(restrict τ σ) (U)
   (judgment-holds (type-conflict () τ σ))]
  
  ;; Refinements
  [(restrict (x : τ where Φ_x) (y : σ where Φ_y))
   (x : (restrict τ σ) where (app Φ_x (subst Φ_y (var x) y)))]
  [(restrict (x : τ where Φ_x) σ)
   (x : (restrict τ σ) where Φ_x)
   (where/hidden #f (is-Refine σ))]
  [(restrict τ (y : σ where Φ_y))
   (y : (restrict τ σ) where Φ_y)
   (where/hidden #f (is-Refine τ))]
  
  ;; Unions
  [(restrict (U τ ...) σ) (U^ ,@(map (λ (t) (term (restrict ,t σ))) (term (τ ...))))
   (where/hidden #t (common-val () (U τ ...) σ))]
  
  [(restrict τ (U σ ...)) (U^ ,@(map (λ (t) (term (restrict τ ,t))) (term (σ ...))))
   (where/hidden #f (is-U τ))
   (where/hidden #t (common-val () τ (U σ ...)))]
  
  ;; Pairs
  [(restrict (τ_0 × σ_0) (τ_1 × σ_1)) (Pair^ (restrict τ_0 τ_1) (restrict σ_0 σ_1))
   (where/hidden #f (subtype (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(restrict (♯ τ) (♯ σ)) (♯ (restrict τ σ))
   (where/hidden #f (subtype (♯ τ) (♯ σ)))]
  
  ;; else if τ <: σ
  [(restrict τ σ) τ
   (judgment-holds (subtype τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))]
  
  ;; else
  [(restrict τ σ) σ
   (where #f (subtype τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))])

;; remove
(define-metafunction λDTR
  remove : τ σ -> τ
  ;; τ_1 <: τ_2
  [(remove τ σ) (U)
   (judgment-holds (subtype τ σ))]
  
  ;; Union
  [(remove (U τ ...) σ) (U^ ,@(map (λ (t) (term (remove ,t σ))) (term (τ ...))))
   (where/hidden #f (subtype (U τ ...) σ))]
  
  ;; Refinement
  [(remove (x : τ where Φ_x) σ) (x : (remove τ σ) where Φ_x)
   (where/hidden #f (subtype (x : τ where Φ_x) σ))
   (where/hidden #f (is-Refine σ))]
  
  ;; Pairs
  [(remove (τ_0 × σ_0) (τ_1 × σ_1)) (Pair^ (remove τ_0 τ_1) 
                                           (remove σ_0 σ_1))
   (where/hidden #f (subtype (τ_0 × σ_0) (τ_1 × σ_1)))]
  
  ;; Vecs
  [(remove (♯ τ) (♯ σ)) (♯ (remove τ σ))
   (where/hidden #f (subtype (♯ τ) (♯ σ)))]
  
  ;; non-special-case
  [(remove τ σ) τ
   (where/hidden #f (subtype τ σ))
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
  [(side-condition (redex-sli-equal? o_1 o_2))
   ----------- "LExp-Equal"
   (lexp-equal o_1 o_2)])

;; update type info in lhs w/ rhs if applicable
(define-metafunction λDTR
  τ-update : δ δ -> δ
  ;; overlapping paths, update w/ path
  [(τ-update (((pe_τ ...) @ x) ?_τ τ) 
             (((pe_σ ... pe_τ ...) @ x) ?_σ σ))
   (((pe_τ ...) @ x) ?_τ (π-update ?_τ τ ?_σ σ (pe_σ ...)))]
  
  ;; equal linear expressions, update types w/ empty path
  [(τ-update (o_τ ?_τ τ) (o_σ ?_σ σ))
   (o_τ ?_τ (π-update ?_τ τ ?_σ σ ()))
   (judgment-holds (lexp-equal o_τ o_σ))]
  
  ;; incompatible objects, no-op
  [(τ-update (o_τ ?_τ τ) (o_σ ?_σ σ)) (o_τ ?_τ τ)
   (where #f (path-postfix o_τ o_σ))
   (where #f (lexp-equal o_τ o_σ))])

(define-metafunction λDTR
  ψ-update : ψ δ -> ψ
  [(ψ-update TT δ) TT]
  [(ψ-update FF δ) FF]
  [(ψ-update δ δ_new) (τ-update δ δ_new)]
  [(ψ-update (ψ_1 ∧ ψ_2) δ_new) (And^ (ψ-update ψ_1 δ_new) 
                                      (ψ-update ψ_2 δ_new))]
  [(ψ-update (ψ_1 ∨ ψ_2) δ_new) (Or^  (ψ-update ψ_1 δ_new) 
                                      (ψ-update ψ_2 δ_new))])

(define-metafunction λDTR
  update* : Γ δ -> Γ
  [(update* Γ δ)
   ,(map (λ (ψ) (term (ψ-update ,ψ δ))) (term Γ))])


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
  
  [(where o_f (fresh-o))
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
(define-metafunction λDTR
  subst : any oo x -> any
  [(subst oo oo_new x) (subst-oo oo oo_new x)]
  [(subst ψ  oo_new x) (subst-ψ  ψ   oo_new x)]
  [(subst τ  oo_new x) (subst-τ  τ   oo_new x)])

(define-metafunction λDTR
  And^ : ψ ψ -> ψ
  [(And^ TT ψ) ψ]
  [(And^ ψ TT) ψ]
  [(And^ FF ψ) FF]
  [(And^ ψ FF) FF]
  [(And^ ψ_l ψ_r) (ψ_l ∧ ψ_r)
   (judgment-holds (<> TT ψ_l))
   (judgment-holds (<> TT ψ_r))
   (judgment-holds (<> FF ψ_l))
   (judgment-holds (<> FF ψ_r))])

(define-metafunction λDTR
  Or^ : ψ ψ -> ψ
  [(Or^ TT ψ) TT]
  [(Or^ ψ TT) TT]
  [(Or^ FF ψ) ψ]
  [(Or^ ψ FF) ψ]
  [(Or^ ψ_l ψ_r) (ψ_l ∨ ψ_r)
   (judgment-holds (<> TT ψ_l))
   (judgment-holds (<> TT ψ_r))
   (judgment-holds (<> FF ψ_l))
   (judgment-holds (<> FF ψ_r))])

(define-metafunction λDTR
  +^ : oo oo -> oo
  [(+^ Ø oo) Ø]
  [(+^ oo Ø) Ø]
  [(+^ 0 o) o]
  [(+^ o 0) o]
  [(+^ i_l i_r) ,(+ (term i_l) (term i_r))]
  [(+^ o_l o_r) (+ o_l o_r)
   (side-condition (nand (exact-integer? (term o_l))
                         (exact-integer? (term o_r))))])

(define-metafunction λDTR
  *^ : oo oo -> oo
  [(*^ Ø oo) Ø]
  [(*^ oo Ø) Ø]
  [(*^ i_l i_r) ,(* (term i_l) (term i_r))]
  [(*^ 0 o) 0]
  [(*^ 1 o) o]
  [(*^ i o) (* i o)
   (side-condition (nor (exact-integer? (term o))
                        (= 0 (term i))
                        (= 1 (term i))))]
  [(*^ o i) (*^ i o)
   (side-condition (not (exact-integer? (term o))))]
  [(*^ oo_l oo_r) Ø
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
  [(subst-oo (+ o_l o_r) oo x) (+^ (subst o_l oo x)
                                   (subst o_r oo x))]
  [(subst-oo (* i o) oo x) (*^ i
                               (subst o oo x))])

(define-metafunction λDTR
  subst-ψ : ψ oo x -> ψ
  ;; TT/FF
  [(subst-ψ TT oo x) TT]
  [(subst-ψ FF oo x) FF]
  ;; fact
  [(subst-ψ (o ? τ) oo x) TT
   (where Ø (subst o oo x))]
  [(subst-ψ (o_1 ? τ) oo x)
   (o_2 ? (subst τ oo x))
   (where o_2 (subst o_1 oo x))]
  ;; And/Or
  [(subst-ψ (And ψ_1 ψ_2) οο x) (And^ (subst ψ_1 oo x)
                                      (subst ψ_2 oo x))]
  [(subst-ψ (Or ψ_1 ψ_2) οο x) (Or^ (subst ψ_1 oo x)
                                    (subst ψ_2 oo x))]
  
  ;; Φ
  [(subst-ψ Φ Ø x) (fme-elim Φ x)]
  [(subst-ψ Φ o x) (subst-Φ Φ o x)])


(define-metafunction λDTR 
  ≤^ : oo oo -> Φ
  [(≤^ Ø oo) []]
  [(≤^ oo Ø) []]
  [(≤^ o_1 o_2) [(o_1 ≤ o_2)]])

(define-metafunction λDTR
  subst-Φ : Φ o x -> ψ
  [(subst-Φ [] o x) []]
  [(subst-Φ [(o_1l ≤ o_1r) (o_2l ≤ o_2r) ...] o x) FF
   (where FF (subst-Φ [(o_2l ≤ o_2r) ...] o x))]
  [(subst-Φ [(o_1l ≤ o_1r) (o_2l ≤ o_2r) ...] o x) FF
    (where [] (≤^ (subst o_1l o x)
                  (subst o_1r o x)))]
  [(subst-Φ [(o_1l ≤ o_1r) (o_2l ≤ o_2r) ...] o x) (app [(o_l ≤ o_r)] Φ_rest)
   (where Φ_rest (subst-Φ [(o_2l ≤ o_2r) ...] o x))
   (where [(o_l ≤ o_r)] (≤^ (subst o_1l o x)
                  (subst o_1r o x)))])

;; standard captura avoiding substitution
;; with smart constructors
(define-metafunction λDTR
  subst-τ : τ oo x -> τ
  [(subst-τ Top oo x) Top]
  [(subst-τ Int oo x) Int]
  [(subst-τ Str oo x) Str]
  [(subst-τ #t oo x) #t]
  [(subst-τ #f oo x) #f]
  [(subst-τ (U τ ...) oo x) (U^ (subst τ oo x) ...)]
  [(subst-τ (τ × σ) oo x)
   (Pair^ (subst τ oo x) (subst σ oo x))]
  [(subst-τ (x : σ → τ (ψ_+ ψ_- oo_f)) oo x) 
   (x : (subst σ oo x) → τ (ψ_+ ψ_- oo_f))]
  [(subst-τ (y : σ → τ (ψ_+ ψ_- oo_f)) oo x)
   (z : (subst (subst σ (var z) y) oo x)
      ->
      (subst (subst τ (var z) y) oo x)
      ((subst (subst ψ_+ (var z) y) oo x)
       (subst (subst ψ_- (var z) y) oo x)
       (subst (subst oo_f (var z) y) oo x)))
   (judgment-holds (<> x y))
   (where z (fresh-o))]
  [(subst-τ (x : τ where Φ) oo x) (x : τ where Φ)]
  [(subst-τ (y : τ where Φ) oo x) 
   (z : (subst (subst τ (var z) y) oo x) 
      where (subst (subst Φ (var z) y) oo x))
   (judgment-holds (<> x y))
   (where z (fresh-o))])

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
  [(dnf ψ) ,(foldl (λ (cur acc) (term (Or^ ,cur ,acc)))
                   (term FF)
                   (map (λ (e)
                          (match e
                            [(list) (term TT)]
                            [(list sli fs) 
                             (term (,sli ∧ ,(foldl (λ (cur acc) 
                                                     (term (And^ ,acc ,cur)))
                                                   (term TT)
                                                   fs)))]))
                        (term (dnf* (([] [])) ψ []))))])

(define-metafunction λDTR
  ;; ((Φ (δ ...)) ...) disjuncts so far
  ;; ψ current prop
  ;; Γ prop stack (i.e. TO DO))
  dnf* : ((Φ (δ ...)) ...) ψ Γ -> ((Φ (δ ...)) ...)
  ;; TT
  [(dnf* ((Φ (δ ...)) ...) TT ()) 
   ((Φ (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) TT (ψ ψ_1 ...)) 
   (dnf* ((Φ (δ ...)) ...) ψ (ψ_1 ...))]
  ;; FF
  [(dnf* ((Φ (δ ...)) ...) FF (ψ ...))
   ()]
  ;; And
  [(dnf* ((Φ (δ ...)) ...) (And ψ_1 ψ_2) (ψ ...))
   (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ_2 ψ ...))]
  ;; Or
  [(dnf* ((Φ (δ ...)) ...) (Or ψ_1 ψ_2) (ψ ...))
   (app (dnf* ((Φ (δ ...)) ...) ψ_1 (ψ ...))
        (dnf* ((Φ (δ ...)) ...) ψ_2 (ψ ...)))]
  ;; Φ
  [(dnf* ((Φ (δ ...)) ...) Φ_1 ())
   (((app Φ Φ_1) (δ ...)) ...)]
  [(dnf* ((Φ (δ ...)) ...) Φ_1 (ψ ψ_1 ...))
   (dnf* (((app Φ Φ_1) (δ ...)) ...) ψ (ψ_1 ...))]
  
  ;; fact
  [(dnf* ((Φ (δ ...)) ...) (o ? τ) ())
   (((app Φ (implied-Φ o ? τ)) (update* (ext (δ ...) (o ? τ)) (o ? τ))) ...)]
  [(dnf* ((Φ (δ ...)) ...) (o ? τ) (ψ ψ_1 ...))
   (dnf* (((app Φ (implied-Φ o ? τ)) (update* (ext (δ ...) (o ? τ)) (o ? τ))) ...) 
         ψ 
         (update* (ψ_1 ...) (o ? τ)))])



(define-metafunction λDTR
  var : x -> o
  [(var x) (() @ x)])

(define-metafunction λDTR
  fresh-o : any ... -> o
  [(fresh-o any ...) (var ,(gensym 'fresh))])

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
  implied-Φ : o ? τ -> Φ
  [(implied-Φ o -! τ) ()]
  [(implied-Φ o -: Top) ()]
  [(implied-Φ o -: #t) ()]
  [(implied-Φ o -: #f) ()]
  [(implied-Φ o -: Int) ()]
  [(implied-Φ o -: Str) ()]
  [(implied-Φ o -: (U τ ...)) ()]
  [(implied-Φ o -: (x : σ → τ (ψ_+ ψ_- oo))) ()]
  [(implied-Φ o -: (τ × σ)) (app (implied-Φ (o-car o) -: τ)
                                 (implied-Φ (o-cdr o) -: σ))]
  [(implied-Φ o -: (♯ τ)) ()]
  [(implied-Φ o -: (x : τ where Φ)) (app (subst Φ o x)
                                         (implied-Φ o -: τ))])

(define-metafunction λDTR
  Pair^ : τ τ -> τ
  [(Pair^ τ σ) (U)
   (judgment-holds (subtype τ (U)))]
  [(Pair^ τ σ) (U)
   (judgment-holds (subtype σ (U)))
   (where/hidden #f (subtype τ (U)))]
  [(Pair^ τ σ) (τ × σ)
   (where #f (subtype τ (U)))
   (where #f (subtype σ (U)))])


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
  [(flatten+dedupe-U (U τ ...)) (U ,@(remove-duplicates (cdr (term (flatten-U (U τ ...))))))])


(define-metafunction λDTR
  U^ : τ ... -> τ
  [(U^ τ ...) σ
   (where (U σ) (flatten+dedupe-U (U τ ...)))]
  [(U^ τ ...) (U)
   (where (U) (flatten+dedupe-U (U τ ...)))]
  [(U^ τ ...) (U σ_0 σ_1 ...)
   (where (U σ_0 σ_1 ...) (flatten+dedupe-U (U τ ...)))])
