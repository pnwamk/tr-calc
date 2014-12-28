#lang racket

(require redex)
(provide (all-defined-out))

(module+ test
  (require redex rackunit))

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
  [o      ::= i (obj π x) (* i o) (+ o o)]
  [φ      ::=  (o ≤ o)]
  [Φ      ::= (φ ...)] 
  [oo     ::= o Ø]
  [τ σ    ::= Top T F Int Str (U τ ...) (Abs x σ τ ψ ψ oo) 
           (Pair τ τ) (Vec τ) (Refine x : τ Φ)]
  [f      ::= (fact o bool τ)]
  [ψ      ::= f (Or ψ ψ) (And ψ ψ) TT FF Φ]
  [Γf     ::= [f ...]]
  [Γ      ::= (ψ ...)])

(define ε '())
(define Bot '(U))

(define-metafunction λDTR
  var : x -> o
  [(var x) (obj ε x)])

(define-metafunction λDTR
  fresh-o : any ... -> o
  [(fresh-o any ...) (var ,(gensym 'fresh))])

;; TODO
(define-judgment-form λDTR
  #:mode (fme-imp I I)
  #:contract (fme-imp Φ Φ)
  [----------- "FME-Imp"
   (fme-imp Φ Φ)])

;; TODO
(define-judgment-form λDTR
  #:mode (fme-sat I)
  #:contract (fme-sat Φ)
  [----------- "F-Sat"
   (fme-sat Φ)])

;; TODO
(define-metafunction λDTR
  fme-elim : Φ x -> Φ
  [(fme-elim Φ x) Φ])

(define-metafunction λDTR
  negb : b -> b
  [(negb b) ,(not (term b))])

(define-metafunction λDTR
  ¬ : ψ -> ψ
  [(¬ TT) FF]
  [(¬ FF) TT]
  [(¬ (fact o b τ))  (fact o (negb b) τ)]
  [(¬ (And ψ_1 ψ_2)) (Or (¬ ψ_1) (¬ ψ_2))]
  [(¬ (Or ψ_1 ψ_2))  (And (¬ ψ_1) (¬ ψ_2))]
  [(¬ ε) FF]
  [(¬ [(o_l ≤ o_r) φ_2 ...]) (Or [((+ 1 o_r) ≤ o_l)]
                                 (¬ [φ_2 ...]))])

(define-judgment-form λDTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo oo)]
  
  [(lexp-equal oo_1 oo_2)
   ------------------- "SO-LExp"
   (subobj oo_1 oo_2)]
  
  [------------------- "SO-Top"
   (subobj oo Ø)])

(define-metafunction λDTR
  ext : any any ... -> any
  [(ext [any_1 ...] any_2 ...) [any_1 ... any_2 ...]])

(define-judgment-form λDTR
  #:mode (subtype I I I)
  #:contract (subtype Φ τ τ)
  [--------------- "S-Refl"
   (subtype Φ τ τ)]
  
  [--------------- "S-Top"
   (subtype Φ τ Top)]
  
  [(subtype Φ σ τ)
   --------------- "S-UnionSuper"
   (subtype Φ σ (U τ_1 ... τ τ_2 ...))]
  
  [(subtype Φ τ_1 τ_2) ...
   --------------- "S-UnionSub"
   (subtype Φ (U τ_1 ...) τ_2)]
  
  [(subtype Φ τ_1 τ_2)
   (subtype Φ σ_1 σ_2)
   ----------------- "S-Pair"
   (subtype Φ (Pair τ_1 σ_1) (Pair τ_2 σ_2))]
  
  [(subtype Φ τ σ)
   ----------------- "S-Vec"
   (subtype Φ (Vec τ) (Vec σ))]
  
  [(subtype Φ σ_2 (subst σ_1 (var x_2) x_1)) 
   (subtype Φ (subst τ_1 (var x_2) x_1) τ_2) 
   (proves [Φ (subst ψ_1+ (var x_2) x_1)] ψ_2+)
   (proves [Φ (subst ψ_1- (var x_2) x_1)] ψ_2-)
   (subobj (subst oo_1 (var x_2) x_1) oo_2)
   ------------------------------------------ "S-Abs"
   (subtype Φ
            (Abs x_1 σ_1 τ_1 ψ_1+ ψ_1- oo_1)
            (Abs x_2 σ_2 τ_2 ψ_2+ ψ_2- oo_2))]
  
  [(where #f (fme-sat Φ))
   ------------------- "S-Unsat"
   (subtype Φ τ σ)]
  
  [(subtype (app Φ Φ_x) τ σ)
   ------------------- "S-Refine-Sub"
   (subtype Φ (Refine x : τ Φ_x) σ)]
  
  [(subtype Φ τ σ)
   (fme-imp Φ Φ_y)
   ------------------- "S-Refine-Super"
   (subtype Φ τ (Refine y : σ Φ_y))]
  
  [(subtype (app Φ Φ_x) τ σ)
   (fme-imp (app Φ Φ_x) Φ_y)
   ------------------- "S-Refine"
   (subtype Φ (Refine x : τ Φ_x) (Refine y : σ Φ_y))])


(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  [(proves-alg ε ε Γ ψ)
   ------------------- "Proves"
   (proves Γ ψ)])

(define-judgment-form λDTR
  #:mode (proves-alg I I I I)
  #:contract (proves-alg Φ Γf Γ ψ)
  
  [(subtype Φ τ σ)
   ---------------- "L-Sub"
   (proves-alg Φ [f_0 ... (fact o #t τ) f_1 ...] ε (fact o #t σ))]
  
  [(subtype Φ σ τ)
   ---------------- "L-SubNot"
   (proves-alg Φ [f_0 ... (fact o #f τ) f_1 ...] ε (fact o #f σ))]
  
  [(type-conflict Φ τ σ)
   ---------------- "L-Conflict"
   (proves-alg Φ [f_0 ... (fact o #t τ) f_1 ...] ε (fact o #f σ))]
  
  [---------------------- "L-Bot"
   (proves-alg Φ [f_0 ... (fact o #t Bot) f_1 ...] ε ψ)]
    
  [---------------------- "L-True"
   (proves-alg Φ Γf Γ TT)]
  
  [(proves-alg Φ Γf [ψ_0 ...] ψ)
   ---------------------- "L-WeakenTrue"
   (proves-alg Φ Γf [TT ψ_0 ...] ψ)]
  
  [---------------------- "L-ExFalso"
   (proves-alg Φ Γf [FF ψ_0 ...] ψ)]
  
  [(proves-alg Φ Γf [ψ_0 ψ_1 ψ_2 ...] ψ)
   ---------------------- "L-AndE"
   (proves-alg Φ Γf [(And ψ_0 ψ_1) ψ_2 ...] ψ)]
  
  [(proves-alg Φ Γf ε ψ_l)
   (proves-alg Φ Γf ε ψ_r)
   ---------------------- "L-AndI"
   (proves-alg Φ Γf ε (And ψ_l ψ_r))]
  
  [(proves-alg Φ Γf (ψ_0 ψ_2 ...) ψ)
   (proves-alg Φ Γf (ψ_1 ψ_2 ...) ψ)
   ---------------------- "L-OrE"
   (proves-alg Φ Γf [(Or ψ_0 ψ_1) ψ_2 ...] ψ)]
  
  [(proves-alg Φ Γf ε ψ_l)
   ---------------------- "L-OrI-L"
   (proves-alg Φ Γf ε (Or ψ_l ψ_r))]
  
  [(proves-alg Φ Γf ε ψ_r)
   ---------------------- "L-OrI-R"
   (proves-alg Φ Γf ε (Or ψ_l ψ_r))]
  
  [(proves-alg (app Φ Φ_0) Γf [ψ_1 ...] ψ)
   ---------------------- "L-Linear"
   (proves-alg Φ Γf [Φ_0 ψ_1 ...] ψ)]
  
  [(where f (fact o b τ))
   (proves-alg (app Φ (implied-Φ o b τ))
               (update* (ext Γf f) f) 
               (update* [ψ_0 ...]  f) 
               ψ)
   ---------------------- "L-Update*"
   (proves-alg Φ Γf [(fact o b τ) ψ_0 ...] ψ)])


(define-metafunction λDTR
  o-car : o -> o
  [(o-car i) i]
  [(o-car (* 1 o)) (o-car o)]
  [(o-car (+ o)) (o-car o)]
  [(o-car (+ o_0 o_1 ...)) (+ o_0 o_1 ...)]
  [(o-car (obj (pe ...) x)) (obj (CAR pe ...) x)])

(define-metafunction λDTR
  o-cdr : o -> o
  [(o-cdr i) i]
  [(o-cdr (* 1 o)) (o-cdr o)]
  [(o-cdr (+ o)) (o-cdr o)]
  [(o-cdr (+ o_0 o_1 ...)) (+ o_0 o_1 ...)]
  [(o-cdr (obj (pe ...) x)) (obj (CDR pe ...) x)])

(define-metafunction λDTR
  o-len : o -> o
  [(o-len i) i]
  [(o-len (* 1 o)) (o-len o)]
  [(o-len (+ o)) (o-len o)]
  [(o-len (+ o_0 o_1 ...)) (+ o_0 o_1 ...)]
  [(o-len (obj (pe ...) x)) (obj (LEN pe ...) x)])

(define-metafunction λDTR
  implied-Φ : o b τ -> Φ
  [(implied-Φ o #f τ) ε]
  [(implied-Φ o #t Top) ε]
  [(implied-Φ o #t T) ε]
  [(implied-Φ o #t F) ε]
  [(implied-Φ o #t Int) ε]
  [(implied-Φ o #t Str) ε]
  [(implied-Φ o #t (U τ ...)) ε]
  [(implied-Φ o #t (Abs x σ τ ψ_+ ψ_- oo)) ε]
  [(implied-Φ o #t (Pair τ σ)) (app (implied-Φ (o-car o) #t τ)
                                    (implied-Φ (o-cdr o) #t σ))]
  [(implied-Φ o #t (Vec τ)) ε]
  [(implied-Φ o #t (Refine x : τ Φ)) (app (subst Φ o x)
                                          (implied-Φ o #t τ))])

(define-metafunction λDTR
  Pair^ : τ τ -> τ
  [(Pair^ τ σ) Bot
   (judgment-holds (subtype ε τ Bot))]
  [(Pair^ τ σ) Bot
   (judgment-holds (subtype ε σ Bot))
   (where/hidden #f (subtype ε τ Bot))]
  [(Pair^ τ σ) (Pair τ σ)
   (where #f (subtype ε τ Bot))
   (where #f (subtype ε σ Bot))])

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
  [(flatten+dedupe-U (U τ ...)) (U ,@(remove-duplicates (term (σ ...))))
   (where (U σ ...) (flatten-U (U τ ...)))])


(define-metafunction λDTR
  U^ : τ ... -> τ
  [(U^ τ ...) σ
   (where (U σ) (flatten+dedupe-U (U τ ...)))]
  [(U^ τ ...) (U)
   (where (U) (flatten+dedupe-U (U τ ...)))]
  [(U^ τ ...) (U σ_0 σ_1 ...)
   (where (U σ_0 σ_1 ...) (flatten+dedupe-U (U τ ...)))])

(define-metafunction λDTR
  π-update : b τ b σ π -> τ
  ;; updates CAR/CDR
  [(π-update b_τ τ b_σ σ [pe ... CAR])
   (π-update b_τ τ b_σ (Pair^ σ Top) [pe ... ])]
  
  [(π-update b_τ τ b_σ σ [pe ... CDR])
   (π-update b_τ τ b_σ (Pair^ Top σ) [pe ... ])]
  
  ;; updates LEN
  [(π-update b_τ τ b_σ σ [pe ... LEN])
   (π-update b_τ τ b_σ (Vec Top) [pe ... ])]
  
  ;; restrict
  [(π-update #t τ #t σ ε) (restrict τ σ)]
  
  ;; remove
  [(π-update #t τ #t σ ε) (remove τ σ)]
  [(π-update #f τ #t σ ε) (remove σ τ)]
  
  ;; union negations
  [(π-update #f τ #f σ ε) σ
   (judgment-holds (subtype ε τ σ))]
  [(π-update #f τ #f σ ε) τ
   (where #f (subtype ε τ σ))
   (judgment-holds (subtype ε σ τ))]
  [(π-update #f τ #f σ ε) τ
   (where #f (subtype ε σ τ))
   (where #f (subtype ε τ σ))])

;; restrict
(define-metafunction λDTR
  restrict : τ σ -> τ
  ;; No common value
  [(restrict τ σ) Bot
   (judgment-holds (type-conflict ε τ σ))]
  
  ;; Refinements
  [(restrict (Refine x : τ Φ_x) (Refine y : σ Φ_y))
   (Refine x : (restrict τ σ) (app Φ_x (subst Φ_y (var x) y)))]
  [(restrict (Refine x : τ Φ_x) σ)
   (Refine x : (restrict τ σ) Φ_x)
   (where/hidden #f (is-Refine σ))]
  [(restrict τ (Refine y : σ Φ_y))
   (Refine y : (restrict τ σ) Φ_y)
   (where/hidden #f (is-Refine τ))]
  
  ;; Unions
  [(restrict (U τ ...) σ) (U^ ,@(map (λ (t) (term (restrict ,t σ))) (term (τ ...))))
   (where/hidden #t (common-val (U τ ...) σ))]
  
  [(restrict τ (U σ ...)) (U^ ,@(map (λ (t) (term (restrict τ ,t))) (term (σ ...))))
   (where/hidden #f (is-U τ))
   (where/hidden #t (common-val τ (U σ ...)))]
  
  ;; else if τ <: σ
  [(restrict τ σ) τ
   (judgment-holds (subtype ε τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))]
  
  ;; else
  [(restrict τ σ) σ
   (where #f (subtype ε τ σ))
   (where/hidden #f (is-U τ))
   (where/hidden #f (is-U σ))])

  ;; remove
(define-metafunction λDTR
  remove : τ σ -> τ
  ;; τ_1 <: τ_2
  [(remove τ σ) Bot
   (judgment-holds (subtype ε τ σ))]
  
  ;; Union
  [(remove (U τ ...) σ) (U^ ,@(map (λ (t) (term (remove ,t σ))) (term (τ ...))))
   (where/hidden #f (subtype ε (U τ ...) σ))]
  
  ;; Refinement
  [(remove (Refine x : τ Φ_x) σ) (Refine x : (remove τ σ) Φ_x)
   (where/hidden #f (subtype ε τ σ))]
  
  ;; non-Union
  [(remove τ σ) σ
   (where/hidden #f (subtype ε τ σ))
   (where/hidden #f (is-U τ))])

(define-judgment-form λDTR
  #:mode (path-postfix I I)
  #:contract (path-postfix o o)
  ;; lhs is a postfix of the rhs object 
  ;; (i.e. rhs can update lhs)
  [------------------ "Path-Postfix"
  (path-postfix (obj (pe_2 ...) x_1) 
                (obj (pe_1 ... pe_2 ...) x_1))])

(define-judgment-form λDTR
  #:mode (lexp-equal I I)
  #:contract (lexp-equal o o)
  [----------- "LExp-Equal-Refl"
   (lexp-equal o_1 o_1)]
  [(where #f #t)
   ----------- "LExp-Equal"
   (lexp-equal o_1 o_2)])

;; update type info in lhs w/ rhs if applicable
(define-metafunction λDTR
  τ-update : f f -> f
  ;; overlapping paths, update w/ path
  [(τ-update (fact (obj          (pe_τ ...) x) b_τ τ) 
             (fact (obj (pe_σ ... pe_τ ...) x) b_σ σ))
   (fact (obj (pe_τ ...) x) b_τ (π-update b_τ τ b_σ σ (pe_σ ...)))]
  
  ;; equal linear expressions, update types w/ empty path
  [(τ-update (fact o_τ b_τ τ) (fact o_σ b_σ σ))
   (fact o_τ b_τ (π-update b_τ τ b_σ σ ()))
   (judgment-holds (lexp-equal o_τ o_σ))]
  
  ;; incompatible objects, no-op
  [(τ-update (fact o_τ b_τ τ) (fact o_σ b_σ σ)) (fact o_τ b_τ τ)
   (where #f (path-postfix o_τ o_σ))
   (where #f (lexp-equal   o_τ o_σ))])


(define-metafunction λDTR
  ψ-update : ψ f -> ψ
  [(ψ-update TT f) FF]
  [(ψ-update FF f) TT]
  [(ψ-update f f_new) (τ-update f f_new)]
  [(ψ-update (And ψ_1 ψ_2) f_new) (And (ψ-update ψ_1 f_new) 
                                       (ψ-update ψ_2 f_new))]
  [(ψ-update (Or  ψ_1 ψ_2) f_new) (Or  (ψ-update ψ_1 f_new) 
                                       (ψ-update ψ_2 f_new))])

(define-metafunction λDTR
  update* : Γ f -> Γ
  [(update* Γ f)
   ,(map (λ (ψ) (term (ψ-update ,ψ f))) (term Γ))])


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
   (common-val Φ (U τ_0 ... τ τ_1 ...) σ)]
  
  [(common-val Φ τ σ)
   ------------------ "CV-Union-rhs"
   (common-val Φ τ (U σ_0 ... σ σ_1 ...))]
  
  [(common-val Φ τ_1 τ_2)
   (common-val Φ σ_1 σ_2)
   -------------------- "CV-Pair"
   (common-val Φ (Pair τ_1 σ_1) (Pair τ_2 σ_2))]
  
  [(common-val Φ τ σ)
   -------------------- "CV-Vec"
   (common-val Φ (Vec τ) (Vec σ))]
  
  [------------------ "CV-Abs"
   (common-val Φ
               (Abs x σ_1 τ_1 ψ_1+ ψ_1- oo_1) 
               (Abs y σ_2 τ_2 ψ_2+ ψ_2- oo_2))]
  
  [(fme-sat (app Φ Φ_x))
   (common-val Φ τ σ)
   (not-Refine σ)
   ----------------- "CV-Refine-L"
   (common-val Φ (Refine x : τ Φ_x) σ)]
  
  [(fme-sat (app Φ Φ_y))
   (common-val Φ τ σ)
   (not-Refine τ)
   ----------------- "CV-Refine-R"
   (common-val Φ τ (Refine y : σ Φ_y))]
  
  [(where o_f (fresh-o Φ
                       (Refine x : τ Φ_x) 
                       (Refine y : σ Φ_y)))
   (fme-sat (app (subst Φ_x o_f x) 
                 (subst Φ_y o_f y)
                 Φ))
   (common-val Φ τ σ)
   ----------------- "CV-Refine"
   (common-val Φ
               (Refine x : τ Φ_x) 
               (Refine y : σ Φ_y))])

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
  #:mode (not-U I)
  #:contract (not-U τ)
  [(where #f (is-U τ))
   -------------- "NonU"
   (not-U τ)])

(define-judgment-form λDTR
  #:mode (is-Refine I)
  #:contract (is-Refine τ)
  [-------------- "IsRefine"
   (is-Refine (Refine x : τ Φ))])

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
  [(subst ψ  oo_new x) (subst-ψ ψ   oo_new x)]
  [(subst τ  oo_new x) (subst-τ τ   oo_new x)])


(define-metafunction λDTR
  fact^ : oo b τ -> ψ
  [(fact^ ø b τ) FF]
  [(fact^ o b τ) (fact o b τ)])

(define-metafunction λDTR
  And^ : ψ ψ -> ψ
  [(And^ TT ψ) ψ]
  [(And^ ψ TT) ψ]
  [(And^ FF ψ) FF]
  [(And^ ψ FF) FF])

(define-metafunction λDTR
  Or^ : ψ ψ -> ψ
  [(Or^ TT ψ) TT]
  [(Or^ ψ TT) TT]
  [(Or^ FF ψ) ψ]
  [(Or^ ψ FF) ψ])

(define-metafunction λDTR
  +^ : oo oo -> oo
  [(+^ ø oo) ø]
  [(+^ oo ø) ø]
  [(+^ 0 o) o]
  [(+^ o 0) o]
  [(+^ i_l i_r) ,(+ (term i_l) (term i_r))]
  [(+^ o_l o_r) (+ o_l o_r)
   (side-condition (nand (exact-integer? (term o_l))
                         (exact-integer? (term o_r))))])

(define-metafunction λDTR
  *^ : oo oo -> oo
  [(*^ i_l i_r) ,(* (term i_l) (term i_r))]
  [(*^ 0 o) 0]
  [(*^ 1 o) o]
  [(*^ i o) (* i o)
   (side-condition (nor (exact-integer? (term o))
                        (= 0 (term i))
                        (= 1 (term i))))]
  [(*^ o i) (*^ i o)
   (side-condition (not (exact-integer? (term o))))]
  [(*^ oo_l oo_r) ø
   (side-condition (not (exact-integer? (term oo_l))))
   (side-condition (not (exact-integer? (term oo_r))))])

;; substitution in oo
;; will null out completely invalid combinations 
;; (e.g. creating a linear expression w/ a non-empty path)
(define-metafunction λDTR
  subst-oo : oo oo x -> oo
  ;; null -> null
  [(subst-oo ø oo_new x) ø]
  ;; matched obj w/ empty path
  [(subst-oo (obj ε x) oo_new x) oo_new]
  ;; null into obj
  [(subst-oo (obj π x) ø x) ø]
  ;; obj into obj, path join
  [(subst-oo (obj [pe_0 pe_1 ...] x) (obj π_y y) x) (obj (app [pe_0 pe_1 ...] π_y) y)]
  ;; invalid obj/linear combinations, resulting in ø
  [(subst-oo (obj [pe_0 pe_1 ...] x) i x) ø]
  [(subst-oo (obj [pe_0 pe_1 ...] x) (* i o) x) ø]
  [(subst-oo (obj (pe_0 pe_1 ...) x) (+ o_l o_r) x) ø]
  ;; possibly valid linear combinations
  [(subst-oo (+ o_l o_r) oo x) (+^ (subst o_l oo x)
                                   (subst o_r oo x))]
  [(subst-oo (* i o) oo x) (*^ i
                               (subst o oo x))])

(define-metafunction λDTR
  subst-ψ : ψ oo x -> ψ
  ;; TT/FF subst
  [(subst-ψ TT oo x) TT]
  [(subst-ψ FF oo x) FF]
  ;; fact subst
  [(subst-ψ (fact o b τ) oo_new x) (fact^ (subst o oo_new x) 
                                          b
                                          (subst τ oo_new x))]
  ;; And/Or
  [(subst-ψ (And ψ_l ψ_r) οο x) (And^ (subst ψ_l oo x)
                                      (subst ψ_r oo x))]
  [(subst-ψ (Or ψ_l ψ_r) οο x) (Or^ (subst ψ_l oo x)
                                    (subst ψ_r oo x))]
  
  ;; Φ
  [(subst-ψ Φ ø x) (fme-elim Φ x)]
  [(subst-ψ Φ o x) (subst-Φ Φ o x)])

(define-metafunction λDTR 
  ≤^ : oo oo -> Φ
  [(≤^ ø oo) []]
  [(≤^ oo ø) []]
  [(≤^ o_l o_r) [(o_l ≤ o_r)]])

(define-metafunction λDTR
  subst-Φ : Φ o x -> ψ
  [(subst-Φ [] o x) []]
  [(subst-Φ [(o_0l ≤ o_0r) (o_1l ≤ o_1r) ...] o x) FF
   (where FF (subst-Φ [(o_1l ≤ o_1r) ...] o x))]
  [(subst-Φ [(o_0l ≤ o_0r) (o_1l ≤ o_1r) ...] o x) FF
   (where [] (≤^ (subst o_0l o x)
                 (subst o_0r o x)))]
  [(subst-Φ [(o_0l ≤ o_0r) (o_1l ≤ o_1r) ...] o x) (app [φ] Φ_rest)
   (where Φ_rest (subst-Φ [(o_1l ≤ o_1r) ...] o x))
   (where [φ] (≤^ (subst o_0l o x)
                  (subst o_0r o x)))])
  
;; standard captura avoiding substitution
;; with smart constructors
(define-metafunction λDTR
  subst-τ : τ oo x -> τ
  [(subst-τ Top oo x Top) Top]
  [(subst-τ Int oo x Int) Int]
  [(subst-τ Str oo x Str) Str]
  [(subst-τ T oo x T) T]
  [(subst-τ F oo x F) F]
  [(subst-τ (U τ ...) oo x) (U^ (subst τ oo x) ...)]
  [(subst-τ (Pair τ σ) oo x)
   (Pair^ (subst τ oo x) (subst σ oo x))]
  [(subst-τ (Abs x σ τ ψ_+ ψ_- oo_f) oo x) (Abs x (subst σ oo x) τ ψ_+ ψ_- oo_f)]
  [(subst-τ (Abs y σ τ ψ_+ ψ_- oo_f) oo x)
   (Abs z 
        (subst (subst σ (var z) y) oo x)
        (subst (subst τ (var z) y) oo x)
        (subst (subst ψ_+ (var z) y) oo x)
        (subst (subst ψ_- (var z) y) oo x)
        (subst (subst oo_f (var z) y) oo x))
   (judgment-holds (<> x y))
   (where z (var ,(gensym 'fresh)))]
  [(subst-τ (Refine x : τ Φ) oo x) (Refine x : τ Φ)]
  [(subst-τ (Refine y : τ Φ) oo x) 
   (Refine z : 
           (subst (subst τ (var z) y) oo x) 
           (subst (subst Φ (var z) y) oo x))
   (judgment-holds (<> x y))
   (where z (var ,(gensym 'fresh)))])

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
