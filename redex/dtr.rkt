#lang racket

(require redex)

(module+ test
  (require redex rackunit))


(define-language λDTR
  [x      ::= variable-not-otherwise-mentioned]
  [b   ::= boolean]
  [z    ::= integer]
  [str    ::= string]
  [e   ::= x (ann e t) (e e) (λ (x : t) e) (if e e e) 
       c b z str (let (x e) e) (cons e e) (vec e ...)
       (car e) (cdr e) (vec-ref e e)]
  [c   ::= add1 zero? int? str? bool? proc? 
       str-len + * error cons? vec?]
  [pe  ::= CAR CDR LEN]
  [π   ::= (pe ...)]
  [loc ::= (& π x)]
  [o   ::= z loc (* z o) (+ o ...)]
  [Φ   ::= ((o ≤ o) ...)] 
  [oo  ::= o ⊘]
  [σ   ::= Top T F Int Str (U t ...) (λ x τ τ ψ ψ oo) (τ * τ) (Vec τ)]
  [τ   ::= σ (x : τ [Φ])]
  [a   ::= (o -: t) (o -! t)]
  [ψ   ::= a (Or ψ ψ) (And ψ ψ) TT FF Φ]
  [Θ   ::= ((x -> o) ...)]
  [Γa  ::= (a ...)]
  [Γ   ::= (ψ ...)])


(define-metafunction λDTR
  var : x -> o
  [(var x_1) (& () x_1)])

(define-metafunction λDTR
  fresh-o : any ... -> o
  [(fresh-o any ...) (var (gensym 'fresh))])

(define-judgment-form λDTR
  #:mode (fme-imp I I)
  #:contract (fme-imp Φ Φ)
  [----------- "F-Implies"
   (fme-imp Φ_1 Φ_1)])

(define-judgment-form λDTR
  #:mode (fme-sat I)
  #:contract (fme-sat Φ)
  [----------- "F-Sat"
   (fme-sat Φ_1)])

(define-metafunction λDTR
  ~ : ψ -> ψ
  [(~ TT) FF]
  [(~ FF) TT]
  [(~ (o_1 -: τ_1)) (o_1 -! τ_1)]
  [(~ (o_1 -! τ_1)) (o_1 -: τ_1)]
  [(~ (And ψ_1 ψ_2)) (Or (~ ψ_1) (~ ψ_2))]
  [(~ (Or ψ_1 ψ_2)) (And (~ ψ_1) (~ ψ_2))])


(define-metafunction λDTR
  subst : any o x -> any
  [(subst any_1 o_1 x_1) any_1])


(define-judgment-form λDTR
  #:mode (subobj I I)
  #:contract (subobj oo oo)
  [------------------- "SO-Refl"
   (subobj oo_1 oo_1)]
  
  [------------------- "SO-Top"
   (subobj oo_1 ⊘)])

(define-judgment-form λDTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [--------------- "S-Refl"
   (subtype τ_1 τ_1)]
  
  [--------------- "S-Top"
   (subtype τ_1 Top)]
  
  [(subtype τ_1 τ_3)
   --------------- "S-UnionSuper"
   (subtype τ_1 (U τ_2 ... τ_3 τ_4 ...))]
  
  [(subtype τ_1 τ_2) ...
   --------------- "S-UnionSub"
   (subtype (U τ_1 ...) τ_2)]
  
  [(subtype τ_1 τ_3)
   (subtype τ_2 τ_4)
   ----------------- "S-Pair"
   (subtype (τ_1 * τ_2) (τ_3 * τ_4))]
  
  [(subtype τ_2d (subst τ_1d (var x_2) x_1)) 
   (subtype (subst τ_1r (var x_2) x_1) τ_2r) 
   (subobj (subst oo_1 (var x_2) x_1) oo_2)
   (proves [(subst ψ_1+ (var x_2) x_1)] ψ_2+)
   (proves [(subst ψ_1- (var x_2) x_1)] ψ_2-)
   ------------------------------------------ "S-Fun"
   (subtype (λ x_1 τ_1d τ_1r ψ_1+ ψ_1- oo_1)
            (λ x_2 τ_2d τ_2r ψ_2+ ψ_2- oo_2))]
  
  [(subtype τ_1 τ_2)
   ------------------- "S-RefineE"
   (subtype (x_1 : τ_1 [Φ_1]) τ_2)]
  
  [(where #f (fme-sat Φ_1))
   ------------------- "S-RefineBot"
   (subtype (x_1 : τ_1 [Φ_1]) τ_2)]
  
  [(subtype τ_1 τ_2)
   (where o_f (fresh-o (x_1 : τ_1 [Φ_1]) (x_2 : τ_2 [Φ_2])))
   (fme-imp (subst Φ_1 o_f x_1) (subst Φ_2 o_f x_2))
   ------------------- "S-RefineSub"
   (subtype (x_1 : τ_1 [Φ_1]) (x_2 : τ_2 [Φ_2]))])


(define-judgment-form λDTR
  #:mode (proves I I)
  #:contract (proves Γ ψ)
  [(proves-alg () Γ_1 ψ_1)
   ------------------- "Proves"
   (proves Γ_1 ψ_1)])


(define-judgment-form λDTR
  #:mode (proves-alg I I I)
  #:contract (proves-alg Γa Γ ψ)
  
  [(subtype τ_1 τ_2)
   ---------------- "L-Sub"
   (proves-alg (a_1 ... (o_1 -: τ_1) a_2 ...) () (o_1 -: τ_2))]
  
  [(subtype τ_2 τ_1)
   ---------------- "L-SubNot"
   (proves-alg (a_1 ... (o_1 -! τ_1) a_2 ...) () (o_1 -! τ_2))]
  
  [(type-conflict τ_1 τ_2)
   ---------------- "L-Conflict"
   (proves-alg (a_1 ... (o_1 -: τ_1) a_2 ...) () (o_1 -: τ_2))]
    
  [---------------------- "L-True"
   (proves-alg Γa_1 Γ_1 TT)]
  
  [(proves-alg Γa_1 (ψ_1 ...) ψ_2)
   ---------------------- "L-TrueSkip"
   (proves-alg Γa_1 (TT ψ_1 ...) ψ_2)]
  
  [---------------------- "L-False"
   (proves-alg Γa_1 (FF ψ_1 ...) ψ_2)]
  
  [(proves-alg Γa_1 (ψ_1 ψ_2 ψ_3 ...) ψ_4)
   ---------------------- "L-AndE"
   (proves-alg Γa_1 ((And ψ_1 ψ_2) ψ_3 ...) ψ_4)]
  
  [(proves-alg Γa_1 () ψ_1)
   (proves-alg Γa_1 () ψ_2)
   ---------------------- "L-AndI"
   (proves-alg Γa_1 () (And ψ_1 ψ_2))]
  
  [(proves-alg Γa_1 (ψ_1 ψ_3 ...) ψ_4)
   (proves-alg Γa_1 (ψ_2 ψ_3 ...) ψ_4)
   ---------------------- "L-OrE"
   (proves-alg Γa_1 ((Or ψ_1 ψ_2) ψ_3 ...) ψ_4)]
  
  [(proves-alg Γa_1 () ψ_1)
   ---------------------- "L-OrI-L"
   (proves-alg Γa_1 () (Or ψ_1 ψ_2))]
  
  [(proves-alg Γa_1 () ψ_2)
   ---------------------- "L-OrI-R"
   (proves-alg Γa_1 () (Or ψ_1 ψ_2))]
  
  [(contains-Bot τ_1)
   ---------------------- "L-Bot"
   (proves-alg (a_1 ... (o_1 -: τ_1) a_2 ...) () a_3)]
  
  [(proves-alg (update* a_2 (a_2 a_1 ...)) 
               (update* a_2 (ψ_1 ...)) ψ_2)
   ---------------------- "L-Update*"
   (proves-alg (a_1 ...) (a_2 ψ_1 ...) ψ_2)])


(define-judgment-form λDTR
  #:mode (contains-Bot I)
  #:contract (contains-Bot t)
  [(subtype τ_1 (U))
   ------------------- "Bot-Subtype"
   (contains-Bot τ_1)]
  
  [(contains-Bot τ_1)
   ------------------- "Bot-Pair-L"
   (contains-Bot (τ_1 * τ_2))]
  
  [(contains-Bot τ_2)
   ------------------- "Bot-Pair-R"
   (contains-Bot (τ_1 * τ_2))]
  
  [(contains-Bot τ_1)
   ------------------- "Bot-Vec"
   (contains-Bot (Vec τ_1))])

;; Update needs to work on overlapping paths 
;; (like the original paper)
;; and on types where they contain
;; any objects w/ overlapping paths nested
;; inside

(define-metafunction λDTR
  π-update : b τ b τ π -> τ
  [(π-update b_1 τ_1 b_2 τ_2 π_2) τ_1]
  ;; [(update (τ_1 * τ_2) b_1 τ_new (pe_1 ... CAR))
  ;;  ((update τ_1 b_1 τ_new (pe_1 ...)) * τ_2)]
  
  ;; [(update (τ_1 * τ_2) b_1 τ_new (pe_1 ... CDR))
  ;;  (τ_1 * (update τ_2 b_1 τ_new (pe_1 ...)))]
  
  ;; [(update τ_1 b_1 τ_new (pe_1 ... CAR))
  ;;  (update τ_1 b_1 (τ_new * Top) (pe_1 ...))
  ;;  (judgment-holds (non-Pair τ_1))]
  
  ;; [(update τ_1 b_1 τ_new (pe_1 ... CDR))
  ;;  (update τ_1 b_1 (Top * τ_new) (pe_1 ...))
  ;;  (judgment-holds (non-Pair τ_1))]
  
  ;; [(update τ_1 #t τ_2 ()) (restrict τ_1 τ_2)]
  
  ;; [(update τ_1 #f τ_2 ()) (remove τ_1 τ_2)]
  )

(define-metafunction λDTR
  Φ-update : Φ Φ -> Φ
  [(Φ-update Φ_1 Φ_2) Φ_1])

(define-metafunction λDTR
  update-ψ : ψ a -> ψ
  [(update-ψ ψ_1 a) ψ_1])

(define-metafunction λDTR
  update* : (ψ ...) a -> (ψ ...)
  [(update* (ψ_1 ...)) (ψ_1 ...)])


(define-judgment-form λDTR
  #:mode (common-val I I)
  #:contract (common-val τ τ)
  [------------------ "CV-Eq"
   (common-val τ_1 τ_1)]
  
  [------------------ "CV-Top-lhs"
   (common-val Top τ_1)]
  
  [------------------ "CV-Top-rhs"
   (common-val τ_1 Top)]
  
  [(common-val τ_2 τ_4)
   ------------------ "CV-Union-lhs"
   (common-val (U τ_1 ... τ_2 τ_3 ...) τ_4)]
  
  [(common-val τ_2 τ_4)
   ------------------ "CV-Union-rhs"
   (common-val τ_4 (U τ_1 ... τ_2 τ_3 ...))]
  
  [(common-val τ_1 τ_3)
   (common-val τ_2 τ_4)
   -------------------- "CV-Pair"
   (common-val (τ_1 * τ_2) (τ_3 * τ_4))]
  
  [------------------ "CV-Abs"
   (common-val (λ x_1 τ_1d τ_1r ψ_1+ ψ_1- oo_1) 
               (λ x_2 τ_2d τ_2r ψ_2+ ψ_2- oo_2))]
  
  [(fme-sat Φ_1)
   (common-val σ_1 σ_2)
   ----------------- "CV-Refine-L"
   (common-val (x_1 : σ_1 [Φ_1]) σ_2)]
  
  [(fme-sat Φ_2)
   (common-val σ_1 σ_2)
   ----------------- "CV-Refine-R"
   (common-val σ_1 (x_2 : σ_2 [Φ_2]))]
  
  [(where o_f (fresh-o (x_1 : σ_1 [Φ_1]) 
                       (x_2 : σ_2 [Φ_2])))
   (fme-sat (⋈ (subst Φ_1 o_f x_1) 
               (subst Φ_2 o_f x_2)))
   (common-val σ_1 σ_2)
   ----------------- "CV-Refine"
   (common-val (x_1 : σ_1 [Φ_1]) 
               (x_2 : σ_2 [Φ_2]))])

(define-metafunction λDTR
  ⋈ : Φ Φ -> Φ
    [(⋈ ((o_1 ≤ o_2) ...) ((o_3 ≤ o_4) ...)) ((o_1 ≤ o_2) ... (o_3 ≤ o_4) ...)]) 

(define-judgment-form λDTR
  #:mode (type-conflict I I)
  #:contract (type-conflict τ τ)
  [(where #f (common-val τ_1 τ_2))
   --------------- "TC-Conflict"
   (type-conflict τ_1 τ_2)])






