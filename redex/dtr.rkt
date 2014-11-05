#lang typed/racket

(require rackunit mtest)

(require/typed fme
  [#:opaque LExp lexp?]
  [#:struct Leq ([lhs : LExp] [rhs : LExp])]
  [lexp (->* ((U Integer (Tuple Integer Obj))) 
             #:rest (U Integer (Tuple Integer Obj)) 
             LExp)]
  [lexp-coefficient (-> LExp Obj Integer)]
  [lexp-constant (-> LExp Integer)]
  [lexp-vars (-> LExp (Listof Obj))]
  [lexp-scale (-> LExp Integer LExp)]
  [lexp-zero? (-> LExp Boolean)]
  [lexp-equal? (-> LExp LExp Boolean)]
  [lexp-subtract (-> LExp LExp LExp)]
  [lexp-add (-> LExp LExp LExp)]
  [lexp-set (-> LExp Obj Integer LExp)]
  [lexp-has-var? (-> LExp Obj Boolean)]
  [lexp-add1 (-> LExp LExp)]
  [lexp-subst (-> LExp Obj Obj LExp)]
  [lexp-subst-lexp (-> LExp LExp Obj LExp)]
  [leq-contains-var? (-> Leq Obj Boolean)]
  [leq-subst (-> Leq Obj Obj Leq)]
  [leq-subst-lexp (-> Leq LExp Obj Leq)]
  [leq-negate (-> Leq Leq)]
  [leq-vars (-> Leq (Listof Obj))]
  [sli-vars (-> SLI (Listof Obj))]
  [sli-subst (-> SLI Obj Obj SLI)]
  [sli-subst-lexp (-> SLI LExp Obj SLI)]
  [sli-elim-var (-> SLI Obj SLI)]
  [sli-satisfiable? (-> SLI Boolean)]
  [sli-proves-leq? (-> SLI Leq Boolean)]
  [sli-proves-sli? (-> SLI SLI Boolean)])


;; *************************************
;; 
;;                                      
;;                                      
;;                ;                     
;;  ;;    ;;      ;                     
;;  ;;;  ;;;                            
;;  ; ;  ; ;                            
;;  ; ;  ; ;    ;;;     ;;;;;     ;;;   
;;  ; ;;;; ;      ;    ;     ;   ;   ;  
;;  ;  ;;  ;      ;    ;        ;       
;;  ;  ;;  ;      ;    ;;;;     ;       
;;  ;      ;      ;       ;;;;  ;       
;;  ;      ;      ;          ;  ;       
;;  ;      ;      ;    ;     ;   ;   ;  
;;  ;      ;   ;;;;;;;  ;;;;;     ;;;   
;;                                      
;;                                      
;;                                      
;;                                      


(define-syntax term
  (syntax-rules ()
    [(term (n o)) (list n o)]
    [(term n) n]))

(define-syntax-rule (+: t ...)
  (LExp (term t) ...))


(define-syntax ≤
  (syntax-rules ()
    [(≤ l1 l2) (And (list (Leq l1 l2)))]
    [(≤ l1 l2 l3) (And (list (Leq l1 l2) 
                             (Leq l2 l3)))]
    [(≤ l1 l2 l3 l4 ...) (And (list (Leq l1 l2) 
                                    (≤ l2 l3 l4 ...)))]))

(define-syntax-rule (== l1 l2)
  (≤ l1 l2 l1))

(define-syntax-rule (!= l1 l2)
  (¬ (== l1 l2)))

(define-syntax-rule (U: t ...)
  (Union (list t ...)))

(define-syntax-rule (And: p ...)
  (And (list p ...)))

(define-syntax-rule (Or: p ...)
  (Or (list p ...)))


(: hash-empty? (All (a b) (case-> (-> (HashTable a b) Boolean) 
                                  (-> HashTableTop Boolean))))
(define (hash-empty? h)
  (zero? (hash-count h)))

(define app append)


;;*****************************************                              
;;                                               
;;                                               
;;                                               
;;   ;;;;;;;                                     
;;      ;                                        
;;      ;                                        
;;      ;     ;     ;  ; ;;;     ;;;;     ;;;;;  
;;      ;      ;   ;;  ;;   ;    ;   ;   ;     ; 
;;      ;      ;   ;   ;     ;  ;    ;;  ;       
;;      ;      ;   ;   ;     ;  ;;;;;;;  ;;;;    
;;      ;       ; ;;   ;     ;  ;           ;;;; 
;;      ;       ; ;    ;     ;  ;              ; 
;;      ;        ;;    ;;   ;    ;       ;     ; 
;;      ;        ;;    ; ;;;      ;;;;    ;;;;;  
;;               ;     ;                         
;;               ;     ;                         
;;             ;;      ;                         
;;                                               


(define prim-ops '(add1 zero? int? str? bool? proc? 
                   str-len + error cons? car cdr <=))

(define-type Path (Listof (U 'CAR 'CDR)))

;; Objects
(define-type Var Symbol)
(define-predicate Var? Var)
(struct Local ([var : Symbol]))
(define-type Id (U Var Local))
(define-predicate Id? Id)

(struct: Obj ([path : Path] [id : Id]) #:transparent)
(define-type Ref (U Obj LExp))   ;; lexp  x   (Obj (car) lexp)
(define-predicate Ref? Ref)
(define-type SLI (Listof Leq))
(define-predicate SLI? SLI)

(: var (-> Id Obj))
(define (var x)
  (Obj empty x))

;; Types
(struct: Top () #:transparent)
(struct: T () #:transparent)
(struct: F () #:transparent)
(struct: Int () #:transparent)
(struct: Str () #:transparent)
(struct: Union ([types : (Listof Type)]) #:transparent)
(struct: Abs ([arg : Symbol] 
              [domain : Type]
              [range : Type]
              [prop+ : Prop] 
              [prop- : Prop] 
              [ref : (Opt Ref)]) #:transparent)
(struct: Pair ([car : Type] [cdr : Type]) #:transparent)
(struct: Dep ([var : Var] [type : Type] [prop : Prop]) #:transparent)
(define-type Type (U Top T F Int Str Union Abs Pair Dep))
(define-predicate Type? Type)

;; Propositions

(struct: TT () #:transparent)
(struct: FF () #:transparent)
(struct: Atom  ([bool : Boolean] [ref : Ref] [type : Type]) #:transparent)
(struct: And ([props : (Listof Prop)]) #:transparent)
(struct: Or ([props : (Listof Prop)]) #:transparent)
(define-type Prop (U TT FF Atom And Or Leq))
(define-predicate Prop? Prop)

(define (Bool)
  (Union (list (T) (F))))
(: Bool? (-> Any Boolean))
(define (Bool? t)
  (equal? t
          (Union (list (T) (F)))))


(define (Bot)
  (Union empty))
(: Bot? (Any -> Boolean))
(define (Bot? a)
  (and (Union? a)
       (empty? (Union-types a))))

;; Environments
(define-type TMap (HashTable Ref (Listof Type)))
(define-type NTMap (HashTable Ref Type))

(define-type Opt Option)
(struct: Env ([props : (Listof Prop)] 
              [types+ : TMap]
              [types- : NTMap]
              [sli : SLI]))

(: env ((Listof Prop) -> Env))
(define (env lop)
  (Env lop (hash) (hash) empty))

(: env+P (Env Prop -> Env))
(define (env+P E P)
  (match E
    [(Env ps ts+ ts- sli) (Env (cons P ps) ts+ ts- sli)]))

;; Expressions
(struct: Ann ([exp : (U Symbol Exp)] [type : Type]) #:transparent)
(struct: App ([rator : Exp] [rand : Exp]) #:transparent)
(struct: Fun ([arg : Symbol] [arg-type : Type] [body : Exp]) #:transparent)
(struct: If ([test : Exp] [then : Exp] [else : Exp]) #:transparent)
(struct: Let ([var : Symbol] [var-exp : Exp] [body : Exp]) #:transparent)
(define-type Op (U 'add1 'zero? 'int? 'str? 'bool? 'proc? 
                   'str-len '+ 'error 'cons? 'car 'cdr '<=))

(: Op? (pred Op))
(define (Op? x)
  (or (equal? x 'add1)
      (equal? x 'zero?)
      (equal? x 'int?)
      (equal? x 'str?)
      (equal? x 'bool?)
      (equal? x 'proc?)
      (equal? x 'str-len)
      (equal? x '+)
      (equal? x 'error)
      (equal? x 'cons?)
      (equal? x 'car)
      (equal? x 'cdr)
      (equal? x '<=)))

(define-type Val (U Integer String Boolean))
(define-type Exp (U Val Ann App Fun If Let))


(: Val? (-> Any Boolean : Val))
(define (Val? a)
  (or (exact-integer? a)
      (string? a)
      (boolean? a)))

(: Is (Obj Type -> Atom))
(define (Is obj type)
  (Atom #t obj type))

(: Not (Obj Type -> Atom))
(define (Not obj type)
  (Atom #f obj type))


(struct TypeInfo ([type : Type] 
                  [prop+ : Prop]
                  [prop- : Prop]
                  [ref : Ref]))

;;*****************************************
;;                                               
;;                                               
;;                         ;                     
;;   ;     ;               ;     ;;;;            
;;   ;     ;    ;                   ;            
;;   ;     ;    ;                   ;            
;;   ;     ;  ;;;;;;     ;;;        ;     ;;;;;  
;;   ;     ;    ;          ;        ;    ;     ; 
;;   ;     ;    ;          ;        ;    ;       
;;   ;     ;    ;          ;        ;    ;;;;    
;;   ;     ;    ;          ;        ;       ;;;; 
;;   ;     ;    ;          ;        ;          ; 
;;   ;;   ;;    ;          ;        ;    ;     ; 
;;    ;;;;;      ;;;    ;;;;;;;      ;;;  ;;;;;  
;;                                               
;;                                               
;;                                               
;;                                               

(: prefix? (All (α β) ((Listof α) (Listof β) -> Boolean)))
(define (prefix? l1 l2)
  (match* (l1 l2)
    [('() _) #t]
    [((cons x xs1) (cons x xs2))
     (prefix? xs1 xs2)]
    [(_ _) #f]))

(: postfix? (All (α β) ((Listof α) (Listof β) -> Boolean)))
(define (postfix? l1 l2)
  (prefix? (reverse l1) (reverse l2)))

(: ¬ (Prop -> Prop))
(define (¬ p)
  (match p
    [(TT) (FF)]
    [(FF) (TT)]
    [(Atom b r t) (Atom (not b) r t)]
    [(And ps) (Or (map ¬ ps))]
    [(Or ps) (And (map ¬ ps))]
    ;; empty SLI
    [(? Leq? l) (leq-negate l)]))

(: contains-Bot? (Type -> Boolean))
(define (contains-Bot? t)
  (match t
    [(Union '()) #t]
    [(Pair lhs rhs) (or (contains-Bot? lhs)
                        (contains-Bot? rhs))]
    [_ #f]))

(module+ test
  (chk (contains-Bot? (Bot)))
  (chk (contains-Bot? (Pair (Top) (Bot))))
  (chk (contains-Bot? (Pair (Pair (Bot) (Top)) (Top))))
  (chk~ (contains-Bot? (U: (Int) (Bot) (Str)))))

(: fvs ((U (Opt Ref) Type Prop) -> (Listof Id)))
(define (fvs e)
  (match e
    ;; References
    [#f empty]
    [(Obj _ x) (list x)]
    [(? lexp? l) (map Obj-id (lexp-vars l))]
    ;; Types
    [(Top) empty]
    [(Int) empty]
    [(Str) empty]
    [(T) empty]
    [(F) empty]
    [(Union ts) empty]
    [(Pair t1 t2) (append (fvs t1) (fvs t2))]
    [(Abs x td tr p+ p- oo) (remove* (list x) 
                                     (append (fvs td)
                                             (fvs tr)
                                             (fvs p+)
                                             (fvs p-)
                                             (fvs oo)))]
    [(Dep x t p) (append (fvs t)
                         (remove* (list x)
                                  (fvs p)))]
    ;; Props
    [(TT) empty]
    [(FF) empty]
    [(Atom b r t) (append (fvs r) (fvs t))]
    [(Or ps) (foldl (λ ([loId : (Listof Id)]
                        [loIds : (Listof Id)])
                      (append loId loIds)) 
                    empty 
                    (map fvs ps))]
    [(And ps) (foldl (λ ([loId : (Listof Id)]
                         [loIds : (Listof Id)])
                       (append loId loIds)) 
                     empty 
                     (map fvs ps))]
    [(? Leq? l) (map Obj-id (leq-vars l))]
    [else (error 'fvs "unknown argument ~a" e)]))

(: subst-obj-in-lexp (LExp Obj Id -> LExp))
(define (subst-obj-in-lexp cur-l new-o x)
  (define y (Obj-id new-o))
  (define π2 (Obj-path new-o))
  (for/fold ([l : LExp cur-l])
            ([o (lexp-vars cur-l)])
    (match-let ([(Obj π1 z) o])
      (if (equal? x z)
          (lexp-subst l (Obj (append π1 π2) y) o)
          l))))

;; returning #f implies the substitution results
;; in a non-linear expression
(: subst-lexp-in-lexp (LExp LExp Id  -> (Opt LExp)))
(define (subst-lexp-in-lexp cur-l new-l x)
  (for/fold ([l : (Option LExp) cur-l])
            ([o (lexp-vars cur-l)])
    (let* ([z (Obj-id o)]
           [πz (Obj-path o)])
      (cond
       [(not l) #f]
       [(equal? x z) 
        (if (empty? πz)
            (lexp-add (lexp-set l o 0)
                      (lexp-scale new-l (lexp-coefficient l o)))
            #f)]
       [else l]))))

(: subst-in-lexp (LExp Ref Id -> (Opt LExp)))
(define (subst-in-lexp cur-l new x)
  (cond
   [(Obj? new)
    (subst-obj-in-lexp cur-l new x)]
   [(lexp? new)
    (subst-lexp-in-lexp cur-l new x)]))

(: subst-in-leq (Leq Ref Id -> (Opt Leq)))
(define (subst-in-leq cur-leq new x)
  (let ([lhs (subst-in-lexp (Leq-lhs cur-leq) new x)]
        [rhs (subst-in-lexp (Leq-rhs cur-leq) new x)])
  (and lhs rhs (Leq lhs rhs))))

(: subst-in-opt-ref ((Opt Ref) Ref Id -> (Opt Ref)))
(define (subst-in-opt-ref ref new x)
  ;; ref[new / x]
  (match* (ref new x)
    ;; ref[#f / x]
    [(#f _ _) #f]
    ;; obj(y)[new / x] x <> y
    [((Obj π1 y) _ x) #:when (not (equal? y x))
     ref]
    ;; obj(x)[new / x]
    [((Obj π1 y) (Obj π2 z) x) #:when (equal? y x)
     (Obj (app π1 π2) z)]
    [((Obj '() y) (? lexp? l) x) #:when (equal? y x)
     l]
    [((Obj `(,x . ,xs) y) (? lexp? l) x) #:when (equal? y x)
     #f]
    [((? lexp? l) _ x) #:when (not (member x (fvs l)))
     l]
    [((? lexp? l) (? Obj? o) x) #:when (member x (fvs l))
     (subst-obj-in-lexp l o x)]
    [((? lexp? l1) (? lexp? l2) x) #:when (member x (fvs l1)) 
     (subst-lexp-in-lexp l1 l2 x)]))


;; NOTE substitution in ICFP '10 ref obliterates
;; atomic props if the target id is in the fvs
;; of the type -- we're not sure why it does this,
;; it seems necc. to *not* do this in fact
(: subst-in-atom (Atom Ref Id -> Prop))
(define (subst-in-atom atom new id)
  (match* (atom new id)
    ;; Atom(lexp(w/ x)) [non-#f / x]
    [((Atom b (? lexp? l) t) (? Ref? r) x) #:when (member x (fvs l))
     (let ([new-l (subst-in-lexp l r x)])
       (if (lexp? new-l)
           (Atom b new-l (t_ t [new / x]))
           (TT)))]
    [((Atom b (? lexp? l) t) (? Ref? r) x) #:when (not (member x (fvs l)))
     atom]
    ;; Atom(obj _ y) [ref / x] x <> y
    [((Atom b (Obj π1 y) t) _ x) #:when (not (equal? y x))
     (Atom b (Obj π1 y)
           (t_ t [new / x]))]
    ;; Atom(obj _ x) [obj / x]
    [((Atom b (Obj π1 y) t) (Obj π2 z) x) #:when (equal? y x)
     (Atom b (Obj (app π1 π2) z)
           (t_ t [new / x]))]
    ;; Atom(obj _ x) [lexp / x]
    [((Atom b (Obj π1 y) t) (? lexp? l) x) #:when (equal? y x)
     (cond 
      [(empty? π1) (Atom b l (t_ t [new / x]))]
      [(and (= 1 (length (fvs l)))
            (zero? (lexp-constant l)))
       (let ([y (first (fvs l))])
         (Atom b (Obj π1 y) (t_ t [new / y])))]
      [else (FF)])]))




(: subst-in-prop (Prop Ref Id -> Prop))
(define (subst-in-prop p new x)
  (match* (p new x)
    [((TT) new x) p]
    [((FF) new x) p]
    ;; Is/Not null
    [((? Atom? atom) new x) (subst-in-atom atom new x)]
    [((And ps) new x) (And (map (λ ([p : Prop]) 
                                  (p_ p [new / x]))
                                ps))]
    [((Or ps) new x) (Or (map (λ ([p : Prop]) 
                                (p_ p [new / x]))
                              ps))]
    [((? Leq? l) _ x)
     (or (subst-in-leq l new x)
         (TT))]
    [(_ _ _) (error 'subst "unknown subst ~a ~a ~a" p new x)]))

(: subst-in-type (Type Ref Id -> Type))
(define (subst-in-type t new x)
  (match t
   [(Top) t]
   [(Int) t]
   [(Str) t]
   [(T) t]
   [(F) t]
   [(Union ts) 
    (Union (map (λ ([t : Type]) (t_ t [new / x])) 
                ts))]
   [(Pair lhs rhs) 
    (Pair (t_ lhs [new / x]) 
          (t_ rhs [new / x]))]
   [(Abs y td tr p+ p- r) #:when (equal? x y)
    (Abs y (t_ td [new / y]) tr p+ p- r)]
   [(Abs y td tr p+ p- r) #:when (not (equal? x y))
    (Abs y 
         (t_ td [new / x]) 
         (t_ tr [new / x]) 
         (p_ p+ [new / x]) 
         (p_ p- [new / x]) 
         (r_ r  [new / x]))]
   [(Dep y t p)
    (if (equal? x y)
        (Dep y (t_ t [new / x]) p)
        (Dep y 
             (t_ t [new / x]) 
             (p_ p [new / x])))]))

(define-syntax r_
  (syntax-rules (/)
    [(r_ opt-ref [new / x])
     (subst-in-opt-ref opt-ref new x)]))

(define-syntax t_
  (syntax-rules (/)
    [(t_ type [new / x])
     (subst-in-type type new x)]))

(define-syntax p_
  (syntax-rules (/)
    [(p_ prop [new / x])
     (subst-in-prop prop new x)]))


(: ext-TMap (TMap 
             Ref 
             Type 
             -> TMap))
(define (ext-TMap imap r t)
  (hash-set imap r (cons t (hash-ref imap r (λ () '())))))


(: ext-NTMap (NTMap 
              Ref 
              Type 
              -> NTMap))
(define (ext-NTMap nmap r t)
  (hash-set nmap r (if (hash-has-key? nmap r)
                       (Union (list t (hash-ref nmap r)))
                       t)))



(: reduce-Union (-> Type Type))
(define (reduce-Union t)
  (cond
   [(not (Union? t)) t]
   [else (let* ([ts (map reduce-Union (Union-types t))]
                [clean-ts (filter (λ ([t : Type]) 
                                    (not (contains-Bot? t))) ts)])
           (Union clean-ts))]))

;;*****************************************
;;                                      
;;                                      
;;                                      
;;   ;;;;;;             ;;;;            
;;   ;    ;;               ;            
;;   ;     ;               ;            
;;   ;     ;   ;;;;        ;     ;;;;;  
;;   ;    ;;   ;   ;       ;    ;     ; 
;;   ;;;;;    ;    ;;      ;    ;       
;;   ;    ;   ;;;;;;;      ;    ;;;;    
;;   ;     ;  ;            ;       ;;;; 
;;   ;     ;  ;            ;          ; 
;;   ;     ;   ;           ;    ;     ; 
;;   ;      ;   ;;;;        ;;;  ;;;;;  
;;                                      
;;                                      
;;                                      
;;                                      


(: subref? ((Opt Ref) (Opt Ref) -> Boolean))
(define (subref? r1 r2)
  (cond
   [(not r2) #t]
   [else (equal? r1 r2)]))

(: implies?  (Prop Prop -> Boolean))
(define (implies? p1 p2)
  (proves? (env (list p1)) p2))

(: tautology? (Prop -> Boolean))
(define (tautology? p)
  (proves? (env empty) p))

(: contradiction? (Prop -> Boolean))
(define (contradiction? p)
  (proves? (env (list p)) (FF)))

(: supertype? (Type Type -> Boolean))
(define (supertype? t1 t2)
  (subtype? t2 t1))

(: subtype? (Type Type -> Boolean))
(define (subtype? t1 t2)
  (match* (t1 t2)
    ;; S-Refl
    [(_ _) #:when (equal? t1 t2) #t]
    ;; S-Top
    [(_ (? Top?)) #t]
    ;; S-Top
    [((Pair t1l t1r) (Pair t2l t2r)) (and (subtype? t1l t2l)
                                          (subtype? t1r t2r))]
    ;; S-UnionSub
    [((Union ts) _) (andmap (curry supertype? t2) ts)]
    ;; S-UnionSuper
    [(_ (Union ts)) (ormap (curry subtype? t1) ts)]
    [((Pair t1l t1r) (Pair t2l t2r)) (and (subtype? t1l t2l)
                                          (subtype? t1r t2r))]
    ;; S-Fun
    [((Abs x1 t1d t1r p1+ p1- r1) 
      (Abs x2 t2d t2r p2+ p2- r2))
     (and (subtype? t2d (t_ t1d [(var x2) / x1]))
          (subtype? (t_ t1r [(var x2) / x1]) t2r)
          (subref? (r_ r1 [(var x2) / x1]) r2)
          (implies? (p_ p1+ [(var x2) / x1]) p2+)
          (implies? (p_ p1- [(var x2) / x1]) p2-))]
    ;; S-Dep
    [((Dep x tx px) (Dep y ty py)) (and (subtype? tx ty)
                                        (implies? px (p_ py [(var x) / y])))]
    ;; S-DepSub
    [((Dep _ t1 _) _) (subtype? t1 t2)]
    ;; S-DepTaut
    [(_ (Dep _ t2 p1)) (and (subtype? t1 t2)
                            (tautology? p1))]
    [(_ _) #f]))

(: equiv-obj-lexp? (Obj LExp -> Boolean))
(define (equiv-obj-lexp? o l)
  (and (empty? (Obj-path o)) 
       (lexp-equal? l (lexp (list 1 o)))))

(: ref-equiv? (Ref Ref -> Boolean))
(define (ref-equiv? r1 r2)
  (match* (r1 r2)
    [((? lexp? l1) (? lexp? l2)) (lexp-equal? l1 l2)]
    [((? lexp? l) (? Obj? o)) (equiv-obj-lexp? o l)]
    [((? lexp? l) (? Obj? o)) (equiv-obj-lexp? o l)]
    [((Obj π2 x) (Obj π1 y)) (equal? r1 r2)]))

(: gen-type-atoms (-> TMap (Listof Atom)))
(define (gen-type-atoms ts+)
  (for/list : (Listof Atom) ([cur-r : Ref (hash-keys ts+)])
    (Atom #t cur-r
          (for/fold ([cur-t : Type (Top)])
                    ([other-r : Ref (hash-keys ts+)])
            (match* (cur-r other-r)
              [((Obj π2 x) (Obj π1 y))
               (if (and (equal? x y) (postfix? π2 π1))
                   (foldl (λ ([next-t : Type]
                              [acc-t : Type]) 
                            (update acc-t #t next-t π1))
                          cur-t
                          (hash-ref ts+ other-r))
                   cur-t)]
              [(_ _) (if (ref-equiv? cur-r other-r)
                         (foldl (λ ([next-t : Type]
                                    [acc-t : Type]) 
                                  (update acc-t #t next-t '()))
                                cur-t
                                (hash-ref ts+ other-r))
                         cur-t)])))))
(: gen-neg-atoms (-> NTMap (Listof Atom)))
(define (gen-neg-atoms ts-)
  (for/list ([r : Ref (hash-keys ts-)])
    (Atom #f r (hash-ref ts- r))))

(: witness? ((U SLI Atom) Prop -> Boolean))
(define (witness? atom goal)
  (match* (atom goal)
    [((Atom #t r t) _) #:when (contains-Bot? t)
     #t]
    [((Atom #t r1 t1) (Atom #t r2 t2))
     (and (ref-equiv? r1 r2)
          (subtype? t1 t2))]
    [((Atom #f r1 t1) (Atom #f r2 t2))
     (and (ref-equiv? r1 r2)
          (subtype? t2 t1))]
    [((Atom #t r1 t1) (Atom #f r2 t2))
     (and (ref-equiv? r1 r2)
          (type-conflict? t1 t2))]
    [((? SLI? sli) (? Leq? l))
     (sli-proves-leq? sli l)]
    [((? SLI? sli) _) #:when (not (sli-satisfiable? sli))
     #t]
    [(_ _) #f]))


  (: update-with-type-negations (TMap NTMap -> TMap))
(define (update-with-type-negations ts+ ts-)
  (for/hash : TMap ([cur-r : Ref (hash-keys ts+)])
    (values 
     cur-r
     (for/fold ([ts : (Listof Type) (hash-ref ts+ cur-r)])
               ([other-r : Ref (hash-keys ts-)])
       (match* (cur-r other-r)
         [((Obj π2 x) (Obj π1 y))
          (if (and (equal? x y) (postfix? π2 π1))
              (map (λ ([t : Type]) (update t #f (hash-ref ts- other-r) π1)) ts)
              ts)]
         [(_ _) (if (ref-equiv? cur-r other-r)
                    (map (λ ([t : Type]) (update t #f (hash-ref ts- other-r) '())) ts)
                    ts)])))))

(: proves? (Env Prop -> Boolean))
(define (proves? E goal)
  (match* (E goal)
    ;; L-TT
    [(_ (TT)) #t]
    ;; L-AndI
    [(_ (And ps)) (andmap (curry proves? E) ps)]
    ;; L-OrI
    [(_ (Or ps)) (ormap (curry proves? E) ps)]
    ;; L-False
    [((Env (cons (FF) ps) ts+ ts- sli) _) #t]
    ;; L-TTSkip
    [((Env (cons (TT) ps) ts+ ts- sli) _) 
     (proves? (Env ps ts+ ts- sli) goal)]
    ;; L-AndE
    [((Env (cons (And ps2) ps) ts+ ts- sli) _) 
     (proves? (Env (app ps2 ps) ts+ ts- sli) goal)]
    ;; L-OrE
    [((Env (cons (Or ps2) ps) ts+ ts- sli) _) 
     (andmap (λ ([p : Prop])
               (proves? (Env (cons p ps) ts+ ts- sli) goal))
             ps2)]
    ;; L-Is-Move
    [((Env (cons (Atom #t r t) ps) ts+ ts- sli) _)
     (proves? (Env ps (ext-TMap ts+ r t) ts- sli) goal)]
    ;; L-NotMove
    [((Env (cons (Atom #f r t) ps) ts+ ts- sli) _)
     (proves? (Env ps ts+ (ext-NTMap ts- r t) sli) goal)]
    ;; L-Leq-Move
    [((Env (cons (? Leq? l) ps) ts+ ts- sli) _)
     (proves? (Env ps ts+ ts- (cons l sli)) goal)]
    ;; L-Update*
    [((Env (? empty?) ts+ ts- sli) _)
     (let ([atoms : (Listof (U SLI Atom)) 
                  (append (cons sli (gen-type-atoms (update-with-type-negations ts+ ts-)))
                          (gen-neg-atoms ts-))])
       (ormap (λ ([a : (U SLI Atom)])
                (witness? a goal))
              atoms))]
    [(_ _) (error 'proves? "unhandled case: ~a ~a" E goal)]))

(: common-val? (Type Type -> Boolean))
(define (common-val? t1 t2)
  (match* (t1 t2)
    [(_ _) #:when (or (contains-Bot? t1)
                      (contains-Bot? t2)) 
     #f]
    [(_ _) #:when (equal? t1 t2) #t]
    [((Top) _) #t]
    [(_ (Top)) #t]
    [(_ (Union ts)) (ormap (λ ([t : Type]) (common-val? t1 t)) ts)]
    [((Union ts) _) (ormap (λ ([t : Type]) (common-val? t t2)) ts)]
    [((Pair t11 t12) (Pair t21 t22)) (and (common-val? t11 t21)
                                          (common-val? t12 t22))]
    [((? Abs?) (? Abs?)) #t]
    [((Dep x1 t1 p1) (Dep x2 t2 p2)) 
     (and (not (contradiction? (And (list p1 (p_ p2 [(var x1) / x2])))))
          (common-val? t1 t2))]
    [((Dep x t p) _) (and (not (contradiction? p))
                          (common-val? t t2))]
    [(_ (Dep x t p)) (and (not (contradiction? p))
                          (common-val? t1 t))]
    [(_ _) #f]))

(: type-conflict? (Type Type -> Boolean))
(define (type-conflict? t1 t2)
  (not (common-val? t1 t2)))

(: update (Type Boolean Type Path -> Type))
(define (update old b new π)
  (let update ([old old]
               [b b]
               [new new]
               [π (reverse π)])
    (match* (old b π)
      [((Pair τ σ) b (cons 'CAR rest)) (Pair (update τ b new rest) σ)]
      [(_ b (cons 'CAR rest)) 
       (if (subtype? (Pair (Top) (Top)) old)
           (Pair (update (Top) b new rest) (Top))
           (Bot))]
      [((Pair τ σ) b (cons 'CDR rest)) (Pair τ (update σ b new rest))]
      [(_ b (cons 'CDR rest)) 
       (if (subtype? (Pair (Top) (Top)) old)
           (Pair (Top) (update (Top) b new rest))
           (Bot))]
      [(t #t '()) (restrict t new)]
      [(t #f '()) (remove t new)])))

(: restrict (Type Type -> Type))
(define (restrict t1 t2)
  (match* (t1 t2)
   [(_ _) #:when (not (common-val? t1 t2)) (Bot)]
   [((Union ts) _) (reduce-Union (Union (map (λ ([t : Type]) 
                                               (restrict t t2)) 
                                             ts)))]
   [(_ _) #:when (subtype? t1 t2) t1]
   [((Dep x tx Px) (Dep y ty Py))
    (Dep x (restrict tx ty) (And: Px 
                                  (p_ Py [(var x) / y])))]
   [(_ (Dep y ty Py))
    (Dep y (restrict t1 ty) Py)]
   [((Dep x tx Px) _)
    (Dep x (restrict tx t2) Px)]
   [(_ _) t2]))

(: remove (Type Type -> Type))
(define (remove t1 t2)
  (match* (t1 t2)
    [(_ _) #:when (subtype? t1 t2) (Bot)]
    [((Union ts) _) (reduce-Union (Union (map (λ ([t : Type]) 
                                                (remove t t2)) 
                                              ts)))]
    [(τ (Dep x σ P)) #:when (subtype? τ σ)
                     (Dep x τ (¬ P))]
    [(_ _) t1]))

;; subtyping tests
(chk (subtype? (Int) (Top)))
(chk (subtype? (Bot) (Int)))
(chk~ (subtype? (Top) (Str)))
(chk (subtype? (Int) (Int)))
(chk~ (subtype? (Int) (Str)))
(chk (subtype? (Int) (U: (Int) (Str))))
(chk~ (subtype? (Top) (U: (Int) (Str))))
(chk~ (subtype? (U: (Int) (Str)) (Int)))
(chk (subtype? (U: (Int) (Str)) (Top)))
(chk~ (subtype? (U: (Int) (Str))
                (U: (Abs 'x (Int) (Int) (TT) (FF) #f) 
                    (Pair (Top) (Top)))))
(chk (subtype? (Pair (Int) (Str))
               (Pair (U: (Str) (Int))
                     (U: (Str) (Int)))))
(chk~ (subtype? (Pair (U: (Str) (Int))
                      (U: (Str) (Int)))
                (Pair (Int) (Str))))
(chk~ (subtype? (Abs 'x 
                     (U: (Str) (Int)) 
                     (U: (Str) (Int)) 
                     (TT) (FF) 
                     #f)
                (Abs 'x (Int) (Int) (TT) (FF) (var 'x))))
(chk (subtype? (Abs 'x (U: (Str) (Int)) (Int) (TT) (FF) (var 'x))
               (Abs 'x (Int) (U: (Str) (Int)) (TT) (TT) #f)))
(chk (subtype? (Dep 'x (Int) (FF)) (Int)))
(chk (subtype? (Int) (Dep 'x (Int) (TT))))
(chk (subtype? (Dep 'x (Int) (Atom #t (var 'y) (Int))) 
               (Dep 'x (U: (Int) (Str)) (TT))))
(chk (subtype? (Dep 'x (Int) (≤ (lexp `(1 ,(var 'x))) 
                                (lexp 42))) 
               (Dep 'x (Int) (≤ (lexp `(1 ,(var 'x))) 
                                (lexp 100)))))
(chk (subtype? (Dep 'x (Int) (≤ (lexp 30) 
                                (lexp `(1 ,(var 'x))) 
                                (lexp 42)))
               (Dep 'x (Int) (≤ (lexp `(1 ,(var 'x))) 
                                (lexp 100)))))
(chk~ (subtype? (Dep 'x (Int) (≤ (lexp 30) 
                                 (lexp `(1 ,(var 'x))) 
                                 (lexp 42))) 
                (Dep 'y (Int) (≤ (lexp `(1 ,(var 'y))) 
                                 (lexp 30)))))

;; Proof tests
(chk (proves? (env (list (And: (Is (var 'x) (Int)))))
              (Is (var 'x) (Int))))
(chk (proves? (env (list (And: (Is (var 'x) (U: (Int) (Str)))
                               (Or: (Is (var 'x) (U: (Int) (Bool)))
                                    (Is (var 'x) (U: (Int) (F) (Bot)))))))
              (Is (var 'x) (Int))))
(chk~ (proves? (env (list (And: (Is (var 'x) (U: (Int) (Str)))
                               (Or: (Is (var 'x) (U: (Int) (Bool)))
                                    (Is (var 'x) (U: (Int) (F) (Bot)))))))
              (Is (var 'x) (Str))))
(chk (proves? (env (list (And: (Is (var 'x) (Pair (Top) (U: (Str) (Bool))))
                               (Is (Obj '(CAR) 'x) (Int))
                               (Not (Obj '(CDR) 'x) (Bool)))))
              (Is (var 'x) (Pair (Int) (Str)))))
(chk (proves? (env (list (And: (Is (var 'x) (Pair (Top) (U: (Str) (Bool))))
                               (Is (Obj '(CAR) 'x) (Int))
                               (Not (Obj '(CDR) 'x) (Bool)))))
              (And: (Is (var 'x) (Pair (Int) (Str)))
                    (Is (var 'x) (Pair (U: (Int) (Str)) (Top))))))
(chk (proves? (env (list (Not (var 'x) (Int))
                         (Not (var 'x) (Str))))
              (Not (var 'x) (U: (Int) (Str)))))
(chk (proves? (env (list (Not (var 'x) (U: (Int) (Str) (Bool)))))
              (Not (var 'x) (U: (Int) (Str)))))
(chk~ (proves? (env (list (Not (var 'x) (U: (Int) (Str)))))
               (Not (var 'x) (U: (Int) (Str) (Bool)))))
(chk~ (proves? (env (list (Is (Obj '(CAR) 'x) (Int))))
               (FF)))
(chk~ (proves? (env (list (And: (Is (var 'x) (Pair (Top) (U: (Str) (Bool))))
                               (Is (Obj '(CAR) 'x) (Int))
                               (Not (Obj '(CDR) 'x) (Bool)))))
              (Is (var 'x) (Pair (Top) (Bool)))))
(chk (proves? (env (list (And: (Is (var 'x) (Dep 'v (Int) (≤ (lexp 1)
                                                             (lexp `(1 ,(var 'v))))))
                               (Is (var 'x) (Dep 'q (Int) (≤ (lexp `(2 ,(var 'q)))
                                                             (lexp 26)))))))
              (Is (var 'x) (Dep 'v (Int) (≤ (lexp 1)
                                            (lexp `(1 ,(var 'v)))
                                            (lexp 13))))))



;;               Or      And     atoms
;; (define-type Conj (Listof (U Atom Leq TT FF)))
;; (define-type DNF (Listof Conj))

;; (: Prop->DNF (Prop -> DNF))
;; (define (Prop->DNF P)
;;   (define (DNFxDNF->DNF [A : DNF] [B : DNF]) : DNF
;;     (for*/list ([a : Conj A]
;;                 [b : Conj B]) : DNF
;;       (append a b)))
;;   (match P
;;     [(? Atom? a) `((,a))]
;;     [(? TT? a) `((,a))]
;;     [(? FF? a) `((,a))]
;;     [(? Leq? l) `((,l))]
;;     [(And '()) `((,(TT)))]
;;     [(And ps) (let ([dnf-ps (map Prop->DNF ps)])
;;                 (foldl DNFxDNF->DNF 
;;                        (first dnf-ps) 
;;                        (rest dnf-ps)))]
;;     [(Or ps) (apply append (map Prop->DNF ps))]))


(: reify-ref ((Opt Ref) -> Ref))
(define (reify-ref opt-r)
  (or opt-r (var (Local (gensym 'local)))))

(: α-vary (Type -> Type))
(define (α-vary t)
  (define αhash : (HashTable Local Local)
    (for/hash ([local : Local (filter Local? (fvs t))]) 
      : (HashTable Local Local)
      (values local (Local (gensym 'local)))))
    t)

#;(define TI TypeInfo)
#;(: typeof ((Listof Prop) Exp -> TypeInfo))
#;(define (typeof Γ e)
  (match e
    [()]))


;;; TODO I'm not sure how essential it is... but it might be the case
;;; that we want to combine SLIs in the same disjunct...?
                                        ;
                                        ;
                                        ;(: simplify (Prop ->p))
                                        ;(define (simplify p)
                                        ;  (let simplify ([E : Env (env empty)]
                                        ;                 [p : Prop p]) 
                                        ;    (match p
                                        ;    [(TT) p]
                                        ;    [(FF) p]
                                        ;    [(IsT x t) (if (proves? E (¬ p))
                                        ;                   (FF)
                                        ;                   p)]
                                        ;    [(NotT x t) (if (proves? E (¬ p))
                                        ;                    (FF)
                                        ;                    p)]
                                        ;    [(And p q) (And (simplify (env+P E q) p)
                                        ;                    (simplify (env+P E p) q))]
                                        ;    [(Or p q) (Or (simplify E p)
                                        ;                  (simplify E q))])))
                                        ;
                                        ;
                                        ;(module+ test
                                        ;  (chk (equal? (simplify (And (Or (IsT 'x (Int)) 
                                        ;                                         (IsT 'x (Union `(,(T) ,(F)))))
                                        ;                                     (NotT 'x (Int))))
                                        ;                      (And (Or (FF) 
                                        ;                               (IsT 'x (Union `(,(T) ,(F)))))
                                        ;                           (NotT 'x (Int))))))
                                        ;
                                        ;
                                        ;(: δt (Op -> Type))
                                        ;(define (δt op)
                                        ;  (match op
                                        ;    ['add1  
                                        ;     (Abs 'x (Int) (Int) 
                                        ;          (TT) (FF) (+: 1 (1 (var 'x))))]
                                        ;    ['zero? 
                                        ;     (Abs 'x (Int) (Bool) 
                                        ;          (== (+: 0) (+: (1 (var 'x)))) 
                                        ;          (!= (+: 0) (+: (1 (var 'x)))) 
                                        ;          #f)]
                                        ;    ['int?  
                                        ;     (Abs 'x (Top) (Bool) (IsT 'x (Int)) (NotT 'x (Int)) #f)]
                                        ;    ['str?  
                                        ;     (Abs 'x (Top) (Bool) (IsT 'x (Str)) (NotT 'x (Str)) #f)]
                                        ;    ['bool?  
                                        ;     (Abs 'x (Top) (Bool) (IsT 'x (Bool)) (NotT 'x (Bool)) #f)]
                                        ;    ['proc?  
                                        ;     (Abs 'x (Top) (Bool) 
                                        ;          (IsT 'x (Abs 'y (Bot) (Top) (TT) (TT) #f)) 
                                        ;          (NotT 'x (Abs 'y (Bot) (Top) (TT) (TT) #f)) 
                                        ;          #f)]
                                        ;    ['str-len?  
                                        ;     (Abs 'x (Str) (Int) (TT) (FF) #f)]
                                        ;    ['+  
                                        ;     (Abs 'x (Int) (Abs 'y (Int) (Int) (TT) (FF) (+: (1 (var 'x)) (1 (var 'y)))) 
                                        ;          (TT) (FF) #f)]
                                        ;    ['<=
                                        ;     (Abs 'x (Int) (Abs 'y (Int) (Bool) 
                                        ;                        (≤ (+: (1 (var 'x)))
                                        ;                           (+: (1 (var 'y))))
                                        ;                        (¬ (≤ (+: (1 (var 'x)))
                                        ;                              (+: (1 (var 'y)))))
                                        ;                        #f) 
                                        ;          (TT) (FF) #f)]
                                        ;    ['error
                                        ;     (Abs 'x (Str) (Bot) (FF) (FF) #f)]
                                        ;    ['cons?
                                        ;     (Abs 'x (Top) (Bool) (IsT 'x (Pair (Top) (Top))) (NotT 'x (Pair (Top) (Top))) #f)]))
                                        ;
;; add1 zero? int? str? bool? proc? 
;; str-len + error cons? car cdr
                                        ;
                                        ;(: oo-join ((Opt Obj) (Opt Obj) -> (Opt Obj)))
                                        ;(define (oo-join oo1 oo2)
                                        ;  (cond
                                        ;    [(or (not oo1)
                                        ;         (not oo1)
                                        ;         (not (equal? oo1 oo2)))
                                        ;     #f]
                                        ;    [else oo1]))
                                        ;
                                        ;(: t-join (Type Type -> Type))
                                        ;(define (t-join t1 t2)
                                        ;  (cond
                                        ;    [(subtype? t1 t2) t2]
                                        ;    [(subtype? t2 t1) t1]
                                        ;    [else (Union `(,t1 ,t2))]))
                                        ;
                                        ;
                                        ;(: typeof (Env Exp -> (Values Type Prop Prop (Opt Ref))))
                                        ;(define (typeof E exp)
                                        ;  (match exp
                                        ;    ;; T-Int
                                        ;    [(? exact-integer? n)
                                        ;     ;; -----------------
                                        ;     (values (Int) (TT) (FF) (+: n))]))





