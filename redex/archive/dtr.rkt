#lang typed/racket

(require rackunit mtest)

(require/typed fme
  [#:opaque LExp lexp?]
  [#:struct Leq ([lhs : LExp] [rhs : LExp])]
  [list->lexp (-> (Listof (U Integer (Tuple Integer Obj))) 
                  LExp)]
  [lexp->string (-> LExp (-> (U Ref False) String) String)]
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
  [leq->string (-> Leq (-> (U Ref False) String) String)]
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
  (syntax-rules (quote)
    [(_ (quote x)) (list 1 (var (quote x)))] ; var (implicit coef 1)
    [(_ (n (quote x))) (list n (var (quote x)))] ; var w/ coeff
    [(_ (n o)) (list n o)] ; object w/ coeff
    [(_ a) (let ([val a])
             (if (exact-integer? val)
                 val
                 (list 1 val)))]))

(define-syntax-rule (+: t ...)
  (list->lexp (list (term t) ...)))


(define-syntax leq
  (syntax-rules ()
    [(leq l1 l2) (Leq l1 l2)]
    [(leq l1 l2 l3) (And (Leq l1 l2) 
                         (Leq l2 l3))]
    [(leq l1 l2 l3 l4 ...) (And (Leq l1 l2) 
                                (leq l2 l3 l4 ...))]))

(define-syntax gt 
  (syntax-rules ()
    [(gt l1 l2) (¬ (leq l1 l2))]
    [(gt l1 l2 l3) (And (gt l1 l2)
                        (gt l2 l3))]))

(define-syntax-rule (eq l1 l2)
  (leq l1 l2 l1))

(define-syntax-rule (neq l1 l2)
  (¬ (eq l1 l2)))

(define-syntax-rule (U: t ...)
  (Union (list t ...)))

(define-syntax And:
  (syntax-rules ()
    [(_ p) p]
    [(_ p q ...) (And p
                      (And: q ...))]))

(define-syntax Or:
  (syntax-rules ()
    [(_ p) p]
    [(_ p q ...) (Or p
                     (Or: q ...))]))


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

(define-type Path (Listof (U 'CAR 'CDR 'LEN)))

(: pe->str (Any -> String))
(define (pe->str pe)
  (match pe
    ['CAR "a"]
    ['CDR "d"]
    ['LEN "L"]))

(: path->str (Path -> String))
(define (path->str p)
  (match p
    ['() ""]
    [pes (string-append "c" (apply string-append (map pe->str pes)) "r")]))

;; Objects
(define-type Var Symbol)
(define-predicate Var? Var)
(struct Local ([var : Symbol]))
(define-type Id (U Var Local))
(define-predicate Id? Id)

(struct: Obj ([path : Path] [id : Id]) #:transparent)
(define-type Ref (U Obj LExp))   ;; lexp  x   (Obj (car) lexp)
(define-predicate Ref? Ref)


(: id->str (Id -> String))
(define (id->str id)
  (if (Var? id)
      (symbol->string id)
      (symbol->string (Local-var id))))

(: ref->str ((Opt Ref) -> String))
(define (ref->str optr)
  (match optr
    [#f "Ø"] 
    [(Obj '() (? Id? x)) (id->str x)]
    [(Obj path (? Id? x)) (string-append "(" 
                                         (path->str path) 
                                         (id->str x) ")")]
    [(? lexp? l) (lexp->string l ref->str)]))


(define-type SLI (Listof Leq))
(define-predicate SLI? SLI)



(: var (-> Id Obj))
(define (var x)
  (Obj empty x))

(: len (-> Id Obj))
(define (len x)
  (Obj '(LEN) x))



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
(struct: Array ([type : Type]))
(struct: Dep ([var : Var] [type : Type] [prop : Prop]) #:transparent)
(define-type Type (U Top T F Int Str Union Abs Pair Dep Array))
(define-predicate Type? Type)

(: type->str (Type -> String))
(define (type->str t)
  (match t
    [(Top) "Top"]
    [(T) "T"]
    [(F) "F"]
    [(Int) "Int"]
    [(Str) "Str"]
    [(Union ts) (string-append "(U" (apply string-append 
                                           (map (λ ([t : Type]) : String
                                                  (string-append " " (type->str t))) 
                                                ts)) 
                               ")")]
    [(Abs x td tr p+ p- optr)
     (string-append "(" (symbol->string x)
                    " : " (type->str td)
                    " -> " (type->str tr)
                    "(" (prop->str p+) " | " (prop->str p-) ")"
                    "[" (ref->str optr) "])")]
    [(Pair t1 t2)
     (string-append "(" (type->str t1) " * " (type->str t2) ")")]
    [(Array t)
     (string-append "<" (type->str t) ">")]
    [(Dep x t p)
     (string-append "{" (symbol->string x)
                    " : " (type->str t) " | "
                    (prop->str p) "}")]))

;; Propositions

(struct: TT () #:transparent)
(struct: FF () #:transparent)
(struct: Atom  ([bool : Boolean] [ref : Ref] [type : Type]) #:transparent)
(struct: And ([lhs : Prop] [rhs : Prop]) #:transparent)
(struct: Or ([lhs : Prop] [rhs : Prop]) #:transparent)
(define-type Prop (U TT FF Atom And Or Leq))
(define-predicate Prop? Prop)

(: prop->str (Prop -> String))
(define (prop->str p)
  (match p
    [(TT) "TT"]
    [(FF) "FF"]
    [(Atom #t r t) (string-append "(" (ref->str r) " -: " (type->str t) ")")]
    [(Atom #f r t) (string-append "(" (ref->str r) " -! " (type->str t) ")")]
    [(And p q) (string-append "("  (prop->str p) " ⋀ " (prop->str q) ")")]
    [(Or p q) (string-append "("  (prop->str p) " ⋁ " (prop->str q) ")")]
    [(? Leq? l) (leq->string l ref->str)]))



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
(struct: Ann ([var : Var] [type : Type]) #:transparent)
(struct: App ([rator : Exp] [rand : Exp]) #:transparent)
(struct: Fun ([arg : Symbol] [arg-type : Type] [body : Exp]) #:transparent)
(struct: If ([test : Exp] [then : Exp] [else : Exp]) #:transparent)
(struct: Let ([var : Symbol] [var-exp : Exp] [body : Exp]) #:transparent)
(struct: Cons ([car : Exp] [cdr : Exp]))
(struct: Vec ([exps : (Listof Exp)]))
(define-type Op (U 'add1 'zero? 'int? 'str? 'bool? 'proc? 
                   'str-len '+ 'double 'modulo 'error 'cons? 
                   'car 'cdr '<= 'ref))
(define-predicate Op? Op)

(define-type Val (U Integer String Boolean Op))
(define-predicate Val? Val)
(define-type Exp (U Val Ann App Fun If Let Cons Vec))
(define-predicate Exp? Exp)

(: exp->str (Exp -> String))
(define (exp->str e)
  (match e
    [(? Val? v) (format "~a" v)]
    [(Ann x t) (format "(~a : ~a)" x (type->str t))]
    [(App e1 e2) (string-append "(" (exp->str e1) " " (exp->str e2) ")")]
    [(Fun x t body) (string-append "(λ ([" (symbol->string x) " : " 
                                   (type->str t) "]) " (exp->str body) ")")]
    [(If e1 e2 e3) (string-append "(if " (exp->str e1) " " 
                                  (exp->str e2) " " 
                                  (exp->str e3) ")")]
    [(Let x xval body) (string-append "(let ([" (symbol->string x)
                                      " " (exp->str xval) "]) "
                                      (exp->str body) ")")]
    [(Vec exps) (string-append "(vec" (apply string-append (map (λ ([e : Exp])
                                                                  (string-append " " (exp->str e)))
                                                                exps))
                               ")")]))




(: Is (Ref Type -> Atom))
(define (Is ref type)
  (Atom #t ref type))

(: Not (Ref Type -> Atom))
(define (Not ref type)
  (Atom #f ref type))


(struct TypeInfo ([type : Type] 
                  [prop+ : Prop]
                  [prop- : Prop]
                  [oref : (Opt Ref)]) #:transparent)

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
    [(And p q) (Or (¬ p) (¬ q))]
    [(Or p q) (And (¬ p) (¬ q))]
    ;; empty SLI
    [(? Leq? l) (leq-negate l)]
    [else (error '¬ "unknown prop ~a" p)]))

(: contains-Bot? (Type -> Boolean))
(define (contains-Bot? t)
  (match t
    [(Union '()) #t]
    [(Pair lhs rhs) (or (contains-Bot? lhs)
                        (contains-Bot? rhs))]
    [(Array vt) (contains-Bot? vt)]
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
    [(Array t) (fvs t)]
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
    [(Or p q) (append (fvs p) (fvs q))]
    [(And p q) (append (fvs p) (fvs q))]
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
     (subst-lexp-in-lexp l1 l2 x)]
    [(_ _ _) (error 'subst-in-opt-ref "invalid args ~a ~a ~a" ref new x)]))


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
    [((And p q) new x) (And (p_ p [new / x]) (p_ q [new / x]))]
    [((Or p q) new x) (Or (p_ p [new / x]) (p_ q [new / x]))]
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
    [(Array vt) (Array (t_ vt [new / x]))]
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
              (p_ p [new / x])))]
    [else (error 'subst-in-type "invalid arg ~a" t)]))

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
  (hash-set imap r (cons t (hash-ref imap r (thunk '())))))


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
    ;; S-UnionSub
    [((Union ts) _) (andmap (curry supertype? t2) ts)]
    ;; S-UnionSuper
    [(_ (Union ts)) (ormap (curry subtype? t1) ts)]
    ;; S-Pair
    [((Pair t1l t1r) (Pair t2l t2r)) (and (subtype? t1l t2l)
                                          (subtype? t1r t2r))]
    ;; S-Array
    [((Vec vt1) (Vec vt2)) (subtype? vt1 vt2)]
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
       (lexp-equal? l (+: o))))

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
    [(_ (And p q)) (and (proves? E p)
                        (proves? E q))]
    ;; L-OrI
    [(_ (Or p q)) (or (proves? E p)
                      (proves? E q))]
    ;; L-DepI
    [(_ (Atom #t x (Dep v t p))) (and (proves? E (Is x t))
                                      (proves? E (p_ p [x / v])))]
    ;; L-False
    [((Env (cons (FF) ps) ts+ ts- sli) _) #t]
    ;; L-TTSkip
    [((Env (cons (TT) ps) ts+ ts- sli) _) 
     (proves? (Env ps ts+ ts- sli) goal)]
    ;; L-IsDepE
    [((Env (cons (Atom #t r (Dep v t p)) ps) ts+ ts- sli) _) 
     (proves? (Env (cons (And (Is r t) 
                              (p_ p [r / v])) 
                         ps)
                   ts+ ts- sli) goal)]
    ;; L-NotDepE
    [((Env (cons (Atom #f r (Dep v t p)) ps) ts+ ts- sli) _) 
     (proves? (Env (cons (¬ (And (Is r t) 
                                 (p_ p [r / v]))) 
                         ps)
                   ts+ ts- sli) goal)]
    ;; L-AndE
    [((Env (cons (And p q) ps) ts+ ts- sli) _) 
     (proves? (Env (cons p (cons q ps)) ts+ ts- sli) goal)]
    ;; L-OrE
    [((Env (cons (Or p q) ps) ts+ ts- sli) _) 
     (and (proves? (Env (cons p ps) ts+ ts- sli) goal)
          (proves? (Env (cons q ps) ts+ ts- sli) goal))]
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
                  (app (cons sli (gen-type-atoms (update-with-type-negations ts+ ts-)))
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
    [((Vec vt1) (Vec vt2)) (common-val? vt1 vt2)]
    [((? Abs?) (? Abs?)) #t]
    [((Dep x1 t1 p1) (Dep x2 t2 p2)) 
     (and (not (contradiction? (And p1 (p_ p2 [(var x1) / x2]))))
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
      [((Array τ) b '(LEN)) (Array τ)]
      [(_ b '(LEN))
       (if (subtype? (Array (Top)) old)
           (Array (Top))
           (Bot))]
      [(_ _ (cons x xs)) (Bot)]
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
(chk (subtype? (Dep 'x (Int) (leq (+: 'x) 
                                  (+: 42))) 
               (Dep 'x (Int) (leq (+: 'x) 
                                  (+: 100)))))
(chk (subtype? (Dep 'x (Int) (leq (+: 30) 
                                  (+: 'x) 
                                  (+: 42)))
               (Dep 'x (Int) (leq (+: 'x) 
                                  (+: 100)))))
(chk~ (subtype? (Dep 'x (Int) (leq (+: 30) 
                                   (+: 'x) 
                                   (+: 42))) 
                (Dep 'y (Int) (leq (+: 'y) 
                                   (+: 30)))))

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
(chk (proves? (env (list (And: (Is (var 'x) (Dep 'v (Int) (leq (+: 1)
                                                               (+: 'v))))
                               (Is (var 'x) (Dep 'q (Int) (leq (+: (2 'q))
                                                               (+: 26)))))))
              (Is (var 'x) (Dep 'v (Int) (leq (+: 1)
                                              (+: 'v)
                                              (+: 13))))))


(: reify-ref ((Opt Ref) -> Ref))
(define (reify-ref opt-r)
  (or opt-r (var (Local (gensym 'local)))))

(: α-vary (Type -> Type))
(define (α-vary t)
  (define αhash : (HashTable Local Local)
    (for/hash ([local : Local (filter Local? (fvs t))]) 
      : (HashTable Local Local)
      (values local (Local (gensym 'local)))))
  (for/fold ([t : Type t])
            ([local : Local (hash-keys αhash)])
    (let ([new-local : Local (hash-ref αhash local)])
      (t_ t [(var new-local) / local]))))

(: δt ((U Op Val) -> Type))
(define (δt a)
  (match a
    [(? exact-integer? n) (Dep 'v (Int) (eq (+: 'v) (+: n)))]
    [(? string? s) (Str)]
    [#t (T)]
    [#f (F)]
    ['add1 
     (Abs 'x (Int) (Dep 'v (Int) (eq (+: 1 'x)
                                     (+: 'v))) 
          (TT) (FF) 
          (+: 1 'x))]
    ['zero? 
     (Abs 'x (Int) (Bool) 
          (Is (var 'x) (Dep 'v (Int) (eq (+: 0) (+: 'v)))) 
          (Is (var 'x) (Dep 'v (Int) (neq (+: 0) (+: 'v)))) 
          #f)]
    ['int?  
     (Abs 'x (Top) (Bool) 
          (Is (var 'x) (Int)) 
          (Not (var 'x) (Int)) 
          #f)]
    ['str?  
     (Abs 'x (Top) (Bool) 
          (Is (var 'x) (Str)) 
          (Not (var 'x) (Str)) 
          #f)]
    ['bool?  
     (Abs 'x (Top) (Bool) 
          (Is (var 'x) (Bool)) 
          (Not (var 'x) (Bool)) 
          #f)]
    ['proc?  
     (Abs 'x (Top) (Bool) 
          (Is (var 'x) (Abs 'y (Bot) (Top) (TT) (TT) #f)) 
          (Not (var 'x) (Abs 'y (Bot) (Top) (TT) (TT) #f)) 
          #f)]
    ['str-len
     (Abs 'x (Str) (Int) (TT) (FF) #f)]
    ['+  
     (Abs 'x (Int) (Abs 'y (Int) (Dep 'v (Int) (eq (+: 'v)
                                                   (+: 'x 'y)))
                        (TT) (FF)
                        (+: 'x 'y)) 
          (TT) (FF) 
          #f)]
    ['double
     (Abs 'x (Int) (Dep 'v (Int) (eq (+: 'v)
                                     (+: (2 'x)))) 
          (TT) (FF)
          (+: (2 (var 'x))))]
    ['modulo
     (Abs 'n (Int) (Abs 'x (Int) (Dep 'v (Int) (leq (+: 0)
                                                    (+: 'v)
                                                    (+: 'n -1)))
                        (TT) (FF)
                        #f)
          (TT) (FF)
          #f)]
    ['<=
     (Abs 'x (Int) (Abs 'y (Int) (Bool) 
                        (Is (var 'x) (Dep 'v (Int) (leq (+: 'v)
                                                        (+: 'y))))
                        (Is (var 'x) (Dep 'v (Int) (¬ (leq (+: 'v)
                                                           (+: 'y)))))
                        #f) 
          (TT) (FF) #f)]
    ['error
     (Abs 'x (Str) (Bot) (FF) (FF) #f)]
    ['cons?
     (Abs 'x (Top) (Bool) 
          (Is (var 'x) (Pair (Top) (Top))) 
          (Not (var 'x) (Pair (Top) (Top))) #f)]))



(: ref-join ((Opt Ref) (Opt Ref) -> (Opt Ref)))
(define (ref-join r1 r2)
  (cond
   [(or (not r1)
        (not r2)
        (not (ref-equiv? r1 r2)))
    #f]
   [else r1]))

(: t-join (Type Type -> Type))
(define (t-join t1 t2)
  (cond
   [(subtype? t1 t2) t2]
   [(subtype? t2 t1) t1]
   [else (Union `(,t1 ,t2))]))


(: val->ref (Val -> (Opt Ref)))
(define (val->ref v)
  (match v
    [(? exact-integer? n) (+: n)]
    [else #f]))

(: val->prop (Val -> Prop))
(define (val->prop b)
  (if b (TT) (FF)))


(define TI TypeInfo)

(: typeof ((Listof Prop) Exp -> (Opt TypeInfo)))
(define (typeof Γ e)
  (match e
    ;; T-Const
    [(? (or Val? Op?) v) 
     (TI (δt v) (val->prop v) (val->prop (not v)) (val->ref v))]
    ;; T-AnnVar
    [(Ann x t)
     (let ([xprop (Is (var x) t)]) 
       (cond
        [(proves? (env Γ) xprop) 
         (TI t 
             (And: xprop (Not (var x) (F))) 
             (And: xprop (Is (var x) (F))) 
             (var x))]
        [else #f]))]
    ;; T-Fun
    [(Fun x dom body) 
     (let ([ti (typeof (cons (Is (var x) dom) Γ) body)])
       (match ti
         [(TypeInfo range P1+ P1- optr1)
          (TI (Abs x dom range P1+ P1- optr1) (TT) (FF) #f)] ; excluded P_x
         [#f #f]
         [_ (error 'typeof "invalid body typeinfo? ~a" ti)]))]
    ;; T-If
    [(If e1 e2 e3)
     (match (typeof Γ e1)
       [#f #f]
       [(TypeInfo t1 p1+ p1- _)
        (match* ((typeof (cons p1+ Γ) e2)
                 (typeof (cons p1- Γ) e3))
          [(#f _) #f]
          [(_ #f) #f]
          [((TypeInfo t2 p2+ p2- r2)
            (TypeInfo t3 p3+ p3- r3))
           (TI (t-join t2 t3) 
               (Or: (And: p1+ p2+)
                    (And: p1- p3+))
               (Or: (And: p1+ p2-)
                    (And: p1- p3-))
               (ref-join r2 r3))])])]
    ;; T-App
    [(App e1 e2) #:when (not (or (equal? e1 'car)
                                 (equal? e1 'cdr)))
     (match* ((typeof Γ e1)
              (typeof Γ e2))
       [(#f _) #f]
       [(_ #f) #f]
       [((TypeInfo (? Abs? fun-t) p1+ p1- optr1)
         (TypeInfo arg-t p2+ p2- optr2))
        (match-let ([(Abs x td tr pf+ pf- rf) (α-vary fun-t)]
                    [r2 (reify-ref optr2)])
          (if (subtype? arg-t td)
              (TI (t_ tr [r2 / x])
                  (p_ pf+ [r2 / x])
                  (p_ pf- [r2 / x])
                  (r_ rf [r2 / x]))
              #f))])]
    ;; T-Let
    [(Let x xval body)
     (match (typeof Γ xval)
       [#f #f]
       [(TypeInfo tx px+ px- optrx)
        (let ([plet (And (Is (var x) tx)
                         (Or (And (Not (var x) (F)) px+)
                             (And (Is (var x) (F)) px-)))])
          (match (typeof (cons plet Γ) body)
            [#f #f]
            [(TypeInfo t2 p2+ p2- optr2)
             (let ([rx (reify-ref optrx)]
                   [p+ (And p2+ plet)]
                   [p- (And p2- plet)])
               (TypeInfo (t_ t2 [rx / x])
                         (p_ p+ [rx / x])
                         (p_ p- [rx / x])
                         (r_ optr2 [rx / x])))]))])]
    ;; T-Cons
    [(Cons e1 e2)
     (match* ((typeof Γ e1) (typeof Γ e2))
     [(#f _) #f]
     [(_ #f) #f]
     [((TypeInfo t1 p1+ p1- optr1) 
       (TypeInfo t2 p2+ p2- optr2))
      (TI (Pair t1 t2) (TT) (FF) #f)])]
    ;; T-Car
    [(App 'car e1)
     (match (typeof Γ e1)
     [#f #f]
     [(TypeInfo (Pair t1 t2) p1+ p1- optr1)
      (let* ([r1 (reify-ref optr1)]
             [x (gensym 'x)]
             [o (Obj '(CAR) x)])
          (TI t1
              (p_ (Not o (F)) [r1 / x])
              (p_ (Is o (F)) [r1 / x])
              (r_ o [r1 / x])))]
     [_ #f])]
    ;; T-Cdr
    [(App 'cdr e1)
     (match (typeof Γ e1)
     [#f #f]
     [(TypeInfo (Pair t1 t2) p1+ p1- optr1)
      (let* ([r1 (reify-ref optr1)]
             [x (gensym 'x)]
             [o (Obj '(CDR) x)])
          (TI t2
              (p_ (Not o (F)) [r1 / x])
              (p_ (Is o (F)) [r1 / x])
              (r_ o [r1 / x])))]
     [_ #f])]
    ;; T-Vec
    [(Vec exps)
     (let ([tis (map (curry typeof Γ) exps)])
       (if (not (empty? (filter not tis)))
           #f
            (let ([t (foldl t-join (Top) (map TypeInfo-type 
                                              (filter TypeInfo? tis)))])
              (TI (Array t) (TT) (FF) #f))))]
    [else (error 'typeof "I don't know what that is, bro! ~a" e)]
    ;; T-Ref
    [(App 'ref e1)
     (match (typeof Γ e1)
       [(TypeInfo (Array t) _ _ optr1)
        ;; ? W/ substutition would this map the domain to Bot if null?
        (let ([r1 (reify-ref optr1)]
              [p+ (if (subtype? t (F)) (FF) (TT))]
              [p- (if (subtype? (F) t) (TT) (FF))])
          (TI (Abs 'x 
                   (t_ (Dep 'i (Int) (leq (+: 0)
                                          (+: 'i)
                                          (+: (1 (len 'v)) -1)))
                       [r1 / 'v])
                   t
                   p+ p-
                   #f)
              (TT) (FF) #f))]
       [_ #f])]))

(: chk-typeof ((Listof Prop) Exp (Opt TypeInfo) -> Boolean))
(define (chk-typeof Γ e ti)
  (match* (ti (typeof Γ e))
    [((TypeInfo et ep+ ep- eoptr) (TypeInfo t p+ p- optr)) 
     (cond
      [(not (subtype? t et))
       (printf "FAILURE:\nEnv: ~a\nTerm: ~a\n~a\nis not a subtype of:\n ~a)" 
               (apply string-append (map prop->str Γ)) 
               (exp->str e) 
               (type->str t) 
               (type->str et))
       #f]
      [(not (proves? (env (cons p+ Γ)) ep+))
       (printf "FAILURE:\nEnv: ~a\nTerm: ~a\n~a \ndoes not imply:\n ~a\n (Prop+)" 
               (apply string-append (map prop->str Γ)) 
               (exp->str e) 
               (prop->str p+) 
               (prop->str ep+))
       #f]
      [(not (proves? (env (cons p- Γ)) ep-))
       (printf "FAILURE:\nEnv: ~a\nTerm: ~a\n~a  \ndoes not imply:\n ~a\n (Prop-)" 
               (apply string-append (map prop->str Γ)) 
               (exp->str e)
               (prop->str p-) 
               (prop->str ep-))
       #f]
      [(not (subref? optr eoptr))
       (printf "FAILURE:\nEnv: ~a\nTerm: ~a\n~a  \nis not a subtype of:\n ~a\n" 
               (apply string-append (map prop->str Γ)) 
               (exp->str e)
               (ref->str optr) 
               (ref->str eoptr))
       #f]
      [else #t])]
    [((TypeInfo t p+ p- optr) #f)
     (printf "FAILURE:\nEnv: ~a\nTerm: ~a\nDid not typecheck!"
             (apply string-append (map prop->str Γ)) 
             (exp->str e))
     #f]
    [(#f (TypeInfo t p+ p- optr))
     (printf "FAILURE:\nEnv: ~a\nTerm: ~a\nDid typecheck! (Expected #f)" 
             (apply string-append (map prop->str Γ)) 
             (exp->str e))
     #f]
    [(#f #f) #t]))

(: chk-not-typeof ((Listof Prop) Exp TypeInfo -> Boolean))
(define (chk-not-typeof Γ e ti)
  (match* (ti (typeof Γ e))
    [((TypeInfo et ep+ ep- eoptr) (TypeInfo t p+ p- optr)) 
     (if (or (not (subtype? t et))
             (not (proves? (env (cons p+ Γ)) ep+))
             (not (proves? (env (cons p- Γ)) ep-))
             (not (subref? optr eoptr)))
         #t
         (begin (printf "FAILURE:\nEnv: ~a\nTerm: ~a\nWas not supposed to check as ~a ~a ~a ~a" 
                        (apply string-append (map prop->str Γ))
                        (exp->str e) 
                        (type->str (TypeInfo-type ti))
                        (prop->str (TypeInfo-prop+ ti))
                        (prop->str (TypeInfo-prop- ti))
                        (ref->str (TypeInfo-oref ti)))
                #f))]
    [((TypeInfo t p+ p- optr) #f)
     (printf "FAILURE:\nEnv: ~a\nTerm: ~a\nDid not typecheck!" 
             (apply string-append (map prop->str Γ)) 
             (exp->str e))
     #f]))

(define-syntax-rule (typeof? (p ...) exp ti)
  (chk-typeof (map parse-prop (list 'p ...))
              (parse-exp 'exp)
              ti))

(define-syntax-rule (not-typecheck? (p ...) exp)
  (typeof? (p ...) exp #f))

(define-syntax-rule (not-typeof? (p ...) exp ti)
  (chk-not-typeof (map parse-prop (list 'p ...))
                  (parse-exp 'exp)
                  ti))


(: parse-term (Any -> (U Integer (Tuple Integer Obj))))
(define (parse-term term)
  (match term
    [(? exact-integer? n) n]
    [(? symbol? x) (list 1 (var x))]
    [(list (? exact-integer? n) r)
     (let ([obj (parse-ref r)])
       (cond
        [(Obj? obj) (list n obj)]
        [else (error 'parse-term "unsupported term for parser: ~a" r)]))]))


(: parse-ref (Any -> Ref))
(define (parse-ref exp)
  (match exp
    [(? Var? v) (var v)]
    [`(car ,v) #:when (Var? v)
     (Obj '(CAR) v)]
    [`(cdr ,v) #:when (Var? v)
     (Obj '(CDR) v)]
    [`(cadr ,v) #:when (Var? v)
     (Obj '(CAR CDR) v)]
    [`(cddr ,v) #:when (Var? v)
     (Obj '(CDR CDR) v)]
    [`(caar ,v) #:when (Var? v)
     (Obj '(CAR CAR) v)]
    [`(cdar ,v) #:when (Var? v)
     (Obj '(CDR CAR) v)]
    [(cons '+: terms) 
     (list->lexp (map parse-term (cast terms (Listof Any))))]
    [else (error 'parse-ref "invalid exp ~a" exp)]))

(: parse-type (Any -> Type))
(define (parse-type exp)
  (match exp
    ['Top (Top)]
    ['Bot (Bot)]
    ['T (T)]
    ['F (F)]
    ['Int (Int)]
    ['Str (Str)]
    ['Bool (Bool)]
    [`(U . ,types) (let ([ts (map parse-type (cast types (Listof Any)))])
                     (Union ts))]
    [`(,t1 -> ,t2) #:when (subtype? (F) (parse-type t2))
     (Abs 'x (parse-type t1) (parse-type t2) (TT) (TT) #f)]
    [`(,t1 -> ,t2) #:when (not (subtype? (F) (parse-type t2)))
     (Abs 'x (parse-type t1) (parse-type t2) (TT) (FF) #f)]
    [`(,x : ,t1 -> ,t2 (,p1 ,p2))
     (Abs (cast x Symbol) (parse-type t1) (parse-type t2) 
          (parse-prop p1) (parse-prop p2) #f)]
    [`(,x : ,t1 -> ,t2 (,p1 ,p2 ,r))
     (Abs (cast x Symbol) (parse-type t1) (parse-type t2) 
          (parse-prop p1) (parse-prop p2) (parse-ref r))]
    [`(,t1 * ,t2) (Pair (parse-type t1) (parse-type t2))]
    [`(,x : ,t where ,p) (Dep (cast x Symbol) (parse-type t) (parse-prop p))]
    [else (error 'parse-type "unknown type: ~a" exp)]))


(: parse-prop (Any -> Prop))
(define (parse-prop exp)
  (match exp
    ['TT (TT)]
    ['FF (FF)]
    [`(,r -: ,t) (Atom #t (parse-ref r) (parse-type t))]
    [`(,r -! ,t) (Atom #f (parse-ref r) (parse-type t))]
    [`(And ,p ,q) 
     (And (parse-prop p) (parse-prop q))]
    [`(Or ,p ,q) 
     (Or (parse-prop p) (parse-prop q))]
    [`(<= ,l1 ,l2)
     (Leq (cast (parse-ref l1) LExp) (cast (parse-ref l2) LExp))]
    [else (error 'parse-prop "unknown prop: ~a" exp)]))


(: parse-exp (Any -> Exp))
(define (parse-exp exp)
  (match exp
    [(? Val? v) v]
    [`(,x : ,t) (Ann (cast x Symbol) (parse-type t))]
    [`(λ ([,x : ,t]) ,body) 
     (Fun (cast x Symbol) (parse-type t) (parse-exp body))]
    [`(if ,e1 ,e2 ,e3) (If (parse-exp e1) (parse-exp e2) (parse-exp e3))]
    [`(let ([,x ,xval]) ,body) (Let (cast x Symbol) (parse-exp xval) (parse-exp body))]
    [`(let ([,x ,xval]
            [,y ,yval]) 
       ,body)
     (Let (cast x Symbol) (parse-exp xval) 
          (Let (cast y Symbol) (parse-exp yval) (parse-exp body)))]
     [`(cons ,e1 ,e2) (Cons (parse-exp e1) (parse-exp e2))]
    [`(or ,e1 ,e2) (Let 'tmp (parse-exp e1) (If (Ann 'tmp (Top)) 
                                                (Ann 'tmp (T))
                                                (parse-exp e2)))]
    [`(and ,e1 ,e2) (If (parse-exp e1) 
                        (parse-exp e2)
                        #f)]
    [`(,e1 ,e2) (App (parse-exp e1) (parse-exp e2))]
    [`(,e1 ,e2 ,e3) (App (App (parse-exp e1) (parse-exp e2)) (parse-exp e3))]
    [else (error 'parse-exp "invalid exp ~a" exp)]))

;; Constants
(chk (typeof? [] 5 
              (TI (Int) (TT) (FF) (+: 5))))

(chk (typeof? [] "Hello World!"
              (TI (Str) (TT) (FF) #f)))

(chk (typeof? [] #t 
              (TI (T) (TT) (FF) #f)))

(chk (typeof? [] #f 
              (TI (F) (FF) (TT) #f)))

(chk (typeof? [(x -: Int)] 
              (x : Int)
              (TI (Int) (TT) (FF) #f)))

(chk (typeof? [(x -: Int)] 
              (x : Top) 
              (TI (Top) (TT) (FF) #f)))

(chk (not-typecheck? [(x -: Int)] 
                     (x : Str)))


;; ****************************************
;; Functions

;; simple function and function subtyping
(chk (typeof? [] 
              (λ ([x : Int]) (x : Int)) 
              (TI (Abs 'x (Int) (Int) (TT) (FF) (var 'x))
                  (TT) (FF) #f)))

(chk (typeof? []
              (λ ([x : Int]) (x : Int))
              (TI (Abs 'x (Bot) (Top) (TT) (FF) (var 'x))
                  (TT) (FF) #f)))

(chk (not-typeof? []
                  (λ ([x : Int]) (x : Int))
                  (TI (Abs 'x (Top) (Int) (TT) (FF) (var 'x))
                      (TT) (FF) #f)))

;; add1 adds exactly 1
(chk (typeof? [] add1 
              (TI (Abs 'x (Int) (Dep 'v (Int) (eq (+: 1 'x) ; 
                                                  (+: 'v))) 
                       (TT) (FF) 
                       (+: 1 'x)) 
                  (TT) (FF) #f)))

;; add1 produces a larger value
(chk (typeof? [] add1 
              (TI (Abs 'x (Int) (Dep 'v (Int) (gt (+: 'v)
                                                  (+: 'x)))
                       (TT) (FF) 
                       (+: 1 'x)) 
                  (TT) (FF) #f)))


(chk (typeof? [] 
              (λ ([x : Int]) (+ 1 (x : Int))) 
              (TI (Abs 'x (Int) (Dep 'v (Int) (eq (+: 1 'x)
                                                  (+: 'v))) 
                       (TT) (FF) (+: 1 'x))
                  (TT) (FF) #f)))


;; ICFP '10 Examples

;; Example 1
(chk (typeof? [(x -: Int)]
              (if (int? (x : Top))
                  (add1 (x : Int))
                  0)
              (TI (Int) (TT) (FF) #f)))

;; Example 2
(chk (typeof? []
              (λ ([x : (U Str Int)])
                (if (int? (x : Top)) 
                    (add1 (x : Int)) 
                    (str-len (x : Str))))
              (TI (Abs 'x (U: (Str) (Int)) (Int) (TT) (FF) #f)
                  (TT) (FF) #f)))

;; Example 3
(chk (typeof? [(x -: (U Str F))]
              (if (x : Top)
                  (str-len (x : Str))
                  (error "string not found!"))
              (TI (Int) (TT) (FF) #f)))

;; Example 4
(chk (typeof? [(f -: ((U Int Str) -> Int))
               (x -: Top)]
              (if (or (int? (x : Top)) (str? (x : Top)))
                  ((f : ((U Int Str) -> Int)) (x : (U Int Str)))
                  0)
              (TI (Int) (TT) (FF) #f)))

;; Example 5
(chk (typeof? [(x -: Top)
               (y -: Top)]
              (if (and (int? (x : Top)) (str? (y : Top)))
                  (+ (x : Int) (str-len (y : Str)))
                  0)
              (TI (Int) (TT) (FF) #f)))


;; Example 6
(chk (not-typecheck? [(x -: (U Str Int)) (y -: Top)]
                     (if (and (int? (x : Top)) (str? (y : Top)))
                         (+ (x : Int) (str-len (y : Str)))
                         (str-len (x : Str)))))


;; Example 7 (see example 6)

;; Example 8
(chk (typeof? []
              (λ ([x : Top])
                (or (int? (x : Top)) (str? (x : Top))))
              (TI (Abs 'x (Top) (Bool) 
                       (Is (var 'x) (U: (Str) (Int))) 
                       (Not (var 'x) (U: (Str) (Int))) 
                       #f)
                  (TT) (FF) #f)))


;; Example 9 (see example 5)

;; Example 10
(chk (typeof? [(p -: (Top * Top))]
              (if (int? (car (p : (Top * Top))))
                  (add1 (car (p : (Int * Top))))
                  42)
              (TI (Int) (TT) (FF) #f)))

(chk (typeof? [(p -: (Top * Top))]
              (if (int? (cdr (p : (Top * Top))))
                  (add1 (cdr (p : (Top * Int))))
                  42)
              (TI (Int) (TT) (FF) #f)))


;; Example 11
(chk (typeof? [(g -: ((Int * Int) -> Int))
               (p -: (Top * Top))]
              (if (and (int? (car (p : (Top * Top))))
                       (int? (cdr (p : (Int * Top)))))
                  ((g : ((Int * Int) -> Int)) (p : (Int * Int)))
                  42)
              (TI (Int) (TT) (FF) #f)))

;; Example 12
(chk (typeof? []
              (λ ([p : (Top * Top)])
                (int? (car (p : (Top * Top))))) 
              (TI (Abs 'p (Pair (Top) (Top)) (Bool)
                       (Is  (Obj '(CAR) 'p) (Int))
                       (Not (Obj '(CAR) 'p) (Int))
                       #f)
                  (TT) (FF) 
                  #f)))

;; Example 13
(chk (typeof? [(x -: Top) (y -: (U Int Str))]
              (if (and (int? (x : Top)) (str? (y : Top)))
                  (+ (x : Int) (str-len (y : Str))) 
                  (if (int? (x : Top))
                      (+ (x : Int) (y : Int))
                      0))
              (TI (Int) (TT) (FF) #f)))

;; Example 14
(chk (typeof? [(x -: Top)]
              (λ ([y : (U Int Str)])
                (if (and (int? (x : Top)) (str? (y : Top))) 
                    (+ (x : Int) (str-len (y : Str))) 
                    (if (int? (x : Top))
                        (+ (x : Int) (y : Int))
                        0)))
              (TI (Abs 'x (U: (Str) (Int)) (Int) (TT) (FF) #f)
                  (TT) (FF) #f)))




