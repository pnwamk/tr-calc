#lang typed/racket

(require/typed fme
               [#:opaque LExp lexp?]
               [#:struct leq ([lhs : LExp] [rhs : LExp])]
               [lexp (->* ((U Integer (Tuple Integer Obj))) 
                          #:rest (U Integer (Tuple Integer Obj)) 
                          LExp)]
               [lexp-coefficient (-> LExp Obj Integer)]
               [lexp-constant (-> LExp Integer)]
               [lexp-vars (-> LExp (Listof Obj))]
               [lexp-scale (-> LExp Integer LExp)]
               [lexp-zero? (-> LExp Boolean)]
               [lexp-subtract (-> LExp LExp LExp)]
               [lexp-add (-> LExp LExp LExp)]
               [lexp-has-var? (-> LExp Obj Boolean)]
               [lexp-add1 (-> LExp LExp)]
               [lexp-subst (-> LExp Obj Obj LExp)]
               [leq-contains-var? (-> leq Obj Boolean)]
               [leq-subst (-> leq Obj Obj leq)]
               [leq-negate (-> leq leq)]
               [sli-vars (-> SLI (Listof Obj))]
               [sli-subst (-> SLI Obj Obj SLI)]
               [sli-elim-var (-> SLI Obj SLI)]
               [sli-satisfiable? (-> SLI Boolean)]
               [sli-proves-leq? (-> SLI leq Boolean)]
               [sli-proves-sli? (-> SLI SLI Boolean)])

(define-syntax-rule (check-true exp)
  (if exp
      (void)
      (error "check failed!" (quote exp))))

(define-syntax-rule (check-false exp)
  (if exp
      (error "check failed!" (quote exp))
      (void)))


(: hash-empty? (All (a b) (case-> (-> (HashTable a b) Boolean) 
                                  (-> HashTableTop Boolean))))
(define (hash-empty? h)
  (zero? (hash-count h)))
;;*****************************************                              
;; λDTR Definition
;;*****************************************
(define prim-ops '(add1 zero? int? str? bool? proc? 
                       str-len + error cons? car cdr))

(define-type Path (Listof (U 'CAR 'CDR)))

;; Objects
(define-type Var Symbol)
(: Var? (Any . -> . Boolean : Var))
(define Var? symbol?)

(struct: Obj ([path : Path] [var : Var]) #:transparent)
(define-type Ref (U Obj LExp))
(define-type SLI (Listof leq))

(: SLI? (pred SLI))
(define (SLI? a)
  (and (list? a)
       (andmap leq? a)))

(: var (-> Var Obj))
(define (var x)
  (Obj empty x))

;; Expressions
(struct: Ann ([exp : (U Symbol Exp)] [type : Type]) #:transparent)
(struct: App ([rator : Exp] [rand : Exp]) #:transparent)
(struct: Fun ([arg : Symbol] [arg-type : Type] [body : Exp]) #:transparent)
(struct: If ([test : Exp] [then : Exp] [else : Exp]) #:transparent)
(struct: Let ([var : Symbol] [var-exp : Exp] [body : Exp]) #:transparent)
(struct: Op ([name : Symbol]) #:transparent
  #:guard (λ (n _)
            (unless (member n prim-ops)
              (error "invalid Op ~a" n))
            n))
(define-type Val (U Integer String Boolean))
(define-type Exp (U Val Ann App Fun If Let))

(: Val? (-> Any Boolean : Val))
(define (Val? a)
  (or (exact-integer? a)
      (string? a)
      (boolean? a)))

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
              [obj : (Opt Obj)]) #:transparent)
(struct: Pair ([car : Type] [cdr : Type]) #:transparent)
(struct: Dep ([var : Var] [type : Type] [prop : Prop]) #:transparent)
(define-type Type (U Top T F Int Str Union Abs Pair Dep))

;; Propositions
(struct: TT () #:transparent)
(struct: FF () #:transparent)
(struct: IsT ([var : Var] [type : Type]) #:transparent)
(struct: NotT ([var : Var] [type : Type]) #:transparent)
(struct: And ([lhs : Prop] [rhs : Prop]) #:transparent)
(struct: Or ([lhs : Prop] [rhs : Prop]) #:transparent)
(define-type Prop (U TT FF IsT NotT And Or SLI))

(: Prop? (Any . -> . Boolean : Prop))
(define (Prop? a)
  (or (TT? a)
      (FF? a)
      (IsT? a)
      (NotT? a)
      (And? a)
      (Or? a)
      (SLI? a)))

(define (Bool)
  (Union (list (T) (F))))
(: Bool? (Any . -> . Boolean))
(define (Bool? a)
  (and (Union? a)
       (let ([ts (Union-types a)])
        (or (equal? (list (T) (F)) ts)
            (equal? (list (F) (T)) ts)))))


(define (Bot)
  (Union empty))
(: Bot? (Any . -> . Boolean))
(define (Bot? a)
  (and (Union? a)
       (empty? (Union-types a))))

;; Environments
(define-type TMap (HashTable Var (Listof Type)))
(define-type NTMap (HashTable Var Type))

(define-type Opt Option)
(struct: Env ([props : (Listof Prop)] 
              [types+ : TMap]
              [types- : NTMap]
              [sli : SLI]))

(: env ((Listof Prop) . -> . Env))
(define (env lop)
  (Env lop (hash) (hash) empty))

;;*****************************************
;; λDTR Helpers
;;*****************************************
(: ¬ (Prop . -> . Prop))
(define (¬ p)
  (match p
    [(TT) (FF)]
    [(FF) (TT)]
    [(IsT x t) (NotT x t)]
    [(NotT x t) (IsT x t)]
    [(And p q) (Or (¬ p) (¬ q))]
    [(Or p q) (And (¬ p) (¬ q))]
    ;; empty SLI
    ['() (FF)]
    ;; SLI of 1
    [(cons leq1 '()) (list (leq-negate leq1))]
    ;; SLI > 1
    [(cons leq1 leqs) (Or (list (leq-negate leq1))
                          (¬ leqs))]))
; option-l

(: contains-Bot? (Type -> Boolean))
(define (contains-Bot? t)
  (match t
    [(Union '()) #t]
    [(Pair lhs rhs) (or (contains-Bot? lhs)
                        (contains-Bot? rhs))]
    [_ #f]))

(module+ test
  (check-true (contains-Bot? (Bot)))
  (check-true (contains-Bot? (Pair (Top) (Bot))))
  (check-true (contains-Bot? (Pair (Pair (Bot) (Top)) (Top))))
  (check-false (contains-Bot? (Union `(,(Int) ,(Bot) ,(Str))))))

(: fvs ((U (Opt Obj) Type Prop) . -> . (Listof Var)))
(define (fvs e)
  (match e
    ;; Objects
    [#f empty]
    [(Obj _ x) (list x)]
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
    [(IsT x t) (cons x (fvs t))]
    [(NotT x t) (cons x (fvs t))]
    [(Or p1 p2) (append (fvs p1) (fvs p2))]
    [(And p1 p2) (append (fvs p1) (fvs p2))]
    [(? SLI? s) (map Obj-var (sli-vars s))]
    [else (error 'fvs "unknown argument ~a" e)]))


(: path-type-norm (Path Type . -> . Type))
(define (path-type-norm π t)
 (match π
   [`() t]
   [`(CAR . ,tl) (Pair (path-type-norm tl t) (Top))]
   [`(CDR . ,tl) (Pair (Top) (path-type-norm tl t))]))


(: subst (case-> [(Opt Obj) Var (Opt Obj) . -> . (Opt Obj)]
                 [Var Var (Opt Obj) . -> . (Opt Obj)]
                 [(Opt Obj) Var Prop . -> . Prop]
                 [Var Var Prop . -> . Prop]
                 [(Opt Obj) Var Type . -> . Type]
                 [Var Var Type . -> . Type]))
(define (subst new old-var tgt)
  (match* (new old-var tgt)
    [((? Var? x) y _) (subst (Obj '() x) y tgt)]
    ;; (Opt Obj)
    [(_ _ #f) #f]
    [(#f x (Obj _ x)) #f]
    [((Obj π2 x) y (Obj π1 y)) (Obj (append π1 π2) x)]
    [(_ x (Obj π1 y)) #:when (not (equal? x y)) (Obj π1 y)]
    ;; Type
    [(_ _ (Top)) (Top)]
    [(_ _ (Int)) (Int)]
    [(_ _ (Str)) (Str)]
    [(_ _ (T)) (T)]
    [(_ _ (F)) (F)]
    [(_ _ (Union ts)) 
     (Union (map (λ ([t : Type]) (subst new old-var t)) ts))]
    [(_ _ (Pair t1 t2)) 
     (Pair (subst new old-var t1) (subst new old-var t2))]
    [(_ x (Abs x td tr p+ p- oo)) 
     (Abs x (subst new x td) tr p+ p- oo)]
    [(_ x (Abs y td tr p+ p- oo)) #:when (not (equal? x y))
                                  (Abs y (subst new x td) 
                                       (subst new x tr) 
                                       (subst new x p+) 
                                       (subst new x p-) 
                                       (subst new x oo))]
    [(_ x (Dep x t p))
     (Dep x (subst new x t) p)]
    [(_ x (Dep y t p)) #:when (not (equal? x y))
                       (Dep y (subst new x t) p)]
    ;; Prop
    [(_ _ (TT)) (TT)]
    [(_ _ (FF)) (FF)]
    [(_ _ (And lhs rhs)) (And (subst new old-var lhs)
                              (subst new old-var rhs))]
    [(_ _ (Or lhs rhs)) (Or (subst new old-var lhs)
                            (subst new old-var rhs))]
    [((Obj π x) y (IsT y t)) (IsT x (path-type-norm π t))]
    [((Obj π x) y (NotT y t)) (NotT x (path-type-norm π t))]
    [(#f y (IsT y t)) (TT)]
    [(#f y (NotT y t)) (TT)]
    [(_ x (IsT y t)) #:when (and (not (equal? x y))
                                 (not (member x (fvs t))))
                     (IsT y t)]
    [(_ x (NotT y t)) #:when (and (not (equal? x y))
                                  (not (member x (fvs t))))
                     (NotT y t)]
    [(_ x (IsT y t)) #:when (and (not (equal? x y))
                                 (member x (fvs t)))
                     (TT)]
    [(_ x (NotT y t)) #:when (and (not (equal? x y))
                                 (member x (fvs t)))
                     (TT)]
    [((Obj '() x) y (? SLI? s)) (for/fold ([sli s])
                                          ([obj (sli-vars s)])
                                  (match obj
                                    [(Obj π y) (sli-subst sli (Obj π x) obj)]
                                    [else sli]))]
    [((Obj π x) y (? SLI? s)) (for/fold ([sli : (U SLI FF) s])
                                  ([obj (sli-vars s)])
                                  (if (FF? sli)
                                      sli
                                      (match obj
                                        [(Obj '() y) (sli-subst sli (Obj π x) obj)]
                                        [(Obj π y) #:when (not (empty? π)) 
                                                   (FF)]
                                        [else sli])))]
    [(#f y (? SLI? s)) (let ([y-objs (filter (λ ([o : Obj]) (equal? y (Obj-var o))) (sli-vars s))])
                         (for/fold ([sli s])
                                   ([obj y-objs])
                                   (sli-elim-var s obj)))]
    [(_ _ _) (error 'subst "unknown subst ~a ~a ~a" new old-var tgt)]))

(: ext-TMap (TMap 
             Var 
             Type 
             . -> . TMap))
(define (ext-TMap imap x t)
  (hash-set imap x (cons t (hash-ref imap x (λ () empty)))))


(: ext-NTMap (NTMap 
              Var 
              Type 
              . -> . NTMap))
(define (ext-NTMap nmap x t)
  (hash-set nmap x (if (hash-has-key? nmap x)
                       (Union (list t (hash-ref nmap x)))
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
;; λDTR Relations
;;*****************************************

(: subobj? ((Opt Obj) (Opt Obj) . -> . Boolean))
(define (subobj? o1 o2)
  (cond
    [(not o2) #t]
    [else (equal? o1 o2)]))

(: implies?  (Prop Prop . -> . Boolean))
(define (implies? p1 p2)
  (proves? (env (list p1)) p2))

(: tautology? (Prop . -> . Boolean))
(define (tautology? p)
  (proves? (env empty) p))

(: contradiction? (Prop . -> . Boolean))
(define (contradiction? p)
  (proves? (env (list p)) (FF)))

(: subtype? (Type Type . -> . Boolean))
(define (subtype? t1 t2)
  (match* (t1 t2)
    ;; S-Refl
    [(_ _) #:when (equal? t1 t2) #t]
    ;; S-Top
    [(_ (? Top?)) #t]
    ;; S-UnionSub
    [((Union ts) _) (andmap (λ ([t : Type]) (subtype? t t2)) ts)]
    ;; S-UnionSuper
    [(_ (Union ts)) (ormap (λ ([t : Type]) (subtype? t1 t)) ts)]
    [((Pair t1l t1r) (Pair t2l t2r)) (and (subtype? t1l t2l)
                                          (subtype? t1r t2r))]
    ;; S-Fun
    [((Abs x1 t1d t1r p1+ p1- oo1) 
      (Abs x2 t2d t2r p2+ p2- oo2))
     (and (subtype? t2d (subst (var x2) x1 t1d))
          (subtype? (subst (var x2) x1 t1r) t2r)
          (subobj? (subst (var x2) x1 oo1) oo2)
          (implies? (subst (var x2) x1 p1+) p2+)
          (implies? (subst (var x2) x1 p1-) p2-))]
    ;; S-Dep
    [((Dep x t1 p1) (Dep y t2 p2)) (and (subtype? t1 t2)
                                        (implies? p1 (subst x y p2)))]
    ;; S-DepSub
    [((Dep _ t1 _) _) (subtype? t1 t2)]
    ;; S-DepTaut
    [(_ (Dep _ t2 p1)) (and (subtype? t1 t2)
                            (tautology? p1))]
    [(_ _) #f]))

(: gen-type-env (-> TMap (Listof IsT)))
(define (gen-type-env ts+)
  (for/list ([x (hash-keys ts+)])
    (IsT x
         (foldl (λ ([t-new : Type] [t-acc : Type])
                  (restrict t-acc t-new))
                (Top)
                (hash-ref ts+ x)))))

(: witness? (IsT Prop . -> . Boolean))
(define (witness? is p)
  (or (contains-Bot? (IsT-type is))
      (and (IsT? p)
           (equal? (IsT-var is) (IsT-var p))
           (subtype? (IsT-type is) (IsT-type p)))))

(: proves? (Env Prop . -> . Boolean))
(define (proves? E goal)
  (match* (E goal)
    ;; L-TT
    [(_ (TT)) #t]
    ;; L-AndI
    [(_ (And lhs rhs)) (and (proves? E lhs)
                            (proves? E rhs))]
    ;; L-OrI
    [(_ (Or lhs rhs)) (or (proves? E lhs)
                          (proves? E rhs))]
    ;; L-IsDepE
    [(_ (IsT x (Dep y t p))) 
     (proves? E (And (IsT x t)
                     (subst x y p)))]
    ;; L-NotT
    [((Env ps ts+ ts- sli) (? NotT? p)) 
     (proves? (Env (cons (¬ p) ps) ts+ ts- sli) (FF))]
    ;; L-False
    [((Env (cons (FF) ps) ts+ ts- sli) _) #t]
    ;; L-TTSkip
    [((Env (cons (TT) ps) ts+ ts- sli) _) 
     (proves? (Env ps ts+ ts- sli) goal)]
    ;; L-AndE
    [((Env (cons (And lhs rhs) ps) ts+ ts- sli) _) 
     (proves? (Env (cons lhs (cons rhs ps)) ts+ ts- sli) goal)]
    ;; L-OrE
    [((Env (cons (Or lhs rhs) ps) ts+ ts- sli) _) 
     (and (proves? (Env (cons lhs ps) ts+ ts- sli) goal)
          (proves? (Env (cons rhs ps) ts+ ts- sli) goal))]
    ;; L-IsDep-Move
    [((Env (cons (IsT x (Dep y t p)) ps) ts+ ts- sli) _)
     (let ([p1 (IsT x t)]
           [p2 (subst x y p)])
       (proves? (Env (cons p1 (cons p2 ps)) ts+ ts- sli) goal))]
    ;; L-NotDep-Move
    [((Env (cons (NotT x (Dep y t p)) ps) ts+ ts- sli) _)
     (let ([ptype (NotT x t)]
           [pprop (¬ (subst x y p))])
       (proves? (Env (cons (Or ptype pprop) ps) ts+ ts- sli) goal))]
    ;; L-Is-Move
    [((Env (cons (IsT x t) ps) ts+ ts- sli) _)
     (proves? (Env ps (ext-TMap ts+ x t) ts- sli) goal)]
    ;; L-NotMove
    [((Env (cons (NotT x t) ps) ts+ ts- sli) _)
     (proves? (Env ps ts+ (ext-NTMap ts- x t) sli) goal)]
    ;; L-SLI-Move
    [((Env (cons (? SLI? s) ps) ts+ ts- sli) _)
     (proves? (Env ps ts+ ts- (append s sli)) goal)]
    ;; L-Restrict*
    [((Env (? empty?) ts+ ts- sli) _)
     #:when (hash-empty? ts-)
     (or (let ([t-env : (Listof IsT) 
                      (gen-type-env ts+)])
           (ormap (λ ([xt : IsT])
                    (witness? xt goal))
                  t-env))
         (and (SLI? goal)
              (sli-proves-sli? sli goal))
         (not (sli-satisfiable? sli)))]
    ;; L-Remove*
    [((Env (? empty?) ts+ ts- sli) _)
     #:when (not (hash-empty? ts-))
     (proves? 
      (Env empty 
           (for/hash : TMap ([x : Var (hash-keys ts+)])
             (let* ([xnt : Type (hash-ref ts- x (λ () (Bot)))]
                    [xts : (Listof Type) (hash-ref ts+ x)])
               (values x (map (λ ([t : Type]) (remove t xnt)) xts))))
           (hash)
           sli)
      goal)]
    [(_ _) #f]))

(: common-val? (Type Type . -> . Boolean))
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
     (and (not (contradiction? (And p1 (subst x1 x2 p2))))
          (common-val? t1 t2))]
    [((Dep x t p) _) (and (not (contradiction? p))
                          (common-val? t t2))]
    [(_ (Dep x t p)) (and (not (contradiction? p))
                          (common-val? t1 t))]
    [(_ _) #f]))

(: type-conflict? (Type Type . -> . Boolean))
(define (type-conflict? t1 t2)
  (not (common-val? t1 t2)))

(: restrict (Type Type . -> . Type))
(define (restrict t1 t2)
  (cond
    [(not (common-val? t1 t2)) (Bot)]
    [(Union? t1) (reduce-Union (Union (map (λ ([t : Type]) 
                                             (restrict t t2)) 
                                           (Union-types t1))))]
    [(subtype? t1 t2) t1]
    [else t2]))

(: remove (Type Type . -> . Type))
(define (remove t1 t2)
  (cond
    [(subtype? t1 t2) (Bot)]
    [(Union? t1) (reduce-Union (Union (map (λ ([t : Type]) 
                                             (remove t t2)) 
                                           (Union-types t1))))]
    [else t1]))

(module+ test
  (check-false (type-conflict? (Int) (Int)))
  (check-false (type-conflict? (Int) (Top)))
  (check-true (type-conflict? (Int) (Bot)))
  (check-false (type-conflict? (Union `(,(Bot) ,(Int) ,(Str)))
                               (Union `(,(Int) ,(Int)))))
  (check-true (type-conflict? (Union `(,(Bot) ,(Int) ,(Str)))
                              (Pair (Top) (Top))))
  (check-false (type-conflict? (Abs 'x (Bot) (Top) (TT) (TT) #f)
                               (Abs 'x (Int) (Int) (TT) (FF) #f)))
  
  (check-true (subtype? (Str) (Str)))
  (check-true (subtype? (Str) (Top)))
  (check-true (subtype? (Bot) (Str)))
  (check-false (subtype? (Int) (Str)))
  (check-true (subtype? (Union `(,(Int) ,(Str)))
                        (Union `(,(Str) ,(Int)))))
  (check-false (subtype? (Union `(,(Int) ,(Str)))
                         (Union `(,(Abs 'x (Int) (Int) (TT) (FF) #f) 
                                  ,(Pair (Top) (Top))))))
  (check-true (subtype? (Pair (Int) (Str))
                        (Pair (Union `(,(Str) ,(Int)))
                              (Union `(,(Str) ,(Int))))))
  (check-false (subtype? (Abs 'x (Union `(,(Str) ,(Int))) 
                              (Union `(,(Str) ,(Int))) (TT) (FF) #f)
                         (Abs 'x (Int) (Int) (TT) (FF) (var 'x))))
(check-true (subtype? (Abs 'x (Union `(,(Str) ,(Int))) (Int) (TT) (FF) (var 'x))
                      (Abs 'x (Int) (Union `(,(Str) ,(Int))) (TT) (TT) #f)))
  
  (check-true (proves? (env empty) (TT)))
  (check-false (proves? (env empty) (FF)))
  (check-true (proves? (env empty) (Or (TT)
                                       (FF))))
  (check-true (proves? (env (list (FF))) (FF)))
  (check-true (proves? (env (list (IsT 'x (Int)))) (NotT 'x (Str))))
  (check-true (proves? (env (list (IsT 'x (Int)))) 
                       (And (NotT 'x (Str))
                            (NotT 'x (Pair (Int) (Str))))))
  (check-false (proves? (env (list (IsT 'x (Int)))) 
                       (And (NotT 'x (Str))
                            (NotT 'y (Pair (Int) (Str))))))
  (check-false (proves? (env (list (IsT 'x (Int)))) 
                       (And (NotT 'y (Str))
                            (NotT 'x (Pair (Int) (Str))))))
  (check-true (proves? (env (list (IsT 'x (Int)))) 
                       (Or (NotT 'x (Int))
                           (NotT 'x (Pair (Int) (Str))))))
  (check-false (proves? (env (list (IsT 'x (Union (list (Int) (Str))))))
                        (IsT 'x (Str))))
  (check-true (proves? (env (list (Or (IsT 'x (Int))
                                      (FF))
                                  (Or (NotT 'x (Int))
                                      (IsT 'y (Str)))
                                  (Or (And (IsT 'y (Int)) (IsT 'z (Bool)))
                                      (IsT 'z (Union `(,(Str) ,(Int)))))
                                  (IsT 'z (Union `(,(Str) ,(Bool))))))
                       (And (NotT 'z (Bool))
                            (Or (FF)
                                (NotT 'z (Bot))))))
  ;; subtyping tests
  (check-true (proves? (env (list (IsT 'x (Str)))) 
                       (IsT 'x (Union `(,(Int) ,(Str))))))
  ;; remove tests
  (check-true (proves? (env (list (IsT 'x (Union `(,(Int) ,(Str))))
                                  (NotT 'x (Str)))) 
                       (IsT 'x (Int))))
  (check-true (proves? (env (list (IsT 'x (Union `(,(Int) ,(Str))))
                                  (NotT 'x (Str))
                                  (NotT 'x (Union `(,(Int) ,(Bot)))))) 
                       (IsT 'x (Bot))))
  ;; restrict tests
  (check-true (proves? (env (list (IsT 'x (Union `(,(Int) ,(Str))))
                                  (IsT 'x (Union `(,(Int) ,(Pair (Top) (Top)))))))
                       (IsT 'x (Int))))
  (check-true (proves? (env (list (IsT 'x (Int)) (IsT 'x (Str))))
                       (FF)))
  
  ;; dependent type tests
  (check-true (proves? (env (list (IsT 'x (Int)) (IsT 'y (Str))))
                       (IsT 'y (Dep 'v (Str) (IsT 'x (Int))))))
  (check-false (proves? (env (list (IsT 'x (Int)) (IsT 'y (Str))))
                       (IsT 'y (Dep 'v (Str) (IsT 'x (Str))))))
  (check-true (proves? (env (list (IsT 'x (Int)) (IsT 'y (Str))))
                       (IsT 'y (Dep 'v (Top) (IsT 'v (Str))))))
  (check-true (proves? (env (list (IsT 'y (Dep 'v (Int) (IsT 'x (Str))))))
                       (IsT 'y (Dep 'v (Union `(,(Int) ,(Str))) 
                                    (And (IsT 'x (Str))
                                         (IsT 'v (Int)))))))
  (check-false (proves? (env (list (IsT 'y (Dep 'v (Int) (IsT 'x (Str))))
                                   (IsT 'z (Top))))
                        (IsT 'y (Dep 'v (Union `(,(Int) ,(Str))) 
                                     (And (And (IsT 'x (Str))
                                               (IsT 'v (Int)))
                                          (IsT 'z (Int)))))))
  
  ;; SLI tests
  (check-true (proves? (env (list (IsT 'x (Dep 'v (Int) `(,(leq (lexp `(7 ,(var 'v)))
                                                                (lexp 28)))))
                                  (list (leq (lexp 4)
                                             (lexp `(1 ,(Obj '() 'x)))))))
                       (IsT 'x (Dep 'v (Int) `(,(leq (lexp `(1 ,(var 'v)))
                                                     (lexp 4))
                                               ,(leq (lexp 4)
                                                     (lexp `(1 ,(Obj '() 'v)))))))))
  (check-false (proves? (env (list (IsT 'x (Dep 'v (Int) `(,(leq (lexp `(7 ,(var 'v)))
                                                                 (lexp 28)))))
                                   `(,(leq (lexp 2)
                                           (lexp `(1 ,(Obj '() 'x)))))))
                        (IsT 'x (Dep 'v (Int) `(,(leq (lexp `(1 ,(var 'v)))
                                                        (lexp 4))
                                                ,(leq (lexp 4)
                                                      (lexp `(1 ,(var 'v)))))))))
  (check-true (proves? (env (list (list (leq (lexp 4)
                                             (lexp `(1 ,(var 'x)))))
                                  (Or (IsT 'x (Int))
                                      `(,(leq (lexp `(1 ,(var 'x))) 
                                           (lexp 3))))
                                  (Or (NotT 'x (Int))
                                      (IsT 'y (Str)))
                                  (Or (And (IsT 'y (Int)) (IsT 'z (Bool)))
                                      (IsT 'z (Union `(,(Str) ,(Int)))))
                                  (IsT 'z (Union `(,(Str) ,(Bool))))))
                       (And (NotT 'z (Bool))
                            (And `(,(leq (lexp -1)
                                         (lexp `(1 ,(var 'x)))))
                                 (NotT 'z (Bot))))))
  (check-false (proves? (env (list (list (leq (lexp 4)
                                              (lexp `(1 ,(var 'x)))))
                                   (Or (IsT 'x (Int))
                                       `(,(leq (lexp `(1 ,(var 'x))) 
                                               (lexp 3))))
                                   (Or (NotT 'x (Int))
                                       (IsT 'y (Str)))
                                   (Or (And (IsT 'y (Int)) (IsT 'z (Bool)))
                                       (IsT 'z (Union `(,(Str) ,(Int)))))
                                   (IsT 'z (Union `(,(Str) ,(Bool))))))
                        (And (NotT 'z (Bool))
                             (And `(,(leq (lexp 5)
                                          (lexp `(1 ,(var 'x)))))
                                  (NotT 'z (Bot)))))))