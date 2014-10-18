#lang typed/racket

(require typed/rackunit)



;;*****************************************                              
;; λDTR Definition
;;*****************************************
(define prim-ops '(add1 zero? int? str? bool? proc? 
                       str-len + error cons? car cdr))

(struct: CAR () #:transparent)
(struct: CDR () #:transparent)

(define-type Path (Listof (U CAR CDR)))

(define-type Var Symbol)
(: Var? (Any . -> . Boolean : Var))
(define Var? symbol?)

(struct: Obj ([path : (Listof Path)] [var : Var]))

(: var (-> Var Obj))
(define (var x)
  (Obj empty x))

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

(struct: Top () #:transparent)
(struct: T () #:transparent)
(struct: F () #:transparent)
(struct: Int () #:transparent)
(struct: Union ([types : (Listof Type)]) #:transparent)
(struct: Abs ([arg : Symbol] 
              [domain : Type]
              [range : Type]
              [prop+ : Prop] 
              [prop- : Prop] 
              [obj : (Opt Obj)]) #:transparent)
(struct: Pair ([car : Type] [cdr : Type]) #:transparent)
(struct: Dep ([type : Type] [prop : Prop]) #:transparent)
(define-type Type (U Top T F Int Union Abs Pair Dep))
(define Dep-var : Symbol (gensym))

(struct: TRUE () #:transparent)
(struct: FALSE () #:transparent)
(struct: IS ([var : Var] [type : Type]) #:transparent)
(struct: ISNT ([var : Var] [type : Type]) #:transparent)
(struct: AND ([lhs : Prop] [rhs : Prop]) #:transparent)
(struct: OR ([lhs : Prop] [rhs : Prop]) #:transparent)
(define-type Prop (U TRUE FALSE IS ISNT AND OR))

(: Prop? (Any . -> . Boolean : Prop))
(define (Prop? a)
  (or (TRUE? a)
      (FALSE? a)
      (IS? a)
      (ISNT? a)
      (AND? a)
      (OR? a)))

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

(define-type Opt Option)
(struct: Env ([props : (Listof Prop)] 
              [types+ : (HashTable Var (Listof Type))]
              [types- : (HashTable Var (Listof Type))]))

(: env ((Listof Prop) . -> . Env))
(define (env lop)
  (Env lop (hash) (hash)))

;;*****************************************
;; λDTR Helpers
;;*****************************************
(: ¬ (Prop . -> . Prop))
(define (¬ p)
  (match p
    [(TRUE) (FALSE)]
    [(FALSE) (TRUE)]
    [(IS x t) (ISNT x t)]
    [(ISNT x t) (IS x t)]
    [(AND p q) (OR (¬ p) (¬ q))]
    [(OR p q) (AND (¬ p) (¬ q))]))
; option-l

(: contains-Bot? (Type -> Boolean))
(define (contains-Bot? t)
  (match t
    [(Union '()) #t]
    [(Pair lhs rhs) (or (contains-Bot? lhs)
                        (contains-Bot? rhs))]))
;; TODO, check for FALSE in Dep?

(: atomic? (Prop . -> . Boolean))
(define (atomic? p)
  (or (IS? p)
      (FALSE? p)))

(: subst (case-> [(Opt Obj) Var (Opt Obj) . -> . (Opt Obj)]
                 [(Opt Obj) Var Prop . -> . Prop]
                 [(Opt Obj) Var Type . -> . Type]))
(define (subst oo x a)
  a)
;; TODO subst

(: rec-type ((HashTable Var (Listof Type)) Var Type . -> . (HashTable Var (Listof Type))))
(define (rec-type tht x t)
  (hash-set tht x (cons t (hash-ref tht x (λ () empty)))))

(: reduce-Union (-> Type Type))
(define (reduce-Union t)
  (cond
    [(not (Union? t)) t]
    [else (let* ([ts (map reduce-Union (Union-types t))]
                 [clean-ts (filter (λ ([t : Type]) (not (contains-Bot? t))) ts)])
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
  (proves? (env (list p)) (FALSE)))

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
    [((Dep t1 p1) (Dep t2 p2)) (and (subtype? t1 t2)
                                    (implies? p1 p2))]
    ;; S-DepSub
    [((Dep t1 _) _) (subtype? t1 t2)]
    ;; S-DepTaut
    [(_ (Dep t2 p1)) (and (subtype? t1 t2)
                          (tautology? p1))]
    [(_ _) #f]))

(: proves? (Env Prop . -> . Boolean))
(define (proves? E goal)
  (match* (E goal)
    ;; L-True
    [(_ (TRUE)) #t]
    ;; L-AndI
    [(_ (AND lhs rhs)) (and (proves? E lhs)
                            (proves? E lhs))]
    ;; L-OrI
    [(_ (OR lhs rhs)) (or (proves? E lhs)
                          (proves? E lhs))]
    ;; L-Not
    [((Env ps ts+ ts-) (? ISNT? p)) 
     (proves? (Env (cons p ps) ts+ ts-) (FALSE))]
    ;; L-False
    [((Env (cons (FALSE) ps) ts+ ts-) _) #t]
    ;; L-AndE
    [((Env (cons (AND lhs rhs) ps) ts+ ts-) _) 
     (proves? (Env (cons lhs (cons rhs ps)) ts+ ts-) goal)]
    ;; L-OrE
    [((Env (cons (OR lhs rhs) ps) ts+ ts-) _) 
     (and (proves? (Env (cons lhs ps) ts+ ts-) goal)
          (proves? (Env (cons rhs ps) ts+ ts-) goal))]
    ;; L-IsMove
    [((Env (cons (IS x t) ps) ts+ ts-) _) 
     (proves? (Env ps (rec-type ts+ x t) ts-) goal)]
    ;; L-IsntMove
    [((Env (cons (ISNT x t) ps) ts+ ts-) _) 
     (proves? (Env ps ts+ (rec-type ts- x t)) goal)])
  ;; TODO
  )

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
    [((Dep t1 p1) (Dep t2 p2)) (and (not (contradiction? (AND p1 p2)))
                                    (common-val? t1 t2))]
    [((Dep t p) _) (and (not (contradiction? p))
                        (common-val? t t2))]
    [(_ (Dep t p)) (and (not (contradiction? p))
                        (common-val? t1 t))]))

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
  (check-true (proves? (env empty) (TRUE)))
  #;(check-false (proves? (env empty) (FALSE)))
  (check-true (proves? (env empty) (OR (TRUE)
                                       (FALSE))))
  (check-true (proves? (env (list (FALSE))) (FALSE))))