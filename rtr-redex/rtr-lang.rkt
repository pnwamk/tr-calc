#lang racket

(require redex)
(provide (all-defined-out))

;; ---------------------------------------------------------
;; Definition for Base Refinement-Typed Racket
(define-language RTR-Base
  ;; variables, as a convention
  [x y z ::= variable-not-otherwise-mentioned]
  [n ::= integer]
  [b ::= true false]
  ;; primitive operations
  [p ::= int? bool? not fst snd + - * <= pair]
  ;; Values
  [v ::= n b p]
  ;; Expressions
  [e ::= v x (λ ([x : t] ...) e)
     (e e ...) (if e e e) (let ([x e] ...) e)]
  ;; path element
  [pe ::= first second]
  [pth ::= (pe ...)]
  ;; objects
  [o ::= (obj pth x)]
  ;; systems of linear inequalities
  [T S ::= Any True False Int (U T ...)
     (Abs ([x : T] ...) -> Res)
     (Refine [x : T] P)]
  [Res ::= (Result T P P)]
  ;; propositions
  [P Q ::= (Is o T) (IsNot o T) (Alias x o)
     (And P ...) (Or P ...) TT FF]
  ;; Type Environment
  [Γ  ::= {[x : T] ...}]
  ;; Proposition Environment
  [Ψ  ::= {P ...}]
  ;; Environment
  [Δ ::= (Env Γ Ψ)])

;; ---------------------------------------------------------
;; racket predicates
(define x? (redex-match? RTR-Base x))
(define p? (redex-match? RTR-Base p))
(define e? (redex-match? RTR-Base e))
(define pe? (redex-match? RTR-Base pe))
(define pth? (redex-match? RTR-Base pth))
(define o? (redex-match? RTR-Base o))
(define T? (redex-match? RTR-Base T))
(define P? (redex-match? RTR-Base P))
(define type-env? (redex-match? RTR-Base Γ))
(define prop-env? (redex-match? RTR-Base Ψ))
(define env? (redex-match? RTR-Base Δ))
(define Is? (redex-match? RTR-Base (Is o T)))
(define IsNot? (redex-match? RTR-Base (IsNot o T)))
(define Alias? (redex-match? RTR-Base (Alias x o)))
(define And? (redex-match? RTR-Base (And P ...)))
(define Or? (redex-match? RTR-Base (Or P ...)))
(define TT? (redex-match? RTR-Base TT))
(define FF? (redex-match? RTR-Base FF))
(define Refine? (redex-match? RTR-Base (Refine [_ : _] _)))
(define Bot? (redex-match? RTR-Base (U)))
(define Any? (redex-match? RTR-Base Any))

;; ---------------------------------------------------------
;; Union smart constructor
(define-metafunction RTR-Base
  Un : T ... -> T
  [(Un T) T]
  [(Un T ... Any S ...) Any]
  [(Un T ... (U) S ...)
   (Un T ... S ...)]
  [(Un T ... (U T_inner ...) S ...)
   (Un T ... T_inner ... S ...)]
  [(Un T ...)
   (U T ...)
   (where (S ...) ,(sort (term (T ...))
                         (λ (a b)
                           (<= (equal-hash-code a)
                               (equal-hash-code b)))))])
(define (x-sym) 'x)
(define (y-sym) 'y)
(define (z-sym) 'y)
(define-term Bool (Un True False))
(define-term mt-Env (Env () ()))

;; ---------------------------------------------------------
;; var
;; constructor for simple objects
;; (when rendering, we can simplify '(var x)' to just 'x'
(define-metafunction RTR-Base
  var : x -> o
  [(var x) (obj () x)])


;; ---------------------------------------------------------
;; in (i.e. ∈)
(define-metafunction RTR-Base
  in : any (any ...) -> boolean
  [(in any_1 any_2) ,(and (memq (term any_1) (term any_2)) #t)])

(module+ test
  (test-equal (term (in x ())) #f)
  (test-equal (term (in x (a b c x y z))) #t)
  (test-equal (term (in x (a b c y z))) #f))

;; ---------------------------------------------------------
;; update
;; replaces an id's entry in Γ if it has an entry,
;; or adds new entry
(define-metafunction RTR-Base
  update : Γ x T  -> Γ
  [(update Γ x T)
   ,(cons (term [x : T])
          (filter-not (λ (t) (eq? (car t) (term x)))
                      (term Γ)))])

(module+ test
  (test-equal (term (update {} a Int))
              (term {[a : Int]}))
  (test-equal (term (update {[a : Int] [b : Any] [c : Any]} b Int))
              (term {[b : Int] [a : Int] [c : Any]}))
  (test-equal (term (update {[a : Int] [b : Any] [c : Any]} d Int))
              (term {[d : Int] [a : Int] [b : Any] [c : Any]})))


;; --------------------------------------------------------------
;; lookup
;; type of x in Γ
;; (takes an optional default argument for failure)
(define-metafunction RTR-Base
  lookup : Γ x  -> T or #f
  [(lookup Γ x)
   ,(for/first ([y:t (in-list (term Γ))]
                #:when (eq? (term x) (first y:t)))
      (third y:t))])

(module+ test
  (test-equal (term (lookup {} a))
              #f)
  (test-equal (term (lookup {[a : Int] [b : Bool] [c : Any]} d))
              #f)
  (test-equal (term (lookup {[a : Int] [b : Bool] [c : Any]} b))
              (term Bool)))

;; ---------------------------------------------------------
;; id-at-bot
;; Is there an identifier whose type is ⊥ in Γ
(define-metafunction RTR-Base
  id-at-bot : Γ -> x or #f
  [(id-at-bot Γ)
   ,(for/first ([x:t (in-list (term Γ))]
                #:when (Bot? (third x:t)))
      (first x:t))])

(module+ test
  (test-equal (term (id-at-bot {[a : Int] [b : (U)] [c : Any]}))
              (term b))
  (test-equal (term (id-at-bot {[a : Int] [b : Int] [c : Any]}))
              (term #f)))

;; ---------------------------------------------------------
;; id-at-refine
;; Is there an identifier whose type is a refinement in Γ
(define-metafunction RTR-Base
  id-at-refine : Γ -> x or #f
  [(id-at-refine Γ)
   ,(for/first ([x:t (in-list (term Γ))]
                #:when (Refine? (third x:t)))
      (first x:t))])

(module+ test
  (test-equal (term (id-at-refine {[a : Int] [b : (Refine [v : Int] TT)] [c : Any]}))
              (term b))
  (test-equal (term (id-at-refine {[a : Int] [b : Int] [c : Any]}))
              (term #f)))


;; ---------------------------------------------------------
;; Fresh variable functions
(define-metafunction RTR-Base
  fresh-var : any x -> x
  [(fresh-var any x) ,(variable-not-in (term any) (term x))])
(define-metafunction RTR-Base
  fresh-vars : any (x ...) -> (x ...)
  [(fresh-vars any (x ...)) ,(variables-not-in (term any) (term (x ...)))])


;; ---------------------------------------------------------
;; ext
;; environment extension
(define-metafunction RTR-Base
  ext : any any ... -> Δ or Γ or Ψ
  [(ext any) any]
  [(ext (Env Γ Ψ) [x : T] any ...)
   (ext (Env (ext Γ [x : T]) Ψ) any ...)]
  [(ext (Env Γ Ψ) P any ...)
   (ext (Env Γ (ext Ψ P)) any ...)]
  [(ext Γ [x : T] ...)
   ,(append (term ([x : T] ...)) (term Γ))]
  [(ext Ψ P ...)
   ,(append (term (P ...)) (term Ψ))])

(module+ test
  (test-equal (term (ext (Env () ())))
              (term (Env {} {})))
  (test-equal (term (ext (Env {} {}) TT))
              (term (Env {} {TT})))
  (test-equal (term (ext (Env {} {TT}) (Is (var x) Int)))
              (term (Env {} {(Is (var x) Int) TT})))
  (test-equal (term (ext (Env {} {TT}) [x : Int]))
              (term (Env {[x : Int]} {TT}))))

(module+ test
  (test-results))

