#lang racket

;; functions responsible for converting redex model representations
;; into data the 'fme' library can parse, and for taking 'fme' library
;; output and converting it back into redex model representations


(require fme
         racket/contract
         racket/set
         "dtr-lang.rkt"
         "utils.rkt")

(provide (all-defined-out)
         fme-sat?
         fme-elim-vars)

(define int? exact-integer?)

(define/contract (satisfiable-Φ? Φ)
  (-> Φ? boolean?)
  (fme-sat? (φ-list->sli (dot-list->list Φ))))

(define/contract (Φ-implies-φ? Φ φ)
  (-> Φ? φ? boolean?)
  (fme-imp? (φ-list->sli (dot-list->list Φ))
            (φ-list->sli (list φ))))

(define/contract (sli->Φ s)
  (-> Φ? sli?)
  (cond
    [(set-empty? s) 'tt]
    [else
     (for/fold ([prop (leq->φ (set-first s))])
               ([ineq (in-set (set-rest s))])
       `(,(leq->φ ineq) ∧ ,prop))]))

(define/contract (Φ->sli Φ)
  (-> Φ? sli?)
  (φ-list->sli (dot-list->list Φ)))

(define (fme-elim-vars sys xs)
  (-> sli? (listof x?) sli?)
  (define (unwanted-o? o)
    (member o xs))
  (fme-elim* sys unwanted-o?))


(define/contract (leq->φ e)
  (-> leq? φ?)
  (define-values (l r) (leq-lexps e))
  `(,(lexp->θ l) ≤ ,(lexp->θ r)))


(define/contract (lexp->θ l)
  (-> lexp? θ?)
  (define vars-exp
    (match (lexp-vars l)
      ['() #f]
      [(cons x xs) 
       (for/fold ([rexp `(,(lexp-coeff l x) ⊗ ,x)])
                 ([x* xs])
         `((* ,(lexp-coeff l x*) ,x*) ⊕ ,rexp))]))
  (define c (lexp-const l))
  (cond
    [(not vars-exp) c]
    [(zero? c) vars-exp]
    [else `(,c ⊕ ,vars-exp)]))

(define/contract (θ->lexp l)
  (-> θ? lexp?)
  (match l
    [(? int? i) (lexp i)]
    [(? symbol? x) (lexp `(1 ,x))]
    [`(,i ⊗ ,x)
     (lexp `(,i ,x))]
    [`(,lhs ⊕ ,rhs)
     (lexp-plus (θ->lexp lhs) (θ->lexp rhs))]
    [else (error 'redex->fme-lexp "bad fme-exp!!! ~a" l)]))

(define/contract (φ->leq ineq)
  (-> φ? leq?)
  (match-define `(,lhs ≤ ,rhs) ineq)
  (leq (θ->lexp lhs)
       (θ->lexp rhs)))

(define/contract (φ-list->sli φs)
  (-> (listof φ?) sli?)
  (for/set ([ineq (in-list φs)])
    (φ->leq ineq)))





