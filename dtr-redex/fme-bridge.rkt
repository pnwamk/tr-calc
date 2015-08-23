#lang racket

;; functions responsible for converting redex model representations
;; into data the 'fme' library can parse, and for taking 'fme' library
;; output and converting it back into redex model representations


(require fme racket/contract racket/set)
(provide (all-defined-out))

(define int? exact-integer?)

(define (fme-elim-var Φ x)
  (fme-elim* Φ (curry equal? x)))

(define (redex-fme-sat? e)
  (fme-sat? (redex-list->fme e)))

(define (redex-sli-equal? sli1 sli2)
  (equal? (redex-list->fme sli1) (redex-list->fme sli2)))

(define (redex-fme-imp? e1 e2)
  (fme-imp? (redex-list->fme e1)
            (redex-list->fme e2)))

(define (parse-lexp l)
  (match l
    [(? int? i) (lexp i)]
    [(? symbol? x) (lexp `(1 ,x))]
    [`(,i ⊗ ,x)
     (lexp `(,i ,x))]
    [`(,lhs ⊕ ,rhs)
     (lexp-plus (parse-lexp lhs) (parse-lexp rhs))]
    [else (error 'redex->fme-lexp "bad fme-exp!!! ~a" l)]))

(define/contract (redex-list->fme Φ)
  (-> list? (set/c leq?))
  (for/set ([ineq (in-list Φ)])
    (match ineq
      [`(,lhs ≤ ,rhs) 
       (leq (parse-lexp lhs) (parse-lexp rhs))])))

(define/contract (lexp->redex l)
  (-> lexp? (or/c list? int?))
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

(define/contract (leq->redex e)
  (-> leq? list?)
  (define-values (l r) (leq-lexps e))
  `(,(lexp->redex l) ≤ ,(lexp->redex r)))

(define/contract (sli->redex sli)
  (-> sli? list?)
  (cond
    [(set-empty? sli) 'tt]
    [else
     (for/fold ([prop (leq->redex (set-first sli))])
               ([ineq (in-set (set-rest sli))])
       `(,(leq->redex ineq) ∧ ,prop))]))


