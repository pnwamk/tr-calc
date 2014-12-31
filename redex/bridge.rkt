#lang racket

(require fme racket/contract racket/set)
(provide (all-defined-out))

(define int? exact-integer?)

(define (fme-elim-var Φ x)
  (fme-elim* Φ (λ (var)
                 (match var
                   [(list π '@ (? (curry equal? x))) #t]
                   [_ #f]))))

(define (redex-fme-sat? e)
  (fme-sat? (redex->fme e)))

(define (redex-sli-equal? sli1 sli2)
  (equal? (redex->fme sli1) (redex->fme sli2)))

(define (redex-fme-imp? e1 e2)
  (fme-imp? (redex->fme e1)
            (redex->fme e2)))

(define/contract (redex->fme e)
  (-> any/c (set/c leq?))
  (let parse ([e e])
    (match e
      [(list) (set)]
      [(cons (list lhs ≤ rhs) rest) 
       (set-add (parse rest) (leq (parse lhs)
                                  (parse rhs)))]
      [(? int? i) (lexp i)]
      [(list π '@ x) (lexp `(1 (,π @ ,x)))]
      [(list '* (? int? i) o) (lexp-scale (parse o) i)]
      [(list '+ o1 o2) (lexp-plus (parse o1) (parse o2))]
      [else (error 'redex->fme-lexp "bad fme-exp!!! ~a" e)])))

(define/contract (lexp->redex l)
  (-> lexp? (or/c list? int?))
  (define var-terms (for/list ([x (lexp-vars l)])
                      `(* ,(lexp-coeff l x) ,x)))
  (define c (lexp-const l))
    (cond
      [(empty? var-terms) c]
      [(not (zero? c)) `(+ ,c ,var-terms)]
      [(= 1 (length var-terms)) (first var-terms)]
      [else `(+ ,var-terms)]))

(define/contract (leq->redex e)
  (-> leq? list?)
  (define-values (l r) (leq-lexps e))
  `(,(lexp->redex l) ≤ ,(lexp->redex r)))

(define/contract (sli->redex sli)
  (-> sli? list?)
  (for/list ([ineq (in-set sli)])
      (leq->redex ineq)))


