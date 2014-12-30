#lang racket

(require fme racket/contract racket/set)
(provide (all-defined-out))

(define int? exact-integer?)

;; o ::= i (obj π x) (* i o) (+ o o)
;; φ ::= (o ≤ o)
;; Φ ::= (φ ...)
(define (fme-elim-var Φ x)
  (fme-elim Φ x))

(define (redex-fme-sat? e)
  (fme-sat? (redex->fme e)))

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
      [(list 'obj π x) (lexp `(1 (obj ,π ,x)))]
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
      [else var-terms]))

(define/contract (leq->redex e)
  (-> leq? list?)
  (define-values (l r) (leq-lexps e))
  `(,(lexp->redex l) ≤ ,(lexp->redex r)))

(define/contract (sli->redex e)
  (-> sli? list?)
  (map leq->redex e))


