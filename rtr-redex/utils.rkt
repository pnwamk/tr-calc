#lang racket

(provide (all-defined-out))
(require redex rackunit)


(define (dot-list->list dl)
  (let loop ([dl dl]
             [acc null])
    (match dl
      ['() acc]
      [`(,x · ,xs)
       (loop xs (cons x acc))])))

(define (list->dot-list xs)
  (for/fold ([dl '()])
            ([x (in-list (reverse xs))])
    `(,x · ,dl)))

(define-syntax-rule (test*-set-equal l1 l2)
  (check-equal? (list->set (term l1)) (list->set (term l2))))

(define-syntax-rule (test*-equal l1 l2)
  (check-equal? (term l1) (term l2)))

(define-syntax-rule (test-true t1)
  (check-true t1))

(define-syntax-rule (test-false t1)
  (check-false t1 #f))

(define-syntax-rule (test*-true t1)
  (check-true (term t1) #t))

(define-syntax-rule (test*-false t1)
  (check-false (term t1) #f))

