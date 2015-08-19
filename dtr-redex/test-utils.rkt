#lang racket

(provide (all-defined-out))
(require redex)

(define-syntax-rule (test*-set-equal l1 l2)
  (test-equal (list->set (term l1)) (list->set (term l2))))

(define-syntax-rule (test*-equal l1 l2)
  (test-equal (term l1) (term l2)))

(define-syntax-rule (test-true t1)
  (test-equal t1 #t))

(define-syntax-rule (test-false t1)
  (test-equal t1 #f))

(define-syntax-rule (test*-true t1)
  (test-equal (term t1) #t))

(define-syntax-rule (test*-false t1)
  (test-equal (term t1) #f))

