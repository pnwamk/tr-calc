#lang racket

(require fme racket/match)
(provide (all-defined-out))

(define int? exact-integer?)

;; z (obj π x) (z * LE) (LE + LE)
(define (redex->lexp le)
  (let parse ([le le])
    (match le
      ;; constant
      [(? int? n) `(,n)]
      [`(obj ,π ,x) `((1 (obj ,π ,x)))]
      [`(,n * ,m) #:when (and (int? n) (int? m))
                  (list (* n m))]
      ;; * over +
      [`(,n * (,lhs + ,rhs)) #:when (int? n)
                             (append (parse `(,n * ,lhs))
                                     (parse `(,n * ,rhs)))]
      ;; int * (int body)
      [`(,n * (,m * ,rhs)) #:when (and (int? n) (int? m))
                           (parse `(,(* n m) * ,rhs))]
      ;; int * obj
      [`(,n * (obj ,π ,x)) #:when (int? n)
                           `((,n (obj ,π ,x)))]
      ;; int + int
      [`(,n + ,m) #:when (and (int? n) (int? m))
                  (list (+ n m))]
      [`(,lhs + ,rhs) (list (parse lhs)
                            (parse rhs))]
      ;; LE + LE (else case)
      [else (error 'parse-LE "bad match!!! ~a" le)])))

(define (redex->sli sli)
  (map redex->lexp
       sli))


(define (lexp->redex l)
  (define c (lexp-constant l))
  (let loop ([exp c]
             [vars (lexp-vars l)])
    (cond
      [(empty? vars) exp]
      [else
       (let* ([x (first vars)]
              [z (lexp-coefficient l x)])
           (loop `((,z * ,x) + ,exp)
                 (rest vars)))])))

(define (sli->redex sli)
  (map lexp->redex sli))

(define (redex-sli-proves-sli? sli1 sli2)
  (sli-proves-sli? (redex->sli sli1)
                   (redex->sli sli2)))

(define (redex-sli-satisfiable? sli1)
  (sli-satisfiable? (redex->sli sli1)))



