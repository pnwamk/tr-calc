#lang typed/racket

(: foo ((U (Listof Integer) (Listof Boolean)) . -> . (Listof Boolean)))
(define (foo l)
  (cond
    ;[(exact-integer? (car l)) (map odd? l)]
    [(andmap exact-integer? l) (map odd? l)]
    [else (map not l)]))


;; Car(X) ISA  INT  ====>   X   ISA  (Pairof Int Top)