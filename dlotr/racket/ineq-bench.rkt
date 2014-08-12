#lang racket

(require "ineq.rkt")

(struct test (assumptions conclusion expected))

(define (run-test t)
  (equal? (sli-implies-sli (test-assumptions t)
                           (test-conclusion t))
          (test-expected t)))

; test1: 4 <= 3 is false
(define test1 (test empty
                    (list (leq (lc (4 #f))
                               (lc (3 #f))))
                    #f))



; test2: P and ~P --> false
(define test2 (test (list (leq (lc) (lc (1 'y)))
                          (leq-negate (leq (lc) (lc (1 'y)))))
                    (list (leq (lc (4 #f))
                               (lc (3 #f))))
                    #t))

; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
(define test3 (test (list (leq (lc (1 'x) (1 'y))
                                        (lc (1 'z)))
                                   (leq (lc)
                                        (lc (1 'y)))
                                   (leq (lc)
                                        (lc (1 'x))))
                             (list (leq (lc (1 'x))
                                        (lc (1 'z)))
                                   (leq (lc (1 'y))
                                        (lc (1 'z))))
                             #t))

; 7x <= 29 --> x <= 4
(define test4 (test (list (leq (lc (7 'x))
                                (lc (29 #f))))
                     (list (leq (lc (1 'x))
                                (lc (4 #f))))
                     #t))

; 7x <= 28 --> x <= 4
(define test5 (test (list (leq (lc (7 'x))
                                (lc (28 #f))))
                     (list (leq (lc (1 'x))
                                (lc (4 #f))))
                     #t))

; 7x <= 28 does not --> x <= 3
(define test6 (test (list (leq (lc (7 'x))
                                (lc (28 #f))))
                     (list (leq (lc (1 'x))
                                (lc (3 #f))))
                     #f))


; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
; x <= y + z; 
; 29r <= x + y + z + q; 
; 0 <= x;  
; 0 <= x + y + z; 
; 0 <= x + z; 
; x <= z
; z + 1 <= t
; 0 <= x + y;
; 0 <= x + r;
; 0 <= x + r + q;
; -->
; 0 <= t
(define test7 (test (list (leq (lc (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
                               (lc (4 'x) (3 'y) (9 'z) (20 'q) (100 'r)))
                          (leq (lc (1 'x))
                               (lc (1 'y) (1 'z)))
                          (leq (lc (29 'r))
                               (lc (1 'x) (1 'y) (1 'z) (1 'q)))
                          (leq (lc (0 #f))
                               (lc (1 'x)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'y) (1 'z)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'z)))
                          (leq (lc (1 'x))
                               (lc (1 'z)))
                          (leq (lc (1 'z) (1 #f))
                               (lc (1 't)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'y)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'r)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'r) (1 'q))))
                    (list (leq (lc (0 #f))
                               (lc (1 't))))
                    #t))

; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
; x <= y + z; 
; 29r <= x + y + z + q; 
; 0 <= x;  
; 0 <= x + y + z; 
; 0 <= x + z; 
; x <= z
; z + 1 <= t
; 0 <= x + y;
; 0 <= x + r;
; 0 <= x + r + q;
; -/->
; t <= 0
(define test8 (test (list (leq (lc (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
                               (lc (4 'x) (3 'y) (9 'z) (20 'q) (100 'r)))
                          (leq (lc (1 'x))
                               (lc (1 'y) (1 'z)))
                          (leq (lc (29 'r))
                               (lc (1 'x) (1 'y) (1 'z) (1 'q)))
                          (leq (lc (0 #f))
                               (lc (1 'x)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'y) (1 'z)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'z)))
                          (leq (lc (1 'x))
                               (lc (1 'z)))
                          (leq (lc (1 'z) (1 #f))
                               (lc (1 't)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'y)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'r)))
                          (leq (lc (0 #f))
                               (lc (1 'x) (1 'r) (1 'q))))
                    (list (leq (lc (1 't))
                               (lc (0 #f))))
                    #f))

(printf "test1 (4 <= 3 is false) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test1)))
(printf "\n")

(printf "test2 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test2)))
(printf "\n")

(printf "test3 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test3)))
(printf "\n")

(printf "test4 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test4)))
(printf "\n")

(printf "test5 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test5)))
(printf "\n")

(printf "test6 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test6)))
(printf "\n")

(printf "test7 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test7)))
(printf "\n")

(printf "test8 (?) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test8)))