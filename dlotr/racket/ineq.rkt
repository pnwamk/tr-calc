#lang racket/base
; The MIT License (MIT)
;
; Copyright (c) 2014 Andrew M. Kent
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in
; all copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
; THE SOFTWARE.


;**********************************************************************
; Inequality Proving Library
;**********************************************************************
;
; This library aims to provide a sound algorithm for deciding
; if one system of linear inequalities over integers (P) implies
; another (Q) by assuming (P /\ ~Q) and testing for unsatisfiability.
;
; The transformations are based on the fourier-motzkin elimination method.
; Variables are eliminated until the system is trivial.
;
; Elimination is performed as follows:
;   1) partition the set of inequalities into those which can be 
;      written as a*x <= l, those which can be written as l <= a*x,
;      and those without x (where a is a positive coefficient and l
;      is a linear combination of variables and coefficients)
;   2) for each possible pairing l1 <= a1*x  and a2*x <= l2, we add
;      a2*l1 <= a1*l2 to the system and remove the equations with x
;      - now our system is larger and does not contain the variable x
;   3) this is repeated until the system can be trivially checked
;      to see if it is unsatisfiable
;
; Because this method is for linear inequalities with variables that range
; over reals (and not integers), it is a sound but incomplete model with 
; respect to testing for unsatisfiability
;
; All inequalities in this system are represented with <=
; For negation we utilize the equivalence ~(a <= b) <-> 1 + b <= a
; since we are concerned with integer solutions.

(require racket/list racket/bool)
(require rackunit)

; swap cons cell values car/cdr
(define (cons-swap c)
  (cons (cdr c) (car c)))


;**********************************************************************
; Linear Combinations  (lc)
; ax + by + cz + ...
;   (and related operations)
;**********************************************************************

; defining linear combinations
; takes list of (scalar symbol)
; #f is used for a constant
(define-syntax lc
  (syntax-rules ()
    [(lc) (hash)]
    [(lc (a x)) 
     (hash x a)]
    [(lc (a x) (b y) ...) 
     (hash-set (lc (b y) ...) x a)]))

(check-equal? (lc) (hash))
(check-equal? (lc (1 'x) (42 'y) (1 #f))
              (hash 'x 1 'y 42 #f 1))

; scalar-accessor
(define (lc-scalar lc var [notinval #f])
  (hash-ref lc var notinval))

(check-equal? (lc-scalar (lc (1 'x) (42 'y) (1 #f)) 'y) 42)
(check-equal? (lc-scalar (lc (1 'x) (42 'y) (1 #f)) #f) 1)
(check-equal? (lc-scalar (lc (1 'x) (42 'y) (1 #f)) 'q) #f)

; lc?
(define (lc? x)
  (hash? x))

(check-true (lc? (lc)))

; lc-var-list
; (no particular order)
(define (lc-vars lc)
  (hash-keys lc))

(check-not-false (let ([vars (lc-vars (lc (42 'x) (17 #f)))])
                   (and (= 2 (length vars))
                        (member 'x vars)
                        (member #f vars))))

; lc-scalars
; (no particular order)
(define (lc-scalars lc)
  (hash-values lc))

(check-not-false (let ([scalars (lc-scalars (lc (42 'x) (17 #f)))])
                   (and (= 2 (length scalars))
                        (member 42 scalars)
                        (member 17 scalars))))

; lc-pairs 
; list of (scalar . symbol)
(define (lc-pairs lc)
  (map cons-swap (hash->list lc)))

(check-not-false (let ([pairs (lc-pairs (lc (42 'x) (17 #f)))])
                   (and (= 2 (length pairs))
                        (member '(42 . x) pairs)
                        (member '(17 . #f) pairs))))

; lc-scale
(define (lc-scale lc a)
  (for/hash ([x (lc-vars lc)])
    (values x (* a (lc-scalar lc x)))))

(check-not-false (let ([scalars (lc-scalars (lc-scale (lc (42 'x) (17 #f)) 2))])
                   (and (= 2 (length scalars))
                        (member 84 scalars)
                        (member 34 scalars))))

; lc-remove-var
(define (lc-remove-var lc var)
  (hash-remove lc var))

(check-equal? (lc-remove-var (lc (42 'x) (17 #f)) 'x)
              (lc (17 #f)))

; lc-set-var-scalar
(define (lc-set-var-scalar lc var scalar)
  (unless (and (hash? lc)
               (exact-integer? scalar)
               (or (symbol? var)
                   (not var)))
    (error 'lc-add-var "invalid args"))
  (hash-set lc var scalar))

(check-equal? (lc-set-var-scalar (lc (17 #f)) 'x 42)
              (lc (42 'x) (17 #f)))
(check-equal? (lc-set-var-scalar (lc (2 'x) (17 #f)) 'x 42)
              (lc (42 'x) (17 #f)))

; lc-size
(define (lc-size lc)
  (hash-count lc))

(check-equal? (lc-size (lc (42 'x) (17 #f)))
              2)

; lc-empty?
(define (lc-empty? lc)
  (hash-empty? lc))

(check-false (lc-empty? (lc (42 'x) (17 #f))))
(check-not-false (lc-empty? (lc)))

; lc-subtract
(define (lc-subtract lc1 lc2)
  (define vars (lc-vars lc2))
  (for/fold ([lc lc1]) ([x vars])
    (let* ([s1 (lc-scalar lc1 x 0)]
           [s2 (lc-scalar lc2 x 0)]
           [snew (- s1 s2)])
      (if (zero? snew)
          (lc-remove-var lc x)
          (lc-set-var-scalar lc x snew)))))

(check-equal? (lc-subtract (lc (2 'x) (3 'y) (-1 #f))
                           (lc (2 'x) (-1 #f) (42 'z)))
              (lc (3 'y) (-42 'z)))
(check-equal? (lc-subtract (lc (0 #f))
                           (lc (2 'x) (-1 #f) (42 'z)))
              (lc (-2 'x) (-42 'z) (1 #f)))

;lc-scalar-gcd
; NOTE! currently this includes
; the constant in the lc, if it exists
;(define (lc-scalar-gcd lc)
;  (apply gcd (lc-scalars lc)))

; lc-has-var
(define (lc-has-var? lc x)
  (hash-has-key? lc x))

(check-false (lc-has-var? (lc (42 'x) (17 #f)) 'y))
(check-not-false (lc-has-var? (lc (42 'x) (17 #f)) 'x))

(define (lc-add1 lc)
  (if (lc-has-var? lc #f)
      (lc-set-var-scalar lc #f (add1 (lc-scalar lc #f)))
      (lc-set-var-scalar lc #f 1)))

(check-equal? (lc-add1 (lc)) (lc (1 #f)))
(check-equal? (lc-add1 (lc (1 #f) (5 'x))) 
              (lc (2 #f) (5 'x)))

;**********************************************************************
; Linear Inequalities  (leq)
; a1x1 + a1x2 + ... <= b1y1 + b2y2 + ...
;   (and related operations)
;**********************************************************************

; leq def
(struct leq (lhs rhs) #:transparent
  #:guard (λ (l r name)
            (unless (and (lc? l)
                         (lc? r))
              (error "invalid linear inequality"))
            (values l r)))

(define (leq-lcs ineq)
  (values (leq-lhs ineq) (leq-rhs ineq)))

; leq-contains-var
(define (leq-contains-var ineq var)
  (or (lc-has-var? (leq-lhs ineq) var)
      (lc-has-var? (leq-rhs ineq) var)))

; leq-vars
(define (leq-vars ineq)
  (remove-duplicates (append (lc-vars (leq-lhs ineq))
                             (lc-vars (leq-rhs ineq)))))

; leq-negate
; ~ (l1 <= l2) ->
; l2 <= 1 + l1
(define (leq-negate ineq)
  (leq (lc-add1 (leq-rhs ineq))
       (leq-lhs ineq)))

(check-equal? (leq-negate (leq (lc (1 'x))
                               (lc (1 'y))))
              (leq (lc (1 'y) (1 #f))
                   (lc (1 'x))))
; leq-normalize
; converts leq with x into either:
;  1) ax <= by + cz + ...
;  or
;  2) by + cz + ... <= ax
;  where a is a positive integer
(define (leq-normalize ineq x)
  (define-values (lhs rhs) (leq-lcs ineq))
  ; ... + ax + .... <= ... + bx + ...
  (define a (lc-scalar lhs x 0))
  (define b (lc-scalar rhs x 0))
  (cond
    [(and a b (= a b))
     (leq (lc-remove-var lhs x)
          (lc-remove-var rhs x))]
    [(and a b (< a b))
     (leq (lc-subtract (lc-remove-var lhs x)
                       (lc-remove-var rhs x))
          (lc ((- b a) x)))]
    [(and a b (> a b))
     (leq (lc ((- a b) x))
          (lc-subtract (lc-remove-var rhs x)
                       (lc-remove-var lhs x)))]
    [else
     ineq]))

; x lhs
(check-equal? (leq-normalize (leq (lc (3 'x) (2 'z) (5 'y))
                                  (lc (1 'x) (1 'z)))
                             'x)
              (leq (lc (2 'x)) (lc (-5 'y) (-1 'z))))

; x rhs
(check-equal? (leq-normalize (leq (lc (3 'x) (2 'z) (5 'y))
                                  (lc (1 'z) (33 'x)))
                             'x)
              (leq (lc (1 'z) (5 'y)) (lc (30 'x))))
; x eq
(check-equal? (leq-normalize (leq (lc (42 'x) (2 'z) (5 'y))
                                  (lc (42 'x) (1 'z)))
                             'x)
              (leq (lc (2 'z) (5 'y))
                   (lc (1 'z))))
; no x
(check-equal? (leq-normalize (leq (lc (2 'z) (5 'y))
                                  (lc (1 'z)))
                             'x)
              (leq (lc (2 'z) (5 'y))
                   (lc (1 'z))))

; x mix
(check-equal? (leq-normalize (leq (lc (2 'x) (4 'y) (1 #f))
                                  (lc (2 'y))) 'x)
              (leq (lc (2 'x))
                   (lc (-1 #f) (-2 'y))))


; simplify-leq-pair
; takes a pair a1x <= l1 and l2 <= a2x
; and returns a2l1 <= a1l2
(define (simplify-leq-pair leq1 leq2 x)
  (define-values (lhs1 rhs1) (leq-lcs leq1))
  (define-values (lhs2 rhs2) (leq-lcs leq2))
  (cond
    ; leq1: a1x <= l1
    ; leq2: l2 <= a2x
    [(and (lc-scalar lhs1 x)
          (lc-scalar rhs2 x))
     (let ([a1 (lc-scalar lhs1 x)]
           [a2 (lc-scalar rhs2 x)])
       (leq (lc-scale lhs2 a1)
            (lc-scale rhs1 a2)))]
    ; leq1: l1 <= a1x
    ; leq2: a2x <= l2
    [(and (lc-scalar rhs1 x)
          (lc-scalar lhs2 x))
     (let ([a1 (lc-scalar rhs1 x)]
           [a2 (lc-scalar lhs2 x)])
       (leq (lc-scale lhs1 a2)
            (lc-scale rhs2 a1)))]
    [else
     (error "bad pair for simplification of ~a: ~a, ~a" x leq1 leq2)]))

(check-equal? (simplify-leq-pair (leq (lc (2 'x))
                                      (lc (4 'y) (10 #f)))
                                 (leq (lc (4 'z) (2 #f))
                                      (lc (4 'x)))
                                 'x)
              (leq (lc (8 'z) (4 #f))
                   (lc (16 'y) (40 #f))))


; trivially-valid?
(define (leq-trivially-valid? ineq)
  (unless (or (empty? (leq-vars ineq))
              (equal? (list #f) (leq-vars ineq)))
    (error 'trivially-valid? "non-trivial inequality: ~a" ineq))
  (define lhs-val (lc-scalar (leq-lhs ineq) #f 0))
  (define rhs-val (lc-scalar (leq-rhs ineq) #f 0))
  (<= lhs-val rhs-val))


;**********************************************************************
; Systems of Linear Inequalities
; a1x1 + a2x2 + ... <= b1y1 + b2y2 + ...
; c1z1 + c2z2 + ... <= d1q1 + d2q2 + ...
; ...
;   (and related operations)
;**********************************************************************

; sli-vars
(define (sli-vars sli)
  (remove-duplicates (apply append (map leq-vars sli))))


; sli-partition
; partitions leq expressions into
; 3 lists of x-normalized inequalities:
;  value 1) list of (ax <= by + cz + ...) leqs
;  value 2) list of form (by + cz + ... <= ax) leqs
;  value 3) leqs w/o x
(define (sli-partition leqs x)
  (define nleqs (map (λ (ineq) (leq-normalize ineq x)) leqs))
  (for/fold ([xslhs empty]
             [xsrhs empty]
             [noxs empty]) ([ineq nleqs])
    (cond
      [(lc-has-var? (leq-lhs ineq) x)
       (values (cons ineq xslhs) xsrhs noxs)]
      [(lc-has-var? (leq-rhs ineq) x)
       (values xslhs (cons ineq xsrhs) noxs)]
      [else
       (values xslhs xsrhs (cons ineq noxs))])))

(check-equal? (let-values ([(lt gt no)
                            (sli-partition  (list (leq (lc (2 'x) (4 'y) (1 #f))
                                                       (lc (2 'y)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc (2 'x)) 
                               (lc (-2 'y) (-1 #f))))
                    empty
                    empty))
(check-equal? (let-values ([(lt gt no)
                            (sli-partition  (list (leq (lc (2 'x) (4 'y) (1 #f))
                                                       (lc (2 'y)))
                                                  (leq (lc (2 'x) (4 'y))
                                                       (lc (2 'y) (42 'x)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc (2 'x)) 
                               (lc (-2 'y) (-1 #f))))
                    (list (leq (lc (2 'y))
                               (lc (40 'x))))
                    empty))
(check-equal? (let-values ([(lt gt no)
                            (sli-partition  (list (leq (lc (2 'x) (4 'y) (-1 #f))
                                                       (lc (2 'y)))
                                                  (leq (lc (2 'x) (4 'y))
                                                       (lc (2 'y) (42 'x)))
                                                  (leq (lc (2 'z) (4 'y))
                                                       (lc (2 'y) (42 'q)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc (2 'x)) 
                               (lc (-2 'y) (1 #f))))
                    (list (leq (lc (2 'y))
                               (lc (40 'x))))
                    (list (leq (lc (2 'z) (4 'y))
                               (lc (2 'y) (42 'q))))))


; cartesian-map
; map of f over each pair of cartesian
; product of input lists
(define (cartesian-map f xs ys)
  (for/fold ([pairs empty]) ([x xs])
    (append pairs
            (for/list ([y ys])
              (f x y)))))



; eliminate-var
; reduces the system of linear inequalties,
; removing x
(define (sli-elim-var sli x)
  (unless (and x (list? sli))
    (error 'sli-elim-var "can't eliminate constant scalars from ineqs"))
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (append (cartesian-map (λ (leq1 leq2) (simplify-leq-pair leq1 leq2 x)) 
                                 xltleqs 
                                 xgtleqs)
          noxleqs))

; sli-satisfiable?
(define (sli-satisfiable? sli)
  (unless (and (list? sli) (not (empty? sli)))
    (error 'sli-satisfiable? "invalid sli: ~a" sli))
  (define vars (remove #f (sli-vars sli)))
  (define simple-system
    (for/fold ([system sli]) ([x vars])
      (sli-elim-var system x)))
  (andmap leq-trivially-valid? simple-system))

; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
(check-true (sli-satisfiable? (list (leq (lc (3 'x) (2 'y))
                                         (lc (7 #f)))
                                    (leq (lc (6 'x) (4 'y))
                                         (lc (15 #f)))
                                    (leq (lc (-1 'x))
                                         (lc (1 #f)))
                                    (leq (lc (0 #f))
                                         (lc (2 'y))))))


; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
(check-false (sli-satisfiable? (list (leq (lc (3 'x) (2 'y))
                                          (lc (4 #f)))
                                     (leq (lc (1 #f))
                                          (lc (1 'x)))
                                     (leq (lc (1 #f))
                                          (lc (1 'y))))))

;**********************************************************************
; Logical Implication for Linear Inequalities
;**********************************************************************

; sli-implies-leq
(define (sli-implies-leq system ineq)
  (not (sli-satisfiable? (cons (leq-negate ineq)
                               system))))

; transitivity! x <= y /\ y <= z --> x <= z
(check-true (sli-implies-leq (list (leq (lc (1 'x))
                                        (lc (1 'y)))
                                   (leq (lc (1 'y))
                                        (lc (1 'z))))
                             (leq (lc (1 'x))
                                  (lc (1 'z)))))


; x  <= x;
(check-true (sli-implies-leq empty
                             (leq (lc (1 'x))
                                  (lc (1 'x)))))

; x  - 1 <= x + 1;
(check-true (sli-implies-leq empty
                             (leq (lc (1 'x) (-1 #f))
                                  (lc (1 'x) (1 #f)))))


; x + y <= z; 1 <= y; 0 <= x --> x + 1 <= z
(check-true (sli-implies-leq (list (leq (lc (1 'x) (1 'y))
                                        (lc (1 'z)))
                                   (leq (lc (1 #f))
                                        (lc (1 'y)))
                                   (leq (lc)
                                        (lc (1 'x))))
                             (leq (lc (1 'x) (1 #f))
                                  (lc (1 'z)))))

;**********************************************************************
; Logical Implication for Systems of Linear Inequalities
;**********************************************************************

; sli-implies-sli
(define (sli-implies-sli assumptions goals)
  (andmap (λ (ineq) (sli-implies-leq assumptions ineq))
          goals))


; 4 <= 3 is false
(check-false (sli-implies-sli empty
                             (list (leq (lc (4 #f))
                                        (lc (3 #f))))))
; P and ~P --> false
(check-true (sli-implies-sli (list (leq (lc) (lc (1 'y)))
                                    (leq-negate (leq (lc) (lc (1 'y)))))
                              (list (leq (lc (4 #f))
                                         (lc (3 #f))))))


; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
(check-true (sli-implies-sli (list (leq (lc (1 'x) (1 'y))
                                        (lc (1 'z)))
                                   (leq (lc)
                                        (lc (1 'y)))
                                   (leq (lc)
                                        (lc (1 'x))))
                             (list (leq (lc (1 'x))
                                        (lc (1 'z)))
                                   (leq (lc (1 'y))
                                        (lc (1 'z))))))

; 7x <= 29 --> x <= 4
(check-true (sli-implies-sli (list (leq (lc (7 'x))
                                        (lc (29 #f))))
                             (list (leq (lc (1 'x))
                                        (lc (4 #f))))))
; 7x <= 28 --> x <= 4
(check-true (sli-implies-sli (list (leq (lc (7 'x))
                                        (lc (28 #f))))
                             (list (leq (lc (1 'x))
                                        (lc (4 #f))))))
; 7x <= 28 does not --> x <= 3
(check-false (sli-implies-sli (list (leq (lc (7 'x))
                                        (lc (28 #f))))
                             (list (leq (lc (1 'x))
                                        (lc (3 #f))))))


; 7x <= 27 --> x <= 3
(check-true (sli-implies-sli (list (leq (lc (7 'x))
                                        (lc (27 #f))))
                             (list (leq (lc (1 'x))
                                        (lc (3 #f))))))
