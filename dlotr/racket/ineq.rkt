#lang racket/base

(require racket/list racket/bool)
(require rackunit)

; swap cons cell values car/cdr
(define (cons-swap c)
  (cons (cdr c) (car c)))

(check-equal? (cons-swap '(1 . 2))
              '(2 . 1))

;************************************************
; Linear Combinations  (lc)
;   (and related operations)
;************************************************

; defining linear combinations
; takes list of (scalar . symbol)
; #f is used for a constant
(define (lc: . loexps)
  (unless (andmap (λ (x) (and (exact-integer? (car x))
                              (or (symbol? (cdr x))
                                  (not (cdr x)))))
                  loexps)
    (error 'lc: "arguments must be integer/symbol pairs"))
  (apply hash (flatten (map cons-swap loexps))))

(check-equal? (lc:) (hash))
(check-equal? (lc: '(1 . x) '(42 . y) '(1 . #f))
              (hash 'x 1 'y 42 #f 1))
(check-exn exn:fail? (λ () (lc: '('a . 'b))))

; scalar-accessor
(define (lc-scalar lc var [notinval #f])
  (hash-ref lc var notinval))

(check-equal? (lc-scalar (lc: '(1 . x) '(42 . y) '(1 . #f)) 'y) 42)
(check-equal? (lc-scalar (lc: '(1 . x) '(42 . y) '(1 . #f)) #f) 1)
(check-equal? (lc-scalar (lc: '(1 . x) '(42 . y) '(1 . #f)) 'q) #f)

; lc?
(define (lc? x)
  (hash? x))

(check-true (lc? (lc:)))

; lc-var-list
; (no particular order)
(define (lc-vars lc)
  (hash-keys lc))

(check-not-false (let ([vars (lc-vars (lc: '(42 . x) '(17 . #f)))])
                   (and (= 2 (length vars))
                        (member 'x vars)
                        (member #f vars))))

; lc-scalars
; (no particular order)
(define (lc-scalars lc)
  (hash-values lc))

(check-not-false (let ([scalars (lc-scalars (lc: '(42 . x) '(17 . #f)))])
                   (and (= 2 (length scalars))
                        (member 42 scalars)
                        (member 17 scalars))))

; lc-pairs 
; list of (scalar . symbol)
(define (lc-pairs lc)
  (map cons-swap (hash->list lc)))

(check-not-false (let ([pairs (lc-pairs (lc: '(42 . x) '(17 . #f)))])
                   (and (= 2 (length pairs))
                        (member '(42 . x) pairs)
                        (member '(17 . #f) pairs))))

; lc-scale
(define (lc-scale lc a)
  (for/hash ([x (lc-vars lc)])
    (values x (* a (lc-scalar lc x)))))

(check-not-false (let ([scalars (lc-scalars (lc-scale (lc: '(42 . x) '(17 . #f)) 2))])
                   (and (= 2 (length scalars))
                        (member 84 scalars)
                        (member 34 scalars))))

; lc-remove-var
(define (lc-remove-var lc var)
  (hash-remove lc var))

(check-equal? (lc-remove-var (lc: '(42 . x) '(17 . #f)) 'x)
              (lc: '(17 . #f)))

; lc-set-var-scalar
(define (lc-set-var-scalar lc var scalar)
  (unless (and (hash? lc)
               (exact-integer? scalar)
               (or (symbol? var)
                   (not var)))
    (error 'lc-add-var "invalid args"))
  (hash-set lc var scalar))

(check-equal? (lc-set-var-scalar (lc: '(17 . #f)) 'x 42)
              (lc: '(42 . x) '(17 . #f)))
(check-equal? (lc-set-var-scalar (lc: '(2 . x) '(17 . #f)) 'x 42)
              (lc: '(42 . x) '(17 . #f)))

; lc-size
(define (lc-size lc)
  (hash-count lc))

(check-equal? (lc-size (lc: '(42 . x) '(17 . #f)))
              2)

; lc-empty?
(define (lc-empty? lc)
  (hash-empty? lc))

(check-false (lc-empty? (lc: '(42 . x) '(17 . #f))))
(check-not-false (lc-empty? (lc:)))

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

(check-equal? (lc-subtract (lc: '(2 . x) '(3 . y) '(-1 . #f))
                           (lc: '(2 . x) '(-1 . #f) '(42 . z)))
              (lc: '(3 . y) '(-42 . z)))
(check-equal? (lc-subtract (lc: '(0 . #f))
                           (lc: '(2 . x) '(-1 . #f) '(42 . z)))
              (lc: '(-2 . x) '(-42 . z) '(1 . #f)))

;lc-scalar-gcd
; NOTE! currently this includes
; the constant in the lc, if it exists
;(define (lc-scalar-gcd lc)
;  (apply gcd (lc-scalars lc)))

; lc-has-var
(define (lc-has-var? lc x)
  (hash-has-key? lc x))

(check-false (lc-has-var? (lc: '(42 . x) '(17 . #f)) 'y))
(check-not-false (lc-has-var? (lc: '(42 . x) '(17 . #f)) 'x))

;************************************************
; Linear Inequalities  (leq)
;   (and related operations)
;************************************************

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
          (lc: (cons (- b a) x)))]
    [(and a b (> a b))
     (leq (lc: (cons (- a b) x))
          (lc-subtract (lc-remove-var rhs x)
                       (lc-remove-var lhs x)))]
    [else
     ineq]))

; x lhs
(check-equal? (leq-normalize (leq (lc: '(3 . x) '(2 . z) '(5 . y))
                                  (lc: '(1 . x) '(1 . z)))
                             'x)
              (leq (lc: '(2 . x)) (lc: '(-5 . y) '(-1 . z))))

; x rhs
(check-equal? (leq-normalize (leq (lc: '(3 . x) '(2 . z) '(5 . y))
                                  (lc: '(1 . z) '(33 . x)))
                             'x)
              (leq (lc: '(1 . z) '(5 . y)) (lc: '(30 . x))))
; x eq
(check-equal? (leq-normalize (leq (lc: '(42 . x) '(2 . z) '(5 . y))
                                  (lc: '(42 . x) '(1 . z)))
                             'x)
              (leq (lc: '(2 . z) '(5 . y))
                   (lc: '(1 . z))))
; no x
(check-equal? (leq-normalize (leq (lc: '(2 . z) '(5 . y))
                                  (lc: '(1 . z)))
                             'x)
              (leq (lc: '(2 . z) '(5 . y))
                   (lc: '(1 . z))))

; x mix
(check-equal? (leq-normalize (leq (lc: '(2 . x) '(4 . y) '(1 . #f))
                                  (lc: '(2 . y))) 'x)
              (leq (lc: '(2 . x))
                   (lc: '(-1 . #f) '(-2 . y))))


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

(check-equal? (simplify-leq-pair (leq (lc: '(2 . x))
                                      (lc: '(4 . y) '(10 . #f)))
                                 (leq (lc: '(4 . z) '(2 . #f))
                                      (lc: '(4 . x)))
                                 'x)
              (leq (lc: '(8 . z) '(4 . #f))
                   (lc: '(16 . y) '(40 . #f))))


; trivially-valid?
(define (leq-trivially-valid? ineq)
  (unless (or (empty? (leq-vars ineq))
              (equal? '(#f) (leq-vars ineq)))
    (error 'trivially-valid? "non-trivial inequality: ~a" ineq))
  (define lhs-val (lc-scalar (leq-lhs ineq) #f 0))
  (define rhs-val (lc-scalar (leq-rhs ineq) #f 0))
  (<= lhs-val rhs-val))


;************************************************
; Systems of Linear Inequalities
;   (and related operations)
;************************************************

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
                            (sli-partition  (list (leq (lc: '(2 . x) '(4 . y) '(1 . #f))
                                                       (lc: '(2 . y)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc: '(2 . x)) 
                               (lc: '(-2 . y) '(-1 . #f))))
                    empty
                    empty))
(check-equal? (let-values ([(lt gt no)
                            (sli-partition  (list (leq (lc: '(2 . x) '(4 . y) '(1 . #f))
                                                       (lc: '(2 . y)))
                                                  (leq (lc: '(2 . x) '(4 . y))
                                                       (lc: '(2 . y) '(42 . x)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc: '(2 . x)) 
                               (lc: '(-2 . y) '(-1 . #f))))
                    (list (leq (lc: '(2 . y))
                               (lc: '(40 . x))))
                    empty))
(check-equal? (let-values ([(lt gt no)
                            (sli-partition  (list (leq (lc: '(2 . x) '(4 . y) '(1 . #f))
                                                       (lc: '(2 . y)))
                                                  (leq (lc: '(2 . x) '(4 . y))
                                                       (lc: '(2 . y) '(42 . x)))
                                                  (leq (lc: '(2 . z) '(4 . y))
                                                       (lc: '(2 . y) '(42 . q)))) 
                                            'x)])
                (list lt gt no))
              (list (list (leq (lc: '(2 . x)) 
                               (lc: '(-2 . y) '(-1 . #f))))
                    (list (leq (lc: '(2 . y))
                               (lc: '(40 . x))))
                    (list (leq (lc: '(2 . z) '(4 . y))
                               (lc: '(2 . y) '(42 . q))))))


; cartesian-product
(define (cartesian-product xs ys)
  (for/fold ([pairs empty]) ([x xs])
    (append pairs
            (for/list ([y ys])
              (cons x y)))))



; eliminate-var
; reduces the system of linear inequalties,
; removing x
(define (sli-elim-var sli x)
  (unless x
    (error 'sli-elim-var "can't eliminate constant scalars from ineqs"))
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (define leq-pairs (cartesian-product xltleqs xgtleqs))
  (append (map (λ (ineqp) (simplify-leq-pair (car ineqp)
                                             (cdr ineqp)
                                             x))
               leq-pairs)
          noxleqs))

; sli-satisfiable?
(define (sli-satisfiable? sli)
  (define vars (remove #f (sli-vars sli)))
  (define simple-system
    (for/fold ([system sli]) ([x vars])
      (sli-elim-var system x)))
  (andmap leq-trivially-valid? simple-system))

; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
(check-true (sli-satisfiable? (list (leq (lc: '(3 . x) '(2 . y))
                                         (lc: '(7 . #f)))
                                    (leq (lc: '(6 . x) '(4 . y))
                                         (lc: '(15 . #f)))
                                    (leq (lc: '(-1 . x))
                                         (lc: '(1 . #f)))
                                    (leq (lc: '(0 . #f))
                                         (lc: '(2 . y))))))


; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
(check-false (sli-satisfiable? (list (leq (lc: '(3 . x) '(2 . y))
                                          (lc: '(4 . #f)))
                                     (leq (lc: '(1 . #f))
                                          (lc: '(1 . x)))
                                     (leq (lc: '(1 . #f))
                                          (lc: '(1 . y))))))