#lang racket

(require rackunit "./matrix.rkt")

;; partitions a list of rows by the sign of their first element
(define (sign-partition-rows list-of-rows)
  (define (part-rows lor pos zero neg)
    (cond
      [(empty? lor)
       (values pos zero neg)]
      [(positive? (caar lor))
       (part-rows (rest lor) (cons (first lor) pos) zero neg)]
      [(negative? (caar lor))
       (part-rows (rest lor) pos zero (cons (first lor) neg))]
      [else
       (part-rows (rest lor) pos (cons (first lor) zero) neg)]))
  (part-rows list-of-rows empty empty empty))

;; Fourier-Motzkin Elimination
;; "given a matrix A and vector b, test if Ax <= b 
;;   has a solution, and if so find one" ([1] pg. 155)
;; A : m by n  matrix of coefficients
;; b : vector length m of bounds
(define (fm-elim-work A b nvar)
  (define-values (m n) (matrix-shape A))
  ; construct the matrix A' = [A|b]
  (define Ab (matrix-augment A b))
  ; partition out rows of A' by sign of first column
  (define-values (pos zero neg) (sign-partition-rows (matrix->list* Ab)))
  (define-values (npos nzero nneg) (values (length pos)
                                           (length zero)
                                           (length neg)))
  ; order A' rows: pos, neg
  (define posneg (list*->matrix (append pos neg)))
  ; divide non-zero first-coefficient inequalities of A' according to first column
  ; (normalizes inequalities relative to first coefficient)
  (define posneg-divided
    (if (empty-matrix? posneg)
        posneg
        (matrix-rdiv posneg (matrix-abs 
                         (matrix* (submatrix posneg (:->) (:-: 0 0)) 
                                  (ones 1 (add1 n)))))))
  ; Add on zero coefficient inequalities
  (define temp (matrix-stack posneg-divided 
                             (list*->matrix zero)))
  ; loop, eliminating 1st column's variable from system
  (define Ab2
    (for/fold ([M  (zeros (+ (* npos nneg) nzero) n)]) ([i (range npos)])
      (define result (matrix+ (matrix* (ones nneg 1)
                                       (submatrix temp 
                                                  (:-: i i) 
                                                  (:-: 1 n)))
                              (submatrix temp 
                                         (:-: npos (sub1 (+ npos nneg))) 
                                         (:-: 1 n))))
      (matrix-set M result (* i nneg))))
  ; append inequalities w/ zero as first coefficient 
  (define Ab3 (matrix-set Ab2 
                    (if (empty-matrix? temp)
                        temp
                        (submatrix temp (:-: (+ npos nneg) (sub1 m)) 
                                   (:-: 1 n)))
                    (* npos nneg)))
  ; extract new vector b (col (n-1)
  (define b-new (submatrix Ab3 (:->) (:-: (sub1 n) (sub1 n))))
  ; extract new A (cols 0 through (n-2)
  (define A-new (submatrix Ab3 (:->) (:-: 0 (- n 2))))
  ;recurse
  (fm-elim A-new b-new nvar))


(define (fm-elim A b [nvar 1])
  (define-values (m n) (matrix-shape A))
  (if (> n nvar)
      (fm-elim-work A b nvar)
      (values A b)))


(define (bounds-valid? coefficients bounds)
  (let loop ([cs coefficients]
             [bs bounds]
             [lower -inf.0]
             [upper +inf.0])
    (cond
      [(> lower upper) #f]
      [(and (empty? cs)
            (empty? bs))
       #t]
      [(xor (empty? cs)
            (empty? bs))
       (error 'bounds-valid? "oops! One list ran out early!")]
      [(positive? (first cs))
       (loop (rest cs)
             (rest bs)
             lower
             (min (/ (first bs) (first cs)) upper))]
      [(zero? (first cs))
       (if (negative? (first bs))
           #f
           (loop (rest cs) (rest bs) lower upper))]
      [else ;(negative? (first cs))
       (loop (rest cs)
             (rest bs)
             (max (/ (first bs) (first cs)) lower)
             upper)])))

(define (satisfiable? A b)
  (define-values (A2 b2) (fm-elim A b))
  (define-values (rows cols) (matrix-shape A2))
  (define coefficients (matrix->list A2))
  (define bounds (matrix->list b2))
  (cond
    [(or (not (= cols 1))
         (not (= rows (length bounds))))
     (error 'satisfiable? "fm-elim produced erroneous output: ~a ~a" A2 b2)]
    [else 
     (bounds-valid? coefficients bounds)]))


; x <= 5
; A = (matrix [[1]])
; b = (array 5)
; satisfiable
(check-equal? (satisfiable? (matrix 1 1 #[1]) 
                            (col-matrix #[5]))
              #t)

; 3x + 2y <= -7 
; -x + 4y <= 9
; 0x + -y <= 4
; satisfiable
(check-equal? (satisfiable? (matrix 3 2 #[3   2
                                         -1  4
                                          0  -1]) 
                            (col-matrix #[-7 9 4]))
              #t)


; 3x + 2y + z  <= -7
; -x + 4y - 2z <= 9
; 0x + -y + 0z <= 4
; 0x + 0y + z <= 0
; 0x + 0y + z <= 100
; satisfiable
(check-equal? (satisfiable? (matrix 5 3 #[3   2   1
                                         -1   4  -2
                                          0  -1   0
                                          0   0   1
                                          0   0   1]) 
                            (col-matrix #[-7 9 4 0 100]))
              #t)

; 3x+2y+9z-10a <= 115
; x+y+3z-2a <= 15
; -x+y+-3z-2a <= 2
(check-equal? (satisfiable? (matrix 3 4 #[3   2    9  -10
                                          1   1    3   -2
                                          -1  1   -3   -2]) 
                            (col-matrix #[115 15 2]))
              #t)

; x <= 5
; -x <= -6
; unsatisfiable
(check-equal? (satisfiable? (matrix 2 1 #[1
                                         -1]) 
                            (col-matrix #[5 -6]))
              #f)


; x + y <= 5
; -2x -2y<= -11
; unsatisfiable
(check-equal? (satisfiable? (matrix 2 2 #[1 1
                                         -2 -2]) 
                            (col-matrix #[5 -11]))
              #f)

; x + y + z <= 5
; -2x -2y + z <= -100
; z <= -100
; x - y <= -1000
; x + y + z <= -1000
; -x + -y + -z <= -1000
(check-equal? (satisfiable? (matrix 6 3 #[1   1   1
                                         -2  -2  1
                                          0   0   1
                                          1  -1   0
                                          1   1   1
                                         -1  -1   -1]) 
                            (col-matrix #[5 -100 -100 -1000 -1000 -1000]))
              #f)

