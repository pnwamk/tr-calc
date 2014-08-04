#lang typed/racket

(require typed/rackunit)
(require math/matrix)
(require math/array)


; Replace a portion of M1 with the contents of M2
;  starting at (0,0) or a specified point in M1
(: matrix-set (->* ((Matrix Real) (Matrix Real)) (Integer Integer) (Matrix Real)))
(define (matrix-set M1 M2 [row0 0] [col0 0])
  (define-values (rows1 cols1) (matrix-shape M1))
  (define-values (rows2 cols2) (matrix-shape M2))
  (cond
    [(or (> (+ row0 rows2) rows1)
         (> (+ col0 cols2) cols1))
     (error 'matrix-set "Cannot assign ~a by ~a matrix into ~a by ~a matrix at (~a, ~a)"
            rows2 cols2 rows1 cols1 row0 col0)]
    [else
     (build-matrix rows1 cols1 
                   (λ ([row : Integer] 
                       [col : Integer])
                     (if (and (< (sub1 col0) col (+ col0 cols2))
                              (< (sub1 row0) row (+ row0 rows2)))
                         (matrix-ref M2 (- row row0) (- col col0))
                         (matrix-ref M1 row col))))]))


(check-equal? (matrix= (matrix-set (matrix [[1 2 3]
                                            [4 5 6]
                                            [7 8 9]])
                                   (matrix [[42 42]
                                            [42 42]]))
                       (matrix [[42 42 3]
                                [42 42 6]
                                [7  8  9]]))
              #t)

(check-equal? (matrix= (matrix-set (matrix [[1 2 3]
                                            [4 5 6]
                                            [7 8 9]])
                                   (matrix [[42 42]
                                            [42 42]])
                                   1
                                   1)
                       (matrix [[1  2  3]
                                [4 42 42]
                                [7 42 42]]))
              #t)

; right division a la ./ or rdiv in Matlab
; (pointwise division)
(: matrix-rdiv (-> (Matrix Real) (Matrix Real) (Matrix Real)))
(define (matrix-rdiv M1 M2)
  (define-values (r1 c1) (matrix-shape M1))
  (define-values (r2 c2) (matrix-shape M2))
  (cond
    [(or (not (= r1 r2))
         (not (= c1 c2)))
     (error 'matrix./ "matrix shapes (~a,~a) (~a,~a) are not equal" r1 c1 r2 c2)]
    [else
     (build-matrix r1 c1
                   (λ ([r : Integer] 
                       [c : Integer])
                     (/ (matrix-ref M1 r c)
                        (matrix-ref M2 r c))))]))

(check-equal? (matrix=
               (matrix-rdiv (matrix [[4 8]
                                     [16 32]])
                            (matrix [[2 8]
                                     [2 4]]))
               (matrix [[2 1]
                        [8 8]]))
              #t)

; partitions a list of rows by the sign of their first element
(: sign-partition-rows (-> (Listof (Listof Real))
                           (Values (Listof (Listof Real))
                                   (Listof (Listof Real))
                                   (Listof (Listof Real)))))
(define (sign-partition-rows list-of-rows)
  (define: (part-rows [lor : (Listof (Listof Real))]
                     [pos : (Listof (Listof Real))]
                     [zero : (Listof (Listof Real))]
                     [neg : (Listof (Listof Real))]) 
    : (Values (Listof (Listof Real))
              (Listof (Listof Real))
              (Listof (Listof Real)))
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

; Build matrix of ones
(: ones (-> Integer Integer (Matrix Real)))
(define (ones r c)
  (build-matrix r c (λ (x y) 1)))

; Build matrix of zeros
(: zeros (-> Integer Integer (Matrix Real)))
(define (zeros r c)
  (build-matrix r c (λ (x y) 0)))

; Absolute value of matrix
(: matrix-abs (-> (Matrix Real) (Matrix Real)))
(define (matrix-abs M)
  (matrix-map abs M))


; Fourier-Motzkin Elimination
; problem A*x <= b
; with elimination of redundant inequalities
; A : m by n  matrix
; b : vector length m
(: fm-elim-work (->* ((Matrix Real) Integer Integer (Array Real) Natural)
           (values (Matrix Real) (Array Real))))
(define (fm-elim-work A m n b nvar)
  ; construct the matrix [A|b]
  (define Ab : (Matrix Real) (matrix-augment (list A (->col-matrix b))))
  ; partition out rows by sign of first element
  (define-values (pos zero neg) (sign-partition-rows (matrix->list* Ab)))
  (define-values (npos nzero nneg) (values (length pos)
                                           (length zero)
                                           (length neg)))
  ; order [pos;neg;zero] and divide according to first column
  (define posneg : (Matrix Real) (list*->matrix (append pos neg)))
  ;(define Ab-ordered : (Matrix Real) (list*->matrix (append pos neg zero)))
  (define posneg-divided : (Matrix Real)
    (let ([denominator (matrix-abs (matrix* (matrix-col posneg 0) 
                                            (ones 1 (add1 n))))])
    (matrix-rdiv posneg denominator)))
  (define temp (matrix-stack (list posneg-divided (list*->matrix zero))))
  (define Ab2 : (Matrix Real)
    (for/fold ([M : (Matrix Real) (zeros (+ (* npos nneg) nzero) n)])
      ([i (range npos)])
      (define result (matrix+ (matrix* (ones nneg 1)
                                       (submatrix temp 
                                                  (list i) 
                                                  (:: 1 (add1 n))))
                              (submatrix temp 
                                         (:: npos (+ npos nneg)) 
                                         (:: 1 (add1 n)))))
      (matrix-set M result (* i nneg))))
  (define Ab3 (matrix-set Ab2 
                          (submatrix temp (:: (+ npos nneg) m) (:: 1 (add1 n)))
                          (* npos nneg)))
  ; extract new vector b
  (define b-new (matrix-col Ab3 (sub1 n)))
  ; extract new A
  (define A-new (submatrix Ab3 (::) (:: 0 (sub1 n))))
  ;recurse
  (fm-elim A-new b-new nvar))

(: fm-elim (->* ((Matrix Real) (Array Real)) (Natural) 
           (values (Matrix Real) (Array Real))))
(define (fm-elim A b [nvar 1])
  (define-values (m n) (matrix-shape A))
  (if (> n nvar)
      (fm-elim-work A m n b nvar)
      (values A b)))


