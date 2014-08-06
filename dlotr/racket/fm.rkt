#lang typed/racket

(require typed/rackunit)
(require math/matrix)
(require math/array)

(define-type Nat Natural)
(define-type Int Integer)
(define-type Opt Option)

(define m* matrix*)
(define m+ matrix+)
(define mref matrix-ref)
(define m= matrix=)
(define mshape matrix-shape)
; matrix? and Matrix are unrelated - someone should go punch themselves
(define: (num-rows [M : (Opt (Matrix Real))]) : Nat
  (if (and M (matrix? M))
      (matrix-num-rows M)
      0))
(check-equal? (num-rows (matrix [[1 2 3]
                                 [3 4 5]
                                 [1 2 3]]))
              3)

(define: (num-cols [M : (Opt (Matrix Real))]) : Nat
  (if (and M (matrix? M))
      (matrix-num-cols M)
      0))

(check-equal? (num-cols (matrix [[1 2 3 4]
                                 [3 4 5 2]
                                 [1 2 3 1]]))
              4)

;; Replace a portion of M1 with the contents of M2
;;  starting at (0,0) or a specified point in M1
(: mset (->* ((Matrix Real) (Opt (Matrix Real))) (Integer Integer) (Matrix Real)))
(define (mset M1 M2 [row0 0] [col0 0])
  (define-values (rows1 cols1) (mshape M1))
  (cond
    [(false? M2) M1]
    [(or (> (+ row0 (num-rows M2)) rows1)
         (> (+ col0 (num-cols M2)) cols1))
     (error 'mset "Cannot assign ~a by ~a matrix into ~a by ~a matrix at (~a, ~a)"
            (num-rows M2) (num-cols M2) rows1 cols1 row0 col0)]
    [else
     (build-matrix rows1 cols1 
                   (λ ([row : Integer] 
                       [col : Integer])
                     (if (and (< (sub1 col0) col (+ col0 (num-cols M2)))
                              (< (sub1 row0) row (+ row0 (num-rows M2))))
                         (mref M2 (- row row0) (- col col0))
                         (mref M1 row col))))]))


(check-equal? (m= (mset (matrix [[1 2 3]
                                 [4 5 6]
                                 [7 8 9]])
                        (matrix [[42 42]
                                 [42 42]]))
                  (matrix [[42 42 3]
                           [42 42 6]
                           [7  8  9]]))
              #t)

(check-equal? (m= (mset (matrix [[1 2 3]
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

(check-equal? (m= (mset (matrix [[1 2 3]
                                 [4 5 6]
                                 [7 8 9]])
                        #f)
                  (matrix [[1 2 3]
                           [4 5 6]
                           [7 8 9]]))
              #t)
(check-exn exn:fail? (λ () (mset (matrix [[1]]) (matrix [[1 2]]))) "assign")


;; right division a la ./ or rdiv in Matlab
;; (pointwise division)
(: mdiv (-> (Matrix Real) (Matrix Real) (Matrix Real)))
(define (mdiv M1 M2)
  (define-values (r1 c1) (mshape M1))
  (define-values (r2 c2) (mshape M2))
  (cond
    [(or (not (= r1 r2))
         (not (= c1 c2)))
     (error 'mdiv "matrix shapes (~a,~a) (~a,~a) are not equal" r1 c1 r2 c2)]
    [else
     (build-matrix r1 c1
                   (λ ([r : Int] 
                       [c : Int])
                     (/ (mref M1 r c)
                        (mref M2 r c))))]))

(check-equal? (m= (mdiv (matrix [[2 8]
                                 [2 4]])
                        (matrix [[2 8]
                                 [2 4]]))
                  (matrix [[1 1]
                           [1 1]]))
              #t)
;
;; partitions a list of rows by the sign of their first element
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



;; Build matrix of ones
(: ones (-> Integer Integer (Matrix Real)))
(define (ones r c)
  (build-matrix r c (λ (x y) 1)))
;
;; Build matrix of zeros
(: zeros (-> Integer Integer (Matrix Real)))
(define (zeros r c)
  (build-matrix r c (λ (x y) 0)))

;; Absolute value of matrix
(: mabs (-> (Matrix Real) (Matrix Real)))
(define (mabs M)
  (matrix-map abs M))

(: list*->optmatrix (-> (Listof (Listof Real)) (Opt (Matrix Real))))
(define (list*->optmatrix lolor)
  (cond 
    [(empty? lolor) #f]
    [else (list*->matrix lolor)]))

(: unopt-filter (All (a) (-> (Listof (Option a)) (Listof a))))
(define (unopt-filter loa)
  (cond
    [(empty? loa)
     empty]
    [(first loa)
     (cons (first loa)
           (unopt-filter (rest loa)))]
    [else
     (unopt-filter (rest loa))]))

(: optmatrix-stack (-> (Listof (Opt (Matrix Real))) (Matrix Real)))
(define (optmatrix-stack optms)
  (: id (-> (Opt (Matrix Real)) (Opt (Matrix Real))))
  (define id (λ (x) x))
  (define ms : (Listof (Matrix Real)) (unopt-filter optms))
  (cond
    [(not (empty? ms))
     (matrix-stack ms)]
   [else
    (error 'optmatrix-stack "No matrices in list")]))

;; Fourier-Motzkin Elimination
;; "given a matrix A and vector b, test if Ax <= b 
;;   has a solution, and if so find one" ([1] pg. 155)
;; A : m by n  matrix of coefficients
;; b : vector length m of bounds
(: fm-elim-work (->* ((Matrix Real) Integer Integer (Array Real) Natural)
                     (values (Matrix Real) (Array Real))))
(define (fm-elim-work A m n b nvar)
  ; construct the matrix A' = [A|b]
  (define Ab : (Matrix Real) (matrix-augment (list A (->col-matrix b))))
  ; partition out rows of A' by sign of first column
  (define-values (pos zero neg) (sign-partition-rows (matrix->list* Ab)))
  (define-values (npos nzero nneg) (values (length pos)
                                           (length zero)
                                           (length neg)))
  ; order A' rows: pos, neg
  (define posneg : (Opt (Matrix Real)) (list*->optmatrix (append pos neg)))
  ; divide non-zero first-coefficient inequalities of A' according to first column
  ; (normalizes inequalities relative to first coefficient)
  (define posneg-divided : (Opt (Matrix Real))
    (if posneg
        (let ([denominator (mabs (m* (matrix-col posneg 0) 
                                     (ones 1 (add1 n))))])
          (mdiv posneg denominator))
        #f))
  ; Add on zero coefficient inequalities
  (define temp : (Matrix Real) (optmatrix-stack (list posneg-divided 
                                                      (list*->optmatrix zero))))
  ; loop, eliminating 1st column's variable from system
  (define Ab2 : (Matrix Real)
    (for/fold ([M  (zeros (+ (* npos nneg) nzero) n)]) ([i (range npos)])
      (define result (m+ (m* (ones nneg 1)
                             (submatrix temp 
                                        (list i) 
                                        (:: 1 (add1 n))))
                         (submatrix temp 
                                    (:: npos (+ npos nneg)) 
                                    (:: 1 (add1 n)))))
      (mset M result (* i nneg))))
  ; append inequalities w/ zero as first coefficient 
  (define Ab3 (mset Ab2 
                    (submatrix temp (:: (+ npos nneg) m) (:: 1 (add1 n)))
                    (* npos nneg)))
  ; extract new vector b (col (n-1)
  (define b-new (matrix-col Ab3 (sub1 n)))
  ; extract new A (cols 0 through (n-2)
  (define A-new (submatrix Ab3 (::) (:: 0 (sub1 n))))
  ;recurse
  (fm-elim A-new b-new nvar))

(: fm-elim (->* ((Matrix Real) (Array Real)) (Natural) 
                (values (Matrix Real) (Array Real))))
(define (fm-elim A b [nvar 1])
  (define-values (m n) (mshape A))
  (if (> n nvar)
      (fm-elim-work A m n b nvar)
      (values A b)))


(define (bounds-valid? [coefficients : (Listof Real)] 
                       [bounds : (Listof Real)]) : Boolean
  (let loop ([cs : (Listof Real) coefficients]
             [bs : (Listof Real) bounds]
             [lower : Real -inf.0]
             [upper : Real +inf.0])
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

(define (satisfiable? [A : (Matrix Real)]
                      [b : (Array Real)]) : Boolean
  (define-values (A2 b2) (fm-elim A b))
  (define-values (rows cols) (matrix-shape A2))
  (define coefficients (matrix->list A2))
  (define bounds (array->list b2))
  (cond
    [(or (not (= cols 1))
         (not (= rows (length bounds))))
     (error 'satisfiable? "fm-elim produced erroneous output: ~a ~a" A2 b2)]
    [else 
     (bounds-valid? coefficients bounds)]))

; test 1
; x <= 5
; A = (matrix [[1]])
; b = (array 5)
; satisfiable
(check-equal? (satisfiable? (matrix [[1]]) 
                            (array 5))
              #t)
; test 2
; 3x + 2y <= -7 
; -x + 4y <= 9
; 0x + -y <= 4
; satisfiable
(check-equal? (satisfiable? (matrix [[3   2]
                                     [-1  4]
                                     [0  -1]]) 
                            (array #(-7 9 4)))
              #t)


; test 3
; 3x + 2y + z  <= -7
; -x + 4y - 2z <= 9
; 0x + -y + 0z <= 4
; 0x + 0y + z <= 0
; 0x + 0y + z <= 100
; satisfiable
(check-equal? (satisfiable? (matrix [[3   2   1]
                                     [-1  4  -2]
                                     [0  -1   0]
                                     [0   0   1]
                                     [0   0   1]]) 
                            (array #(-7 9 4 0 100)))
              #t)

; test 4
; x <= 5
; -x <= -6
; unsatisfiable
(check-equal? (satisfiable? (matrix [[1]
                                     [-1]]) 
                            (array #[5 -6]))
              #f)

; test 5
; x + y <= 5
; -2x -2y<= -11
; unsatisfiable
(check-equal? (satisfiable? (matrix [[1 1]
                                     [-2 -2]]) 
                            (array #[5 -11]))
              #f)
; test 6
; x + y + z <= 5
; -2x -2y + z <= -100
; z <= -100
; x - y <= -1000
; x + y + z <= -1000
; -x + -y + -z <= -1000
(check-equal? (satisfiable? (matrix [[1   1   1]
                                     [-2  -2  1]
                                     [0   0   1]
                                     [1  -1   0]
                                     [1   1   1]
                                     [-1  -1   -1]]) 
                            (array #(5 -100 -100 -1000 -1000 -1000)))
              #f)

