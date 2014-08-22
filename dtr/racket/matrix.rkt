#lang racket/base

(require rackunit racket/list racket/vector)

(provide (all-defined-out))

; span def
(struct span (base length) #:transparent
  #:guard (λ (b l name)
            (unless (and (or (exact-nonnegative-integer? b))
                         (or (exact-nonnegative-integer? l)
                             (not l)))
              (error "not valid span: " b l))
            (values b l)))

(define (:-> [begin 0] [len #f])
  (span begin len))

(define (:-: l u)
  (span l (add1 (- u l))))

(define (span-shape s)
  (values (span-base s) (span-length)))

(define (empty-span? s)
  (and (number? (span-length s))
       (zero? (span-length s))))

; matrix def
(struct matrix (num-rows num-cols data) #:transparent
  #:guard (λ (rs cs v name)
            (unless (and (exact-nonnegative-integer? rs)
                         (exact-nonnegative-integer? cs)
                         (vector? v)
                         (= (* rs cs) (vector-length v)))
              (error "not valid matrix args: " rs cs v))
            (values rs cs v)))

(define empty-matrix (matrix 0 0 (vector)))

; matrix-shape=
(define (matrix-shape= M1 M2)
  (and (= (matrix-num-rows M1) (matrix-num-rows M2))
       (= (matrix-num-cols M1) (matrix-num-cols M2))))

(define (empty-matrix? M)
  (or (zero? (matrix-num-rows M))
      (zero? (matrix-num-cols M))))

; build-matrix
(define (build-matrix rows cols f)
  (cond
    [(and (exact-nonnegative-integer? rows)
          (exact-nonnegative-integer? cols)
          (= 2 (procedure-arity f)))
     (matrix rows cols (build-vector (* rows cols)
                                  (λ (pos) (f (quotient pos cols)
                                              (remainder pos cols)))))]
    [else
     (error 'build-matrix "invalid parameters: ~a ~a ~a" rows cols f)]))

(check-equal? (build-matrix 0 1 (λ (x y) (error "unreachable")))
              (matrix 0 1 (vector)))

(check-equal? (build-matrix 2 3 (λ (r c) (+ c (* 10 r))))
              (matrix 2 3 (vector 0   1  2
                                  10 11 12)))

; matrix-ref
(define (matrix-ref M row col)
  (unless (and (exact-nonnegative-integer? row)
               (exact-nonnegative-integer? col)
               (< -1 row (matrix-num-rows M))
               (< -1 col (matrix-num-cols M)))
    (error 'matrix-ref "invalid args" M row col))
  (vector-ref (matrix-data M) (+ col (* row (matrix-num-cols M)))))

(check-equal? (matrix-ref (matrix 2 3 
                                  (vector 0   1  2
                                          10 11 12))
                          1 2)
              12)

; row-matrix
(define (row-matrix v)
  (matrix 1 (vector-length v) v))

(check-equal? (row-matrix #[0 1 2])
              (matrix 1 3 #(0 1 2)))

; row-matrix?
(define (row-matrix? M)
  (= 1 (matrix-num-rows M)))

(check-equal? (row-matrix? (matrix 1 3 #(0 1 2))) #t)
(check-equal? (row-matrix? (matrix 2 2 #(0 1 2 4))) #f)

; col-matrix
(define (col-matrix v)
  (matrix (vector-length v) 1 v))

(check-equal? (col-matrix #[0 1 2])
              (matrix 3 1 #[0 1 2]))

; col-matrix?
(define (col-matrix? M)
  (= 1 (matrix-num-cols M)))

(check-equal? (col-matrix? (matrix 3 1 #(0 1 2))) #t)
(check-equal? (col-matrix? (matrix 2 2 #(0 1 2 4))) #f)

; matrix-shape
(define (matrix-shape M)
  (values (matrix-num-rows M) (matrix-num-cols M)))

; identity-matrix
; make-matrix

; ones
(define (ones rows cols)
  (build-matrix rows cols (λ (x y) 1)))

;zeros
(define (zeros rows cols)
  (build-matrix rows cols (λ (x y) 0)))

; list -> matrix
(define (list->matrix rows cols l)
  (matrix rows cols (list->vector l)))

; matrix -> list
(define (matrix->list M)
  (vector->list (matrix-data M)))

; list*->matrix
; turns a list of row-lists 
; into a matrix
(define (list*->matrix lol)
  (cond
    [(null? lol) empty-matrix]
    [(not (let ([cols (length (car lol))])
            (andmap (λ (l) (= (length l) cols)) lol)))
     (error 'list*->matrix "lists not of equal length")]
    [else
     (let ([cols (length (car lol))]
           [rows (length lol)])
       (matrix rows cols (list->vector (flatten lol))))]))

(check-equal? (list*->matrix empty) empty-matrix)
(check-equal? (list*->matrix (list (list 1 2) (list 3 4)))
              (matrix 2 2 #[1 2 3 4]))
(check-exn exn:fail? (λ () (list*->matrix (list (list 1 2) (list 3 4 5)))) "length")

; matrix->list*
(define (matrix->list* M)
  (for/list ([r (matrix-num-rows M)])
    (for/list ([c (matrix-num-cols M)])
      (matrix-ref M r c))))

; matrix+
(define (matrix+ M1 M2)
  (if (matrix-shape= M1 M2)
      (matrix (matrix-num-rows M1)
              (matrix-num-cols M1)
              (vector-map + 
                          (matrix-data M1) 
                          (matrix-data M2)))
      (error 'matrix+ "incompatible shapes")))

(check-equal? (matrix+ (matrix 1 0 (vector))
                       (matrix 1 0 (vector)))
              (matrix 1 0 (vector)))

(check-equal? (matrix+ (matrix 0 0 (vector))
                       (matrix 0 0 (vector)))
              (matrix 0 0 (vector)))

(check-equal? (matrix+ (matrix 2 2 (vector 1 2 3 4))
                       (matrix 2 2 (vector 1 1 1 1)))
              (matrix 2 2 (vector 2 3 4 5)))

; matrix*
(define (matrix* M1 M2)
  (define-values (m n)  (matrix-shape M1))
  (define-values (n2 p) (matrix-shape M2))
  (cond
    [(not (= n n2))
     (error 'matrix* "incompatible matrices for *: [~a, ~a] and [~a, ~a]" 
            m n n2 p)]
    [else
     (let ([data (make-vector (* m p))])
       (for ([r (range m)])
         (for ([c (range p)])
           (vector-set! data
                        (+ c (* r p))
                        (for/sum ([i (range n)])
                          (* (matrix-ref M1 r i)
                             (matrix-ref M2 i c))))))
       (matrix m p data))]))

(check-equal? (matrix* (matrix 1 0 (vector))
                       (matrix 0 0 (vector)))
              (matrix 1 0 (vector)))

(check-equal? (matrix* (matrix 1 0 (vector))
                       (matrix 0 2 (vector)))
              (matrix 1 2 (vector 0 0)))

(check-equal? (matrix* (matrix 2 4 (vector 4 -2 5 6
                                           7  2 0 8))
                       (matrix 4 3 (vector 9 -1 1
                                           3 4 -2
                                           -4 0 5
                                           7 -3 2)))
              (matrix 2 3 (vector 52 -30 45
                                  125 -23 19)))

; matrix-map
(define (matrix-map f M)
  (matrix (matrix-num-rows M)
          (matrix-num-cols M)
          (vector-map f 
                      (matrix-data M))))

(check-equal? (matrix-map add1 (matrix 2 2 (vector 1 2 3 4)))
              (matrix 2 2 (vector 2 3 4 5)))

; matrix-abs
(define (matrix-abs M)
  (matrix-map abs M))

; matrix-rdiv
; pointwise M1 / M2
(define (matrix-rdiv M1 M2)
  (unless (matrix-shape= M1 M2)
    (error 'matrix-rdiv "shapes not equal"))
  (define-values (rows cols) (matrix-shape M1))
  (matrix rows 
          cols 
          (vector-map / (matrix-data M1) (matrix-data M2))))

(check-equal? (matrix-rdiv (matrix 0 1 #[])
                           (matrix 0 1 #[]))
              (matrix 0 1 #[]))
(check-equal? (matrix-rdiv (matrix 1 1 #[4])
                           (matrix 1 1 #[2]))
              (matrix 1 1 #[2]))
(check-equal? (matrix-rdiv (matrix 2 3 #[4 4 4
                                         6 6 6])
                           (matrix 2 3 #[2 2 2
                                         3 3 3]))
              (matrix 2 3 #[2 2 2
                            2 2 2]))

; submatrix
(define (submatrix M rspan cspan)
  (unless (and (matrix? M)
               (span? rspan)
               (span? cspan))
    (error 'submatrix "invalid args"))
  (define-values (m n) (matrix-shape M))
  (define rbase (span-base rspan))
  (define cbase (span-base cspan))
  (define rlen (or (span-length rspan) m))
  (define clen (or (span-length cspan) n))
  (unless (and (<= (+ rbase rlen) m)
                   (<= (+ cbase clen) n))
    (error 'submatrix "invalid ranges for ~a by ~a matrix: (:-> ~a ~a) (:-> ~a ~a)"
           m n rbase rlen cbase clen))
  (build-matrix rlen clen (λ (r c) (matrix-ref M
                                               (+ rbase r)
                                               (+ cbase c)))))

(check-equal? (submatrix (matrix 1 1 #[0]) (:->) (:->))
              (matrix 1 1 #[0]))
(check-equal? (submatrix (matrix 2 2 #[1 2
                                       3 4]) 
                         (:->) 
                         (:-> 1 1))
              (matrix 2 1 #(2 4)))
(check-equal? (submatrix (matrix 2 2 #[1 2
                                       3 4]) 
                         (:-: 0 1) 
                         (:-: 0 1))
              (matrix 2 2 #[1 2
                            3 4]))

(check-equal? (submatrix (matrix 2 2 #[1 2
                                       3 4]) 
                         (:-> 0 1) 
                         (:->))
              (matrix 1 2 #(1 2)))

; matrix-augment
; adds columns
(define (matrix-augment M1 M2)
  (unless (= (matrix-num-rows M1)
             (matrix-num-rows M2))
    (error 'matrix-augment "invalid args ~a ~a" M1 M2))
  (let* ([M1rows (matrix->list* M1)]
        [M2rows (matrix->list* M2)]
        [combined (map append M1rows M2rows)])
  (list*->matrix combined)))

(check-equal? (matrix-augment (matrix 2 1 #[1
                                            2])
                              (matrix 2 1 #[3
                                            4]))
              (matrix 2 2 #[1 3
                            2 4]))


; matrix-stack
; adds rows
(define (matrix-stack M1 M2)
  (list*->matrix (append (matrix->list* M1)
                         (matrix->list* M2))))

(check-equal? (matrix-stack (matrix 1 2 #[1 2])
                            (matrix 1 2 #[3 4]))
              (matrix 2 2 #[1 2
                            3 4]))

; matrix-assign
(define (matrix-set M1 M2 [row0 0] [col0 0])
  (define-values (M1rc M1cc) (matrix-shape M1))
  (define-values (M2rc M2cc) (matrix-shape M2))
  (unless (and (exact-nonnegative-integer? row0)
               (exact-nonnegative-integer? col0)
               (<= (+ row0 M2rc) M1rc)
               (<= (+ col0 M2cc) M1cc))
    (error 'matrix-set "invalid args" M1 M2 row0 col0))
  (build-matrix M1rc
                M1cc
                (λ (r c) 
                  (if (and (< (sub1 row0) r (+ row0 M2rc))
                           (< (sub1 col0) c (+ col0 M2cc)))
                      (matrix-ref M2 (- r row0) (- c col0))
                      (matrix-ref M1 r c)))))

(check-equal? (matrix-set (matrix 1 1 #[0]) (matrix 1 1 #[1]))
              (matrix 1 1 #[1]))

(check-equal? (matrix-set (matrix 2 2 #[1 2
                                        3 4]) 
                          (matrix 1 1 #[42]))
              (matrix 2 2 #[42 2
                            3 4]))

(check-equal? (matrix-set (matrix 2 2 #[1 2
                                        3 4]) 
                          (matrix 2 1 #[42
                                        42])
                          0 1)
              (matrix 2 2 #[1 42
                            3 42]))
(check-exn exn:fail? (λ () (matrix-set (matrix 2 2 #[1 2
                                        3 4]) 
                          (matrix 2 1 #[42
                                        42])
                          1 1)))
