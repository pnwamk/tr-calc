#lang typed/racket

(require typed/rackunit)

(define-type Vec (Vectorof Real))
; matrix = vector of rows
(define-type Matrix (Vectorof (Vectorof Real)))

; matrix dimensions
(: m-dim (-> Matrix (values Index Index)))
(define (m-dim M)
  (values (vector-length M)
          (vector-length (vector-ref M 0))))

; matrix reference
(: m-ref (-> Matrix Integer Integer Real))
(define (m-ref A row col)
  (vector-ref (vector-ref A row) col))

; matrix set!
(: m-set! (-> Matrix Integer Integer Real Void))
(define (m-set! M r c v)
  (vector-set! (vector-ref M r)
               c
               v))

(check-equal? (let ([M : Matrix (vector (vector 1 2))])
                (m-set! M 0 1 42)
                M)
              #[ #[1 42]])

; matrix set! a sub matrix into matrix A
; (placing B starting at row0 col0 in A)
(: m-setm! (->* (Matrix Matrix) (Integer Integer) Void))
(define (m-setm! A B [row0 0] [col0 0])
  (define-values (m n) (m-dim A))
  (define-values (j k) (m-dim B))
  (cond
    [(or (> (+ row0 j) m)
         (> (+ col0 k) n))
     (error 'm-set! "Cannot assign ~a by ~a matrix into ~a by ~a matrix"
            j k m n)]
    [else
     (for ([r (range j)])
       (for ([c (range k)])
         (m-set! A 
                 (+ row0 r) 
                 (+ col0 c) 
                 (m-ref B r c))))]))

(check-equal? (let ([M : Matrix (vector (vector 1 2 3) 
                                        (vector 4 5 6)
                                        (vector 7 8 9))])
                (m-setm! M
                         #[ #[42 42] 
                            #[42 42]])
                M)
              #[ #[42 42 3] 
                 #[42 42 6]
                 #[7   8 9]])

(check-equal? (let ([M : Matrix (vector (vector 1 2 3) 
                                        (vector 4 5 6)
                                        (vector 7 8 9))])
                (m-setm! M
                         #[ #[42 42] 
                            #[42 42]]
                         1 1)
                M)
              #[ #[1  2  3] 
                 #[4 42 42]
                 #[7 42 42]])

; matrix column extract
(: m-col (-> Matrix Integer Matrix))
(define (m-col M c)
  (build-vector (vector-length M)
                (λ ([i : Integer]) : Vec
                  (vector (m-ref M i c)))))

(check-equal? (m-col #[ #[1 2]
                        #[3 4]]
                     0)
              #[ #[1]
                 #[3]])

; matrix addition
(: m+ (-> Matrix Matrix Matrix))
(define (m+ A B)
  (define n : Integer (vector-length A))
  (define m : Integer (vector-length (vector-ref A 0)))
  (if (or (not (= n (vector-length B)))
          (not (= m (vector-length (vector-ref B 0)))))
      (error 'm* 
             "invalid dimensions (~a , ~a) + (~a , ~a)"
             n m
             (vector-length B) (vector-length (vector-ref B 0)))
      (build-vector n 
                    (λ ([i : Integer]) : Vec 
                      (build-vector m
                                    (λ ([j : Integer]) : Real
                                      (+ (m-ref A i j)
                                         (m-ref B i j))))))))

(check-equal? (m+ #[ #[1 2]
                     #[1 2]]
                  #[ #[4 5]
                     #[6 7]])
              #[ #[5 7]
                 #[7 9]])

; matrix multiply
; A : n by m matrix
; B : m by p matrix
; returns n by p matrix
(: m* (-> Matrix Matrix Matrix))
(define (m* A B)
  (define n : Integer (vector-length A))
  (define m : Integer (vector-length (vector-ref A 0)))
  (define p : Integer (vector-length (vector-ref B 0)))
  (if (not (= (vector-length B) m))
      (error 'm* 
             "invalid dimensions (~a , ~a) x (~a , ~a)"
             n m
             (vector-length B) p)
      (build-vector n 
                    (λ ([i : Integer]) : Vec 
                      (build-vector p
                                    (λ ([j : Integer]) : Real
                                      (for/sum : Real ([k : Integer (range m)])
                                        (* (m-ref A i k)
                                           (m-ref B k j)))))))))


(check-equal? (m* #[ #[2] ] #[ #[2] ])
              #[ #[4] ])
(check-equal? (m* #[ #[1 2 3] 
                     #[4 5 6]] 
                  #[ #[2 2] 
                     #[2 2]
                     #[2 2]])
              #[ #[12 12]
                 #[30 30]])

; builds a rows by cols matrix of ones
(: ones (-> Integer Integer Matrix))
(define (ones rows cols)
  ;(define ones-row : (Vectorof Real) (make-vector cols 1))
  (build-vector rows (λ ([x : Integer]) : (Vectorof Real)
                       (make-vector cols 1))))

; builds a rows by cols matrix of ones
(: zeros (-> Integer Integer Matrix))
(define (zeros rows cols)
  (build-vector rows (λ ([x : Integer]) : (Vectorof Real)
                       (make-vector cols 0))))

; Append Column
; Appends the column vector to the Matrix,
; creating[A|v]
(: app-col (-> Matrix Vec Matrix))
(define (app-col A v)
  (vector-map
   (λ: ([v : Vec] 
        [val : Real])
     (vector-append v (vector val)))
   A
   v))

(check-equal? (app-col (vector (vector 1)) (vector 2)) 
              (vector (vector 1 2)))
(check-equal? (app-col (vector (vector 1) 
                               (vector 3)) 
                       (vector 2 4)) 
              (vector (vector 1 2)
                      (vector 3 4)))

; Right-Array Division
; perform right-array division by dividing each 
; element of A by the corresponding element of B.
(: m-rdiv! (-> Matrix Matrix Matrix))
(define (m-rdiv! A B)
  (vector-map! (λ: ([rA : Vec]
                    [rB : Vec])
                 (vector-map! (λ: ([a : Real]
                                   [b : Real])
                                (/ a b))
                              rA
                              rB))
               A
               B))

(check-equal? (let ([M : Matrix (vector (vector 4))])
                (m-rdiv! M 
                         #[ #[2]])
                M)
              #[ #[2]])
(check-equal? (let ([M : Matrix (vector (vector 4 8)
                                        (vector 16 32))])
                (m-rdiv! M
                         #[ #[1 2]
                            #[4 8]]))
              #[ #[4 4]
                 #[4 4]])

;; Matrix Absolute Value
(: m-abs (-> Matrix Matrix))
(define (m-abs M)
  (vector-map (λ ([r : Vec]) 
                (vector-map (λ ([x : Real]) (abs x))
                            r))
              M))
(check-equal? (let ([M : Matrix (vector (vector -4 2)
                                        (vector -2 -1)
                                        (vector 3 -5))])
                (m-abs M))
              #[ #[ 4 2] 
                 #[ 2 1]
                 #[ 3 5]])


;; Matrix Absolute Value
(: m-abs! (-> Matrix Matrix))
(define (m-abs! M)
  (vector-map! (λ ([r : Vec]) 
                 (vector-map! (λ ([x : Real]) (abs x))
                              r))
               M))

(check-equal? (let ([M : Matrix (vector (vector -4 2)
                                        (vector -2 -1)
                                        (vector 3 -5))])
                (m-abs! M)
                M)
              #[ #[ 4 2] 
                 #[ 2 1]
                 #[ 3 5]])


; Fourier-Motzkin Elimination
; problem A*x <= b
; with elimination of redundant inequalities
; A : m by n  matrix
; b : vector length m
(: fm (->* (Matrix Vec) (Natural) 
           (values Matrix Vec)))
(define (fm A b [nvar 1])
  (define m : Integer (vector-length A))
  (define n : Integer (vector-length (vector-ref A 0)))
  ; make the matrix [A|b]
  (define Ab : Matrix (app-col A b))
  ; extract rows w/ pos 1st elements
  (define-values (pos-rows nonpos-rows)  
    (partition (λ: ([r : Vec])
                 (positive? (vector-ref r 1)))
               (vector->list Ab)))
  ; separate out rows w/ neg & zero 1st elements
  (define-values (zero-rows neg-rows)  
    (partition (λ: ([r : Vec])
                 (zero? (vector-ref r 1)))
               nonpos-rows))
  (define non-zeros : Matrix (list->vector (append pos-rows neg-rows)))
  ; rdivide entries in non-zeros by matrix built from column 0
  (m-rdiv! non-zeros 
           (m-abs (m* (m-col non-zeros 0) 
                      (ones 1 (add1 n)))))
  (define A2 : Matrix (zeros (+ (* (length pos-rows)
                                   (length neg-rows))
                                (length zero-rows))
                             n))
 #;(for ([i (range (length pos-rows))])
    #|
     assign to A2's row (i-1)*nneg+1:i*nneg
       ones(nneg,1)*temp(i,2:n+1)+temp(npos+1:npos+nneg,2:n+1)
    |#)
  (values (vector) (vector)))


#|
The pos/neg portion of the graph =

  pos/neg portion  ./  (abs (* (1st-col pos/neg) (ones 1 (add1 n))

|#
