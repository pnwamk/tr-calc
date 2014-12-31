#lang racket

(require redex "dtr.rkt" rackunit)

;; substs tests
(check-equal? (term (subst (var x) Ø x)) (term Ø))
(check-equal? (term (subst ((var x) -: Int) (var x) x)) 
              (term ((var x) -: Int)))
(check-equal? (term (subst ((var x) -: Int) (var y) x)) 
              (term ((var y) -: Int)))
(check-equal? (term (subst ((var x) -: Int) Ø y)) 
              (term ((var x) -: Int)))
(check-equal? (term (subst ((var x) -: Int) Ø x)) 
              (term TT))
(check-equal? (term (subst ((+ 42 (* 13 (var x))) -: Int) Ø x)) 
              (term TT))
(check-equal? (term (subst ((+ 42 (* 13 (var x))) -: Int) (+ (var z) (var q)) x)) 
              (term ((+ 42 (* 13 (+ (var z) (var q)))) -: Int)))

;; fme tests
(check-true (judgment-holds (fme-sat [])))
(check-true (judgment-holds (fme-sat [((var x) ≤ (var y))])))
(check-true (judgment-holds (fme-sat [((var x) ≤ (var y))
                                      ((+ 1 (var y)) ≤ (var z))])))
(check-false (judgment-holds (fme-sat [((var x) ≤ (var y))
                                       ((+ 1 (var y)) ≤ (var z))
                                       ((var z) ≤ (var x))])))
(check-true (judgment-holds (fme-imp (((var x) ≤ 3)) 
                                     (((var x) ≤ 5)))))
(check-equal? (term (subst (((var x) ≤ (var z))
                            ((var z) ≤ (o-car (var z)))
                            ((o-car (var z)) ≤ (var y)))
                           Ø
                           z))
              (term (((* 1 (() @ x)) ≤ (* 1 (() @ y))))))


;; subtype tests
(check-true (judgment-holds (subtype Int Int)))
(check-true (judgment-holds (subtype Int Top)))
(check-true (judgment-holds (subtype (U) Int)))
(check-true (judgment-holds (subtype Int (U Int #f))))
(check-true (judgment-holds (subtype (U #t #f) (U Int #t #f))))
(check-true (judgment-holds (subtype Int Int)))
(check-false (judgment-holds (subtype (U Int #t) Int)))
(check-true (judgment-holds (subtype (U Int Int) Int)))
(check-true (judgment-holds (subtype (U Int Int) (U Int #t))))
(check-true (judgment-holds 
             (subtype (x : Top → (U #t #f) (((var x) -: Int) ((var x) -! Int) Ø)) 
                      (x : Top → (U #t #f) (((var x) -: Int) ((var x) -! Int) Ø)))))
(check-true (judgment-holds 
             (subtype (x : Top → (U #t #f) (((var x) -: Int) ((var x) -! Int) Ø)) 
                      (y : Top → (U #t #f) (((var y) -: Int) ((var y) -! Int) Ø)))))
(check-true (judgment-holds 
             (subtype (x : Top → Int (TT TT Ø))
                      (y : Int → (U Int #t #f) (TT TT Ø)))))

;; subtype tests w/ refinements
(check-true (judgment-holds (subtype (x : Int where [((var x) ≤ 5)]) Int)))
(check-true (judgment-holds (subtype (y : Int where [((var y) ≤ 3)]) 
                                     (x : Int where [((var x) ≤ 5)]))))
(check-false (judgment-holds (subtype (y : Int where [((var y) ≤ 13)]) 
                                      (x : Int where [((var x) ≤ 5)]))))


;; update* fact tests
(check-equal? (term (update* [((var x) -: Int)]
                             ((var x) -: Str))) 
              (term (((var x) -: (U)))))
(check-equal? (term (update* [((var x) -: Str)]
                             ((var x) -! Str)))
              (term (((var x) -: (U)))))
(check-equal? (term (update* [((var x) -: (U Int Str))]
                             ((var x) -! Str))) 
              (term (((var x) -: Int))))
(check-equal? (term (update* [((var x) -: (U Int Str))]
                             ((var x) -: (U #t Str)))) 
              (term (((var x) -: Str))))
(check-equal? (term (update* [((var x) -: (Top × Top))]
                             (((CAR) @ x) -: Int))) 
              (term (((var x) -: (Int × Top)))))
(check-equal? (term (update* [((var x) -: (Top × Top))]
                             (((CDR) @ x) -: Int))) 
              (term (((var x) -: (Top × Int)))))
(check-equal? (term (update* [((var x) -: (Int × Top))]
                             (((CAR) @ x) -: Str))) 
              (term (((var x) -: (U)))))
(check-equal? (term (update* [((var x) -: Int)]
                             (((CAR) @ x) -: Str))) 
              (term (((var x) -: (U)))))
(check-equal? (term (update* [((var x) -: (♯ (U Int Str)))]
                             ((var x) -: (♯ Str))))
              (term (((var x) -: (♯ Str)))))
(check-equal? (term (update* [((var x) -: (♯ (U Int Str)))]
                             ((var x) -! (♯ Str))))
              (term (((var x) -: (♯ Int)))))
(check-equal? (term (update* [((var x) -: (z : (U Int Str) where [((var z) ≤ (var z))]))]
                             ((var x) -: Int)))
              (term (((var x) -: (z : Int where [((var z) ≤ (var z))])))))
(check-equal? (term (update* [((var x) -: (z : (U Int Str) where [((var z) ≤ (var z))]))]
                             ((var x) -! Str)))
              (term (((var x) -: (z : Int where (((var z) ≤ (var z))))))))
(check-equal? (term (update* [((var x) -: (z : (U Int Str) where [((var z) ≤ (var z))]))]
                             ((var x) -: (q : Int where [((var q) ≤ (+ 1 (var q)))]))))
              (term (((var x) -: (z : Int where [((var z) ≤ (var z))
                                                 ((var z) ≤ (+ 1 (var z)))])))))
(check-equal? (term (update* [((var x) -: (z : (U Int Str) where [((+ 1 (var z)) ≤ (var x))]))]
                              ((var x) -: (q : Int where [((+ 1 (var x)) ≤ (var q))]))))
              (term (((var x) -: (U)))))

;; update* other tests
(check-equal? (term (update* [((var x) -: Int)
                              ((var x) -: Int)]
                             ((var x) -: Str))) 
              (term (((var x) -: (U)) 
                     ((var x) -: (U)))))
(check-equal? (term (update* [(TT ∧ ((var x) -: Int))]
                             ((var x) -: Str))) 
              (term (((var x) -: (U)))))
(check-equal? (term (update* [(((var x) -: Int) ∨ FF)]
                             ((var x) -: Str)))
              (term (((var x) -: (U)))))

;;logic tests
(check-false (judgment-holds (proves [] FF)))
(check-true (judgment-holds (proves [((var x) -: Int)]
                                    ((var x) -: Int))))
(check-true (judgment-holds (proves [((var x) -: Int)]
                                    ((var x) -! Str))))
(check-true (judgment-holds (proves [(((var x) -: Int) 
                                      ∧ ((var y) -: #f))] 
                                    (((var y) -: #f) 
                                     ∧ ((var x) -: Int)))))
(check-true (judgment-holds (proves [((var x) -: Int)] 
                                    (((var x) -: Int) 
                                     ∨ ((var x) -: (U #t #f))))))
(check-true (judgment-holds (proves [((var x) -: Int)
                                     ((var x) -! Int)] 
                                    FF)))
(check-true (judgment-holds (proves [((var x) -: Int) 
                                     ((var x) -: Str)] 
                                    FF)))
(check-true (judgment-holds (proves [((var x) -: (U #t #f Int)) 
                                     (((var x) -! #t) 
                                      ∧ ((var x) -: (U #t Int)))]
                                    ((var x) -: Int))))
(check-true (judgment-holds (proves [((((var z) -: (U)) ∨ FF)
                                      ∨ ((var x) -: Int))
                                     (((var x) -! Int) 
                                      ∨ ((var y) -: (U #t #f)))
                                     (((var y) -: Int) 
                                      ∨ ((var z) -: (U #t #f)))] 
                                    ((var z) -: (U #t #f)))))

