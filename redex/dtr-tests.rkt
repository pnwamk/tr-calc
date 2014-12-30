#lang racket

(require redex "dtr.rkt" rackunit)

;; substs tests
(check-equal? (term (subst (var x) Ø x)) (term Ø))
(check-equal? (term (subst (fact (var x) #t Int) (var x) x)) (term (fact (var x) #t Int)))
(check-equal? (term (subst (fact (var x) #t Int) (var y) x)) (term (fact (var y) #t Int)))
(check-equal? (term (subst (fact (var x) #t Int) Ø y)) (term (fact (var x) #t Int)))
(check-equal? (term (subst (fact (var x) #t Int) Ø x)) (term TT))
(check-equal? (term (subst (fact (+ 42 (* 13 (var x))) #t Int) Ø x)) (term TT))
(check-equal? (term (subst (fact (+ 42 (* 13 (var x))) #t Int) (+ (var z) (var q)) x)) 
              (term (fact (+ 42 (* 13 (+ (var z) (var q)))) #t Int)))

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
(check-equal? (term (subst (((obj () x) ≤ (obj () z))
                            ((obj () z) ≤ (obj (CAR) z))
                            ((obj (CAR) z) ≤ (obj () y)))
                           Ø
                           z))
              (term [((* 1 (obj () x)) ≤ (* 1 (obj () y)))]))


;; subtype tests
(check-true (judgment-holds (subtype Int Int)))
(check-true (judgment-holds (subtype Int Top)))
(check-true (judgment-holds (subtype (U) Int)))
(check-true (judgment-holds (subtype Int (U Int F))))
(check-true (judgment-holds (subtype (U T F) (U Int T F))))
(check-true (judgment-holds (subtype Int Int)))
(check-false (judgment-holds (subtype (U Int T) Int)))
(check-true (judgment-holds (subtype (U Int Int) Int)))
(check-true (judgment-holds (subtype (U Int Int) (U Int T))))
(check-true (judgment-holds 
             (subtype (Abs x Top (U T F) (fact (var x) #t Int) (fact (var x) #f Int) Ø) 
                      (Abs x Top (U T F) (fact (var x) #t Int) (fact (var x) #f Int) Ø))))
(check-true (judgment-holds 
             (subtype (Abs x Top (U T F) (fact (var x) #t Int) (fact (var x) #f Int) Ø) 
                      (Abs y Top (U T F) (fact (var y) #t Int) (fact (var y) #f Int) Ø))))
(check-true (judgment-holds 
             (subtype (Abs x Top Int TT TT Ø)
                      (Abs y Int (U Int T F) TT TT Ø))))

;; subtype tests w/ refinements
(check-true (judgment-holds (subtype (Refine x : Int [((var x) ≤ 5)]) Int)))
(check-true (judgment-holds (subtype (Refine y : Int [((var y) ≤ 3)]) 
                                     (Refine x : Int [((var x) ≤ 5)]))))
(check-false (judgment-holds (subtype (Refine y : Int [((var y) ≤ 13)]) 
                                      (Refine x : Int [((var x) ≤ 5)]))))


;; update* fact tests
(check-equal? (term (update* [(fact (var x) #t Int)]
                             (fact (var x) #t Str))) 
              (term ((fact (var x) #t (U)))))
(check-equal? (term (update* [(fact (var x) #t Str)]
                             (fact (var x) #f Str)))
              (term ((fact (var x) #t (U)))))
(check-equal? (term (update* [(fact (var x) #t (U Int Str))]
                             (fact (var x) #f Str))) 
              (term ((fact (var x) #t Int))))
(check-equal? (term (update* [(fact (var x) #t (U Int Str))]
                             (fact (var x) #t (U T Str)))) 
              (term ((fact (var x) #t Str))))
(check-equal? (term (update* [(fact (var x) #t (Pair Top Top))]
                             (fact (obj (CAR) x) #t Int))) 
              (term ((fact (var x) #t (Pair Int Top)))))
(check-equal? (term (update* [(fact (var x) #t (Pair Top Top))]
                             (fact (obj (CDR) x) #t Int))) 
              (term ((fact (var x) #t (Pair Top Int)))))
(check-equal? (term (update* [(fact (var x) #t (Pair Int Top))]
                             (fact (obj (CAR) x) #t Str))) 
              (term ((fact (var x) #t (U)))))
(check-equal? (term (update* [(fact (var x) #t Int)]
                             (fact (obj (CAR) x) #t Str))) 
              (term ((fact (var x) #t (U)))))
(check-equal? (term (update* [(fact (var x) #t (Vec (U Int Str)))]
                             (fact (var x) #t (Vec Str))))
              (term ((fact (var x) #t (Vec Str)))))
(check-equal? (term (update* [(fact (var x) #t (Vec (U Int Str)))]
                             (fact (var x) #f (Vec Str))))
              (term ((fact (var x) #t (Vec Int)))))
(check-equal? (term (update* [(fact (var x) #t (Refine z : (U Int Str) [((var z) ≤ (var z))]))]
                             (fact (var x) #t Int)))
              (term ((fact (var x) #t (Refine z : Int [((var z) ≤ (var z))])))))
(check-equal? (term (update* [(fact (var x) #t (Refine z : (U Int Str) [((var z) ≤ (var z))]))]
                             (fact (var x) #f Str)))
              (term ((fact (var x) #t (Refine z : Int [((var z) ≤ (var z))])))))
(check-equal? (term (update* [(fact (var x) #t (Refine z : (U Int Str) [((var z) ≤ (var z))]))]
                             (fact (var x) #t (Refine q : Int [((var q) ≤ (+ 1 (var q)))]))))
              (term ((fact (var x) #t (Refine z : Int [((var z) ≤ (var z))
                                                       ((var z) ≤ (+ 1 (var z)))])))))
(check-equal? (term (update* [(fact (var x) #t (Refine z : (U Int Str) [((+ 1 (var z)) ≤ (var x))]))]
                             (fact (var x) #t (Refine q : Int [((+ 1 (var x)) ≤ (var q))]))))
              (term ((fact (var x) #t (U)))))

;; update* other tests
(check-equal? (term (update* [(fact (var x) #t Int)
                              (fact (var x) #t Int)]
                             (fact (var x) #t Str))) 
              (term ((fact (var x) #t (U)) (fact (var x) #t (U)))))
(check-equal? (term (update* [(And FF
                                   (fact (var x) #t Int))]
                             (fact (var x) #t Str))) 
              (term ((And FF 
                          (fact (var x) #t (U))))))
(check-equal? (term (update* [(Or (fact (var x) #t Int)
                                  TT)]
                             (fact (var x) #t Str))) 
              (term ((Or (fact (var x) #t (U)) 
                         TT))))

;;logic tests
(check-false (judgment-holds (proves [] FF)))
(check-true (judgment-holds (proves [(fact (var x) #t Int)]
                                    (fact (var x) #t Int))))
(check-true (judgment-holds (proves [(fact (var x) #t Int)]
                                    (fact (var x) #f Str))))
(check-true (judgment-holds (proves [(And (fact (var x) #t Int) 
                                          (fact (var y) #t F))] 
                                    (And (fact (var y) #t F) 
                                         (fact (var x) #t Int)))))
(check-true (judgment-holds (proves [(fact (var x) #t Int)] 
                                    (Or (fact (var x) #t Int)
                                        (fact (var x) #t (U T F))))))
(check-true (judgment-holds (proves [(fact (var x) #t Int)
                                     (fact (var x) #f Int)] 
                                    FF)))
(check-true (judgment-holds (proves [(fact (var x) #t Int) 
                                     (fact (var x) #t Str)] 
                                    FF)))
(check-true (judgment-holds (proves [(fact (var x) #t (U T F Int)) 
                                     (And (fact (var x) #f T) 
                                          (fact (var x) #t (U T Int)))]
                                    (fact (var x) #t Int))))
(check-true (judgment-holds (proves [(Or (Or (fact (var z) #t (U)) 
                                             FF) 
                                         (fact (var x) #t Int))
                                     (Or (fact (var x) #f Int) 
                                         (fact (var y) #t (U T F)))
                                     (Or (fact (var y) #t Int) 
                                         (fact (var z) #t (U T F)))] 
                                    (fact (var z) #t (U T F)))))

