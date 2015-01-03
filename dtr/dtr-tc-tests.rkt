#lang racket

(require redex "dtr-redex.rkt" rackunit)

(define-judgment-form λDTR
  #:mode (typeof* I I I I)
  #:contract (typeof* Γ e τ (ψ ψ oo))
  [(where o (fresh-o))
   (typeof Γ e_1 τ_2 (ψ_2+ ψ_2- oo_2))
   (proves (ext Γ (o -: τ_2)) (o -: τ_1))
   (proves (ext Γ ψ_2+) ψ_1+)
   (proves (ext Γ ψ_2-) ψ_1-)
   (subobj oo_2 oo_1)
   -------------- "T-Subsume"
   (typeof* Γ e_1 τ_1 (ψ_1+ ψ_1- oo_1))])

(define-metafunction λDTR
  and : e e -> e
  [(and e_1 e_2) (if e_1 e_2 #f)])

(define-metafunction λDTR
  or : e e -> e
  [(or e_1 e_2) (let (tmp e_1) 
                  (if (ann tmp (U #t #f))
                      (ann tmp (U #t #f))
                      e_2))])

(define-metafunction λDTR
  Option : τ -> τ
  [(Option τ) (U τ #f)])

;; T-Int
(check-true 
 (judgment-holds 
  (typeof* () 
           42 
           Int 
           (TT FF Ø))))

;; T-Str
(check-true 
 (judgment-holds 
  (typeof* () 
           "Hello World"
           Str 
           (TT FF Ø))))

;; T-True
(check-true 
 (judgment-holds 
  (typeof* () 
           #t
           #t 
           (TT FF Ø))))

;; T-False
(check-true 
 (judgment-holds 
  (typeof* () 
           #f
           #f
           (FF TT Ø))))

;; T-Var
(check-true 
 (judgment-holds 
  (typeof* ((is x Int))
           (ann x Int)
           Int
           (TT FF Ø))))


;; T-Abs
(check-true 
 (judgment-holds 
  (typeof* ()
           (λ (x : Int) (ann x Int))
           (x : Int → Int (TT FF (id x)))
           (TT FF Ø))))

;; T-App
(check-true
 (judgment-holds 
  (typeof* ()
           (add1 41)
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* ()
           (add1 41)
           (Int= 42)
           (TT FF 42))))

;; T-If
(check-true
 (judgment-holds 
  (typeof* ((is x (U #t #f)))
           (if (ann x (U #t #f))
               (add1 41)
               42)
           (Int= 42)
           (TT FF 42))))

(check-true
 (judgment-holds 
  (typeof* ((is x (U #t #f)))
           (if (ann x (U #t #f))
               42
               "Hello World")
           (U Int Str)
           (TT FF Ø))))

;; T-Let
(check-true
 (judgment-holds 
  (typeof* ((is x (U #t #f)))
           (let (y (ann x (U #t #f)))
            (if (ann y (U #t #f))
               42
               "Hello World"))
           (U Int Str)
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* ((is x Top))
           (let (y (ann x Top))
             (ann y Top))
           Top
           ((! x #f) (is x #f) (id x)))))

(check-true
 (judgment-holds 
  (typeof* ((is x Top))
           (let (y (int? (ann x Top)))
             (ann y (U #t #f)))
           (U #t #f)
           ((is x Int) (! x Int) Ø))))

;; T-Cons
(check-true
 (judgment-holds 
  (typeof* ()
           (cons 42 "Hello World")
           (Int × Str)
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* ()
           (cons (cons 40 2) (cons "Hello" "World"))
           ((Int × Int) × (Str × Str))
           (TT FF Ø))))

;; T-Car
(check-true
 (judgment-holds 
  (typeof* ()
           (car (cons 42 "Hello World"))
           Int
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* ((is p (Int × Str)))
           (car (ann p (Int × Str)))
           Int
           (TT FF ((CAR) @ p)))))

;; T-Cdr
(check-true
 (judgment-holds 
  (typeof* ()
           (cdr (cons 42 "Hello World"))
           Str
           (TT FF Ø))))

(check-true
 (judgment-holds 
  (typeof* ((is p (Int × Str)))
           (cdr (ann p (Int × Str)))
           Str
           (TT FF ((CDR) @ p)))))

;; T-Vec
(check-true
 (judgment-holds
  (typeof* ()
           (vec 42)
           (♯ Int)
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* ()
           (vec 42 "Hello World")
           (♯ (U Int Str))
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* ()
           (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!")
           (♯ (U Int Str))
           (TT FF Ø))))

;; T-VecRef
(check-true
 (judgment-holds
  (typeof* ()
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") 0)
           (U Int Str)
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* ()
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((* 2) 2))
           (U Int Str)
           (TT FF Ø))))

(check-false
 (judgment-holds
  (typeof* ()
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((+ 0) -1))
           (U Int Str)
           (TT FF Ø))))

(check-true
 (judgment-holds
  (typeof* ()
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") 7)
           (U Int Str)
           (TT FF Ø))))

(check-false
 (judgment-holds
  (typeof* ()
           (vec-ref (vec 42 "All" "Your" "Base" "Are" "Belong" "To" "Us!") ((* 2) 4))
           (U Int Str)
           (TT FF Ø))))

;;; Example 1
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)] 
;           (if (int? (ann x Top))
;               (add1 (ann x Int))
;               0) 
;           Int 
;           TT TT
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* []
;           (λ ([x : Int])
;             (add1 (ann x Int)))
;           (λ x Int Int TT FF Null)
;           TT TT
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: (U Str Int))] 
;           (if (int? (ann x Top))
;               (add1 (ann x Int))
;               (str-len (ann x Str)))
;           Int
;           TT TT
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (int? (ann x Top))
;           (U T F)
;           ((var x) -: Int) ((var x) -! Int)
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* []
;           (λ ([x : Top])
;             (int? (ann x Top)))
;           (λ x Top (U T F) ((var x) -: Int) ((var x) -! Int) Null)
;           TT TT
;           Null)))
;
;
;;; Example 2
;(check-true 
; (judgment-holds 
;  (typeof* []
;           (λ ([x : (U Str Int)])
;             (if (int? (ann x Top))
;                 (add1 (ann x Int))
;                 (str-len (ann x Str))))
;           (λ x (U Str Int) Int TT FF Null)
;           TT FF
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (if (int? (ann x Top))
;               #t
;               (str? (ann x Top)))
;           (U T F)
;           ((var x) -: (U Int Str)) ((var x) -! (U Int Str))
;           Null)))
;
;;; Example 3
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: (Option Str))]
;           (if (ann x Top)
;               (str-len (ann x Str))
;               (error "string not found!"))
;           Int
;           TT FF
;           Null)))
;
;
;(check-true
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (let ([tmp (int? (ann x Top))]) 
;             (ann tmp (U T F)))
;           (U T F)
;           ((var x) -: Int) ((var x) -! Int)
;           Null)))
;
;(check-true
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (let ([tmp (int? (ann x Top))]) 
;             (if (ann tmp (U T F))
;                 (ann tmp (U T F))
;                 (str? (ann x Top))))
;           (U T F)
;           ((var x) -: (U Int Str)) ((var x) -! (U Int Str))
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (or (int? (ann x Top))
;               (str? (ann x Top)))
;           (U T F)
;           ((var x) -: (U Int Str)) ((var x) -! (U Int Str))
;           Null)))
;
;;; Example 4
;(check-true (judgment-holds 
;             (typeof* [((var f) -: (λ x (U Int Str) Int TT FF Null))
;                       ((var x) -: Top)]
;                      (if (or (int? (ann x Top))
;                              (str? (ann x Top)))
;                          ((ann f (λ x (U Int Str) Int TT FF Null))
;                           (ann x (U Int Str)))
;                          0)
;                      Int
;                      TT FF
;                      Null)))
;
;
;;; Example 5
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top) ((var y) -: Top)]
;           (if (and (int? (ann x Top)) (str? (ann y Top)))
;               ((+ (ann x Int)) (str-len (ann y Str)))
;               0)
;           Int
;           TT FF
;           Null)))
;
;;; Example 6
;(check-false 
; (judgment-holds 
;  (typeof* [((var x) -: Top) ((var y) -: Top)]
;           (if (and (int? (ann x Top)) (str? (ann y Top)))
;               ((+ (ann x Int)) (str-len (ann y Str)))
;               (str-len (ann y Str)))
;           Int
;           TT FF
;           Null)))
;
;;; Example 7
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top) ((var y) -: Top)]
;           (if (if (int? (ann x Top)) (str? (ann y Top)) #f)
;               ((+ (ann x Int)) (str-len (ann y Str)))
;               0)
;           Int
;           TT FF
;           Null)))
;
;;; Example 8
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (let ([tmp (str? (ann x Top))])
;             (if (ann tmp Top)
;                 (ann tmp Top)
;                 (int? (ann x Top))))
;           Top
;           ((var x) -: (U Str Int)) ((var x) -! (U Str Int))
;           Null)))
;
;;; Example 9
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (if (let ([tmp (int? (ann x Top))])
;                 (if (ann tmp Top)
;                     (ann tmp Top)
;                     (str? (ann x Top))))
;               ((λ ([x : (U Str Int)])
;                  (if (int? (ann x Top))
;                      (add1 (ann x Int))
;                      (str-len (ann x Str))))
;                (ann x (U Int Str)))
;               0)
;           Int
;           TT FF
;           Null)))
;
;
;;; Example 10
;(check-true 
; (judgment-holds 
;  (typeof* [((var p) -: (Top * Top))]
;           (if (int? (car (ann p (Top * Top))))
;               (add1 (car (ann p (Int * Top))))
;               7)
;           Int
;           TT FF
;           Null)))
;
;;; Example 11
;(check-true 
; (judgment-holds 
;  (typeof* [((var p) -: (Top * Top))
;            ((var g) -: (λ x (Int * Int) Int TT FF Null))]
;           (if (and (int? (car (ann p (Top * Top))))
;                    (int? (cdr (ann p (Top * Top)))))
;               ((ann g (λ x (Int * Int) Int TT FF Null))
;                (ann p (Int * Int)))
;               42)
;           Int
;           TT FF
;           Null)))
;
;;; Example 12
;(check-true 
; (judgment-holds 
;  (typeof* []
;           (λ ([p : (Top * Top)])
;             (int? (car (ann p (Top * Top)))))
;           (λ x 
;             (Top * Top) 
;             (U T F)
;             ((obj (CAR) x) -: Int)
;             ((obj (CAR) x) -! Int)
;             Null)
;           TT
;           FF
;           Null)))
;
;(check-true 
; (judgment-holds 
;  (typeof* []
;           (λ ([p : (Top * Top)])
;             (int? (cdr (ann p (Top * Top)))))
;           (λ x 
;             (Top * Top) 
;             (U T F)
;             ((obj (CDR) x) -: Int)
;             ((obj (CDR) x) -! Int)
;             Null)
;           TT
;           FF
;           Null)))
;
;;; Example 13
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top) ((var y) -: (U Int Str))]
;           (if (and (int? (ann x Top)) (str? (ann y Top)))
;               ((+ (ann x Int)) (str-len (ann y Str)))
;               (if (int? (ann x Top))
;                   ((+ (ann x Int)) (ann y Int))
;                   0))
;           Int
;           TT FF
;           Null)))
;
;;; Example 14
;(check-true 
; (judgment-holds 
;  (typeof* [((var x) -: Top)]
;           (λ ([y : (U Int Str)])
;             (if (and (int? (ann x Top)) (str? (ann y Top)))
;                 ((+ (ann x Int)) (str-len (ann y Str)))
;                 (if (int? (ann x Top))
;                     ((+ (ann x Int)) (ann y Int))
;                     0)))
;           (λ x (U Str Int) Int TT FF Null)
;           TT FF
;           Null)))

