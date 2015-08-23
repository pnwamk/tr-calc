#lang racket
(require redex
         "lang.rkt"
         "substitution.rkt"
         "subtyping.rkt")


(define-metafunction DTR
  elim-id : x any -> any)

(define-metafunction DTR
  normal-form : any -> any)