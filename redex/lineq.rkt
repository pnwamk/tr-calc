#lang racket

(require redex fme)

(define-language LI
  [x   ::= variable-not-otherwise-mentioned]
  [z   ::= integer]
  [LE  ::= z (obj π x) (z * LE) (LE + LE)]
  [SLI ::= (LE ...)])

(define-judgment-form LI
  #:mode (implies I I)
  #:contract (implies SLI SLI)
  [--------------- "Implies-Nil"
   (implies SLI_1 ())]
  [
   --------------- "Implies-SLI"
   (implies SLI_1 SLI_2)])