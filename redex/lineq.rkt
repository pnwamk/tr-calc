#lang racket

(require redex fme)

(define-language LI
  [x   ::= variable-not-otherwise-mentioned]
  [z   ::= integer]
  [LE  ::= z (z x) (+ LE LE)])